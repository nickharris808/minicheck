"""Build a `Protocol` from a declarative JSON/dict spec — no code execution.

`Protocol` takes Python callables, which is flexible and completely unsuitable for anything you did
not write yourself. This module accepts a restricted, declarative description instead, so a state
machine can arrive over a network, from a config file, or from a language model without handing the
sender arbitrary execution.

Spec shape::

    {
      "name": "mutex",
      "fields": ["a", "b", "lock"],
      "initial": {"a": 0, "b": 0, "lock": 0},
      "transitions": [
        {"label": "a_enter", "when": {"a": 0, "lock": 0}, "set": {"a": 1, "lock": 1}},
        {"label": "a_exit",  "when": {"a": 1},            "set": {"a": 0, "lock": 0}}
      ],
      "invariants": {
        "not_both": {"forbid": {"a": 1, "b": 1}}
      },
      "goal": {"require": {"a": 1}}
    }

``when`` is a conjunction of field == value tests (omit it for an always-enabled transition).
``set`` assigns literals, or ``{"incr": n}`` / ``{"decr": n}`` for integer fields.
An invariant is ``{"forbid": {...}}`` (fails when every listed field matches) or
``{"require": {...}}`` (fails unless every listed field matches). ``goal`` uses the same shape.

Bounded by construction, and the bound is CHECKED rather than silently applied. ``int_bound`` limits
the magnitude an integer field may take. If a run would carry a field past it, the build raises
`IntBoundExceeded` instead of saturating the value.

This matters more than it looks. An earlier version *clamped* to the bound, which made a counter that
genuinely reaches 100 stop at 64 — so a "never reach 100" invariant was reported as HOLDING when it
does not. A truncated search that reports success is a false proof, and a false proof from a verifier
is worse than no verifier. The rule here is: when the analysis cannot cover the state space, say so
and refuse; never return a confident verdict the search did not earn.
"""

from __future__ import annotations

from typing import Any

from ._core import Protocol, SearchIncomplete

__all__ = [
    "SpecError",
    "IntBoundExceeded",
    "protocol_from_spec",
    "validate_spec",
    "spec_warnings",
    "DEFAULT_INT_BOUND",
]

DEFAULT_INT_BOUND = 64


class SpecError(ValueError):
    """The spec is malformed. The message names the offending key."""


class IntBoundExceeded(SpecError, SearchIncomplete):
    """An integer field left the declared ``int_bound``, so the search could not be exhaustive.

    Raised rather than clamping the value, because clamping silently shrinks the state space and
    turns "I did not look there" into "it holds". Raise ``int_bound`` to cover the real range, or
    treat this as an explicit refusal to answer.
    """


def _require(cond: bool, msg: str) -> None:
    if not cond:
        raise SpecError(msg)


def _in_bound(v: Any, int_bound: int) -> bool:
    """True unless `v` is an integer of magnitude greater than the bound."""
    if isinstance(v, bool) or not isinstance(v, int):
        return True
    return -int_bound <= v <= int_bound


def validate_spec(spec: dict, int_bound: int = DEFAULT_INT_BOUND) -> None:
    """Raise `SpecError` if the spec is not well formed. Returns None on success.

    Rejects any integer in ``initial``, ``when`` or ``set`` that lies outside ``int_bound``: those
    describe states the encoding cannot represent, so the model as written is not the model that
    would be checked.

    Conditions (invariants and the goal) are NOT rejected for the same reason — see `spec_warnings`.
    A condition naming an out-of-range value is trivially satisfied rather than wrong, so it is
    reported as uninformative instead of refused.
    """
    _require(isinstance(spec, dict), "spec must be an object")
    _require(isinstance(int_bound, int) and not isinstance(int_bound, bool), "'int_bound' must be an integer")
    _require(int_bound > 0, "'int_bound' must be positive")
    fields = spec.get("fields")
    _require(
        isinstance(fields, list) and fields,
        '\'fields\' must be a non-empty list of state-variable names, e.g. ["a", "b", "lock"]',
    )
    _require(all(isinstance(f, str) for f in fields), "every field name must be a string")
    if len(set(fields)) != len(fields):
        dupes = sorted({f for f in fields if fields.count(f) > 1})
        raise SpecError(
            f"field names must be unique, but {dupes} appear more than once. Two fields with the "
            f"same name would be one variable, so the model would not be the one you described."
        )

    init = spec.get("initial")
    _require(isinstance(init, dict), "'initial' must be an object mapping every field to its starting value")
    if set(init) != set(fields):
        missing = sorted(set(fields) - set(init))
        extra = sorted(set(init) - set(fields))
        parts = []
        if missing:
            parts.append(f"missing {missing}")
        if extra:
            parts.append(f"unknown {extra}")
        raise SpecError(
            f"'initial' must assign exactly the declared fields {sorted(fields)}, but it is "
            f"{' and '.join(parts)}. Give every field a starting value and remove any name that "
            f"is not in 'fields'."
        )
    for f, v in init.items():
        _require(
            _in_bound(v, int_bound),
            f"'initial' field {f!r} is {v}, outside int_bound {int_bound}; raise int_bound to cover it",
        )

    trans = spec.get("transitions")
    _require(
        isinstance(trans, list) and trans,
        "'transitions' must be a non-empty list. Each entry needs a 'set', and optionally a "
        "'when' guard and a 'label', e.g. "
        '{"label": "enter", "when": {"lock": 0}, "set": {"lock": 1}}',
    )
    for i, t in enumerate(trans):
        _require(isinstance(t, dict), f"transition {i} must be an object")
        _require(isinstance(t.get("label", ""), str), f"transition {i}: 'label' must be a string")
        for key in ("when", "set"):
            v = t.get(key)
            if v is not None:
                _require(isinstance(v, dict), f"transition {i}: '{key}' must be an object")
                unknown = set(v) - set(fields)
                _require(not unknown, f"transition {i}: '{key}' names unknown fields {sorted(unknown)}")
        for f, val in (t.get("when") or {}).items():
            _require(
                _in_bound(val, int_bound),
                f"transition {i}: 'when' field {f!r} is {val}, outside int_bound {int_bound}",
            )
        _require(isinstance(t.get("set"), dict) and t["set"], f"transition {i}: 'set' is required")
        for f, val in t["set"].items():
            if isinstance(val, dict):
                _require(
                    set(val) <= {"incr", "decr"} and len(val) == 1,
                    f"transition {i}: field {f!r} update must be a literal, {{'incr': n}} or {{'decr': n}}",
                )
                amount = list(val.values())[0]
                _require(
                    isinstance(amount, int) and not isinstance(amount, bool),
                    f"transition {i}: field {f!r} incr/decr amount must be an integer",
                )
            else:
                _require(
                    _in_bound(val, int_bound),
                    f"transition {i}: 'set' field {f!r} is {val}, outside int_bound {int_bound}; "
                    f"raise int_bound to cover it",
                )

    invs = spec.get("invariants") or {}
    _require(isinstance(invs, dict), "'invariants' must be an object")
    for name, cond in invs.items():
        _check_cond(cond, fields, f"invariant {name!r}", int_bound)
    if spec.get("goal") is not None:
        _check_cond(spec["goal"], fields, "goal", int_bound)


def _check_cond(cond: Any, fields: list, where: str, int_bound: int = DEFAULT_INT_BOUND) -> None:
    _require(isinstance(cond, dict), f"{where}: must be an object")
    _require(
        set(cond) <= {"forbid", "require"} and len(cond) == 1,
        f"{where}: must have exactly one of 'forbid' or 'require'",
    )
    body = list(cond.values())[0]
    _require(isinstance(body, dict) and body, f"{where}: condition body must be a non-empty object")
    unknown = set(body) - set(fields)
    _require(not unknown, f"{where}: names unknown fields {sorted(unknown)}")
    # Deliberately does NOT reject an out-of-bound literal here. Now that integers are never
    # clamped, the reachable space genuinely lies inside the bound, so "never reach 99" with a
    # bound of 64 is a TRUE statement about that space, not a false one — just an uninformative
    # one. `spec_warnings` reports it so the triviality is visible without rejecting a valid spec.
    return


def spec_warnings(spec: dict, int_bound: int = DEFAULT_INT_BOUND) -> list:
    """Conditions that are technically true but carry no information. Never fatal.

    The case that matters: an invariant or goal naming an integer the bounded state space cannot
    represent. Because integers are no longer clamped, the reachable space really does lie inside
    ``int_bound``, so such a condition genuinely holds — it just holds for a reason that has nothing
    to do with the protocol being modelled. Reporting a bare ``holds: true`` there invites a reader
    to conclude something was verified, so the triviality is surfaced instead of buried.
    """
    warnings: list = []
    fields = spec.get("fields") if isinstance(spec, dict) else None
    if not isinstance(fields, list):
        return warnings

    def scan(cond, where):
        if not isinstance(cond, dict) or len(cond) != 1:
            return
        body = list(cond.values())[0]
        if not isinstance(body, dict):
            return
        for f, v in body.items():
            if not _in_bound(v, int_bound):
                warnings.append(
                    f"{where}: field {f!r} is compared against {v}, which is outside int_bound "
                    f"{int_bound}. No reachable state can hold that value, so this condition is "
                    f"trivially satisfied and verifies nothing. Raise int_bound to at least "
                    f"{abs(v)} if you meant this to be checkable."
                )

    for name, cond in (spec.get("invariants") or {}).items():
        scan(cond, f"invariant {name!r}")
    if spec.get("goal") is not None:
        scan(spec["goal"], "goal")
    return warnings


def _pred(cond: dict):
    kind, body = next(iter(cond.items()))
    if kind == "forbid":
        return lambda d: not all(d.get(f) == v for f, v in body.items())
    return lambda d: all(d.get(f) == v for f, v in body.items())


def protocol_from_spec(spec: dict, int_bound: int = DEFAULT_INT_BOUND) -> Protocol:
    """Build a `Protocol` from a declarative spec. Raises `SpecError` if malformed.

    The returned transition function raises `IntBoundExceeded` if a run carries an integer field
    past ``int_bound``. It does NOT clamp: a saturated counter would make unreachable states look
    unreachable-by-proof, which is a false negative dressed as a verdict.
    """
    validate_spec(spec, int_bound=int_bound)
    fields: list = list(spec["fields"])
    idx = {f: i for i, f in enumerate(fields)}
    initial = tuple(spec["initial"][f] for f in fields)
    rules = spec["transitions"]

    def checked(v, field: str, label: str):
        """Return `v`, or refuse if it left the bound. Never silently truncates."""
        if isinstance(v, int) and not isinstance(v, bool) and not (-int_bound <= v <= int_bound):
            raise IntBoundExceeded(
                f"transition {label!r} drives field {field!r} to {v}, outside int_bound {int_bound}. "
                f"The state space is not finite under this bound, so no exhaustive verdict is "
                f"available. Re-run with int_bound >= {abs(v)}."
            )
        return v

    def transitions(s):
        d = dict(zip(fields, s))
        out = []
        for i, t in enumerate(rules):
            label = t.get("label", f"t{i}")
            when = t.get("when") or {}
            if not all(d.get(f) == v for f, v in when.items()):
                continue
            nxt = list(s)
            for f, val in t["set"].items():
                if isinstance(val, dict):
                    cur = d.get(f)
                    if not isinstance(cur, int) or isinstance(cur, bool):
                        continue  # incr/decr on a non-integer is a no-op
                    delta = val.get("incr", 0) - val.get("decr", 0)
                    nxt[idx[f]] = checked(cur + delta, f, label)
                else:
                    nxt[idx[f]] = checked(val, f, label)
            out.append((label, tuple(nxt)))  # self-loops are legal and kept
        return out

    invariants = {name: _pred(cond) for name, cond in (spec.get("invariants") or {}).items()}
    goal = _pred(spec["goal"]) if spec.get("goal") is not None else None

    return Protocol(
        name=spec.get("name", "spec"),
        candidate=bool(spec.get("candidate", False)),
        fields=tuple(fields),
        initial=initial,
        transitions=transitions,
        invariants=invariants,
        goal=goal,
    )
