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

Bounded by construction: integers are clamped to ``int_bound`` so a runaway counter cannot produce an
unbounded state space.
"""

from __future__ import annotations

from typing import Any

from ._core import Protocol

__all__ = ["SpecError", "protocol_from_spec", "validate_spec"]

DEFAULT_INT_BOUND = 64


class SpecError(ValueError):
    """The spec is malformed. The message names the offending key."""


def _require(cond: bool, msg: str) -> None:
    if not cond:
        raise SpecError(msg)


def validate_spec(spec: dict) -> None:
    """Raise `SpecError` if the spec is not well formed. Returns None on success."""
    _require(isinstance(spec, dict), "spec must be an object")
    fields = spec.get("fields")
    _require(isinstance(fields, list) and fields, "'fields' must be a non-empty list")
    _require(all(isinstance(f, str) for f in fields), "every field name must be a string")
    _require(len(set(fields)) == len(fields), "field names must be unique")

    init = spec.get("initial")
    _require(isinstance(init, dict), "'initial' must be an object")
    _require(set(init) == set(fields), "'initial' must assign exactly the declared fields")

    trans = spec.get("transitions")
    _require(isinstance(trans, list) and trans, "'transitions' must be a non-empty list")
    for i, t in enumerate(trans):
        _require(isinstance(t, dict), f"transition {i} must be an object")
        _require(isinstance(t.get("label", ""), str), f"transition {i}: 'label' must be a string")
        for key in ("when", "set"):
            v = t.get(key)
            if v is not None:
                _require(isinstance(v, dict), f"transition {i}: '{key}' must be an object")
                unknown = set(v) - set(fields)
                _require(not unknown, f"transition {i}: '{key}' names unknown fields {sorted(unknown)}")
        _require(isinstance(t.get("set"), dict) and t["set"], f"transition {i}: 'set' is required")
        for f, val in t["set"].items():
            if isinstance(val, dict):
                _require(
                    set(val) <= {"incr", "decr"} and len(val) == 1,
                    f"transition {i}: field {f!r} update must be a literal, {{'incr': n}} or {{'decr': n}}",
                )
                _require(
                    isinstance(list(val.values())[0], int),
                    f"transition {i}: field {f!r} incr/decr amount must be an integer",
                )

    invs = spec.get("invariants") or {}
    _require(isinstance(invs, dict), "'invariants' must be an object")
    for name, cond in invs.items():
        _check_cond(cond, fields, f"invariant {name!r}")
    if spec.get("goal") is not None:
        _check_cond(spec["goal"], fields, "goal")


def _check_cond(cond: Any, fields: list, where: str) -> None:
    _require(isinstance(cond, dict), f"{where}: must be an object")
    _require(
        set(cond) <= {"forbid", "require"} and len(cond) == 1,
        f"{where}: must have exactly one of 'forbid' or 'require'",
    )
    body = list(cond.values())[0]
    _require(isinstance(body, dict) and body, f"{where}: condition body must be a non-empty object")
    unknown = set(body) - set(fields)
    _require(not unknown, f"{where}: names unknown fields {sorted(unknown)}")


def _pred(cond: dict):
    kind, body = next(iter(cond.items()))
    if kind == "forbid":
        return lambda d: not all(d.get(f) == v for f, v in body.items())
    return lambda d: all(d.get(f) == v for f, v in body.items())


def protocol_from_spec(spec: dict, int_bound: int = DEFAULT_INT_BOUND) -> Protocol:
    """Build a `Protocol` from a declarative spec. Raises `SpecError` if malformed."""
    validate_spec(spec)
    fields: list = list(spec["fields"])
    idx = {f: i for i, f in enumerate(fields)}
    initial = tuple(spec["initial"][f] for f in fields)
    rules = spec["transitions"]

    def clamp(v):
        if isinstance(v, int) and not isinstance(v, bool):
            return max(-int_bound, min(int_bound, v))
        return v

    def transitions(s):
        d = dict(zip(fields, s))
        out = []
        for i, t in enumerate(rules):
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
                    nxt[idx[f]] = clamp(cur + delta)
                else:
                    nxt[idx[f]] = clamp(val)
            nxt = tuple(nxt)
            if nxt != s or True:  # self-loops are legal and kept
                out.append((t.get("label", f"t{i}"), nxt))
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
