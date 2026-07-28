"""Export a spec to the industrial model checkers, so this is an on-ramp and not a dead end.

`minicheck` is deliberately small. Explicit-state search in CPython runs out of room somewhere around
10⁵–10⁶ states, and when your model outgrows that the honest answer is "use SPIN or TLC". A tool that
strands you at its own ceiling is a tool worth being wary of adopting, so this exports the model
instead.

``promela``   for SPIN. Partial-order reduction, bitstate hashing, orders of magnitude more capacity.
``tla``       for TLC and the TLA+ toolbox. Also the format the wider formal-methods world reads.

**Only the declarative JSON spec can be exported.** A `Protocol` built from a Python callable cannot
be, and this refuses rather than guessing: the transition function is arbitrary code, and emitting an
approximation of it would hand you a Promela model that checks something *different* from what you
verified here. Silently exporting the wrong machine is worse than not exporting.

The generated models are readable rather than clever. You are going to have to trust them, so they
are written to be checked by eye against the spec they came from.
"""

from __future__ import annotations

from .spec import DEFAULT_INT_BOUND, SpecError, validate_spec

__all__ = ["to_promela", "to_tla", "ExportError"]


class ExportError(SpecError):
    """The model cannot be faithfully expressed in the target language."""


def _ident(name: str) -> str:
    """A safe identifier, since spec field names are arbitrary strings."""
    out = "".join(c if (c.isalnum() or c == "_") else "_" for c in str(name))
    if not out or out[0].isdigit():
        out = "f_" + out
    return out


def _ident_map(fields) -> dict:
    """Field name -> a UNIQUE target identifier.

    Sanitising is many-to-one: ``a-b`` and ``a_b`` both become ``a_b``. Applying `_ident`
    independently to each field would therefore emit two variables with the same name, silently
    merging two independent pieces of state — so the exported model would be a *different machine*
    than the one that was checked. Collisions get a numeric suffix instead.
    """
    mapping, used = {}, set()
    for f in fields:
        base = _ident(f)
        cand, k = base, 2
        while cand in used:
            cand, k = f"{base}_{k}", k + 1
        used.add(cand)
        mapping[f] = cand
    return mapping


def _values_of(spec: dict, field: str) -> list:
    """Every literal a field is compared against or assigned, for range inference."""
    seen = [spec["initial"][field]]
    for t in spec["transitions"]:
        for src in (t.get("when") or {}, t.get("set") or {}):
            if field in src and not isinstance(src[field], dict):
                seen.append(src[field])
    for cond in list((spec.get("invariants") or {}).values()) + (
        [spec["goal"]] if spec.get("goal") is not None else []
    ):
        body = list(cond.values())[0] if isinstance(cond, dict) and len(cond) == 1 else {}
        if isinstance(body, dict) and field in body:
            seen.append(body[field])
    return seen


def _check_exportable(spec: dict) -> None:
    """Refuse anything the target languages cannot hold faithfully."""
    for f in spec["fields"]:
        for v in _values_of(spec, f):
            if isinstance(v, bool) or isinstance(v, int):
                continue
            raise ExportError(
                f"field {f!r} takes the non-integer value {v!r}. Promela and TLA+ are exported here "
                f"with integer state variables only, and mapping strings onto integers silently "
                f"would produce a model whose counterexamples do not match yours. Re-encode the "
                f"field as an integer in the spec if you want to export it."
            )


def _cond_expr(cond: dict, op_and: str, eq: str = "==", idents: dict | None = None) -> str:
    """Render a forbid/require body as a boolean expression in the target syntax.

    **Always parenthesised**, including the single-condition case. That is not cosmetic: callers
    negate the result with a prefix operator, and `!` binds tighter than `==` in Promela and C. An
    earlier version omitted the parentheses when there was only one condition, so a `forbid` on one
    field exported as ``!f0 == 2`` — which parses as ``(!f0) == 2`` and is *always false*. Every
    generated model with a single-field invariant therefore asserted a property that fires
    immediately, and SPIN dutifully reported a violation of something the spec never said.

    Found by a differential sweep against SPIN. The hand-written test models all happened to use
    two-field invariants, where the parentheses were already being added.
    """
    kind, body = next(iter(cond.items()))
    ident = (lambda f: idents[f]) if idents else _ident
    parts = [f"{ident(f)} {eq} {int(v) if isinstance(v, bool) else v}" for f, v in body.items()]
    conj = f" {op_and} ".join(parts) if parts else "TRUE"
    return f"({conj})", kind


def to_promela(spec: dict, *, int_bound: int = DEFAULT_INT_BOUND) -> str:
    """A Promela model for SPIN.

    Run it with::

        spin -a model.pml && gcc -o pan pan.c && ./pan -a

    Invariants become `assert`s inside the process loop, which is the idiom SPIN reports best: a
    violation prints the trail, and `spin -t -p model.pml` replays it step by step.
    """
    validate_spec(spec, int_bound=int_bound)
    _check_exportable(spec)

    fields = list(spec["fields"])
    idents = _ident_map(fields)
    name = _ident(spec.get("name", "spec"))
    lines = [
        f"/* Generated from a minicheck spec: {spec.get('name', 'spec')}",
        " *",
        " * Verify with:",
        " *   spin -a this.pml && gcc -o pan pan.c && ./pan -a",
        " *   spin -t -p this.pml        # replay the counterexample trail",
        " *",
        f" * Integer fields are bounded to +/-{int_bound}, matching the minicheck run.",
        " */",
        "",
    ]
    for f in fields:
        init = spec["initial"][f]
        lines.append(f"int {idents[f]} = {int(init) if isinstance(init, bool) else init};")
    lines.append("")

    invs = spec.get("invariants") or {}
    if invs:
        lines.append("/* Safety invariants. `forbid` fails when every listed field matches. */")
        for inv_name, cond in invs.items():
            expr, kind = _cond_expr(cond, "&&", idents=idents)
            neg = f"!{expr}" if kind == "forbid" else expr
            lines.append(f"#define {_ident(inv_name)} ({neg})")
        lines.append("")

    lines.append(f"active proctype {name}() {{")
    if invs:
        # The initial state must be checked BEFORE any transition fires. Asserting only inside the
        # transition bodies misses a model that is already broken at step zero — minicheck reports
        # that as a zero-step counterexample, and an export that cannot see it would have SPIN
        # calling a broken model fine. Found by a differential sweep against SPIN.
        lines.append("  /* the initial state is a reachable state, so it is checked too */")
        for inv_name in invs:
            lines.append(f"  assert({_ident(inv_name)});")
    lines.append("  do")
    for i, t in enumerate(spec["transitions"]):
        label = t.get("label", f"t{i}")
        guard_parts = [
            f"{idents[f]} == {int(v) if isinstance(v, bool) else v}" for f, v in (t.get("when") or {}).items()
        ]
        guard = " && ".join(guard_parts) if guard_parts else "true"
        lines.append(f"  :: {guard} ->")
        lines.append(f"     atomic {{  /* {label} */")
        for f, val in t["set"].items():
            if isinstance(val, dict):
                delta = val.get("incr", 0) - val.get("decr", 0)
                # The bound is re-imposed here so SPIN explores the same space minicheck did.
                lines.append(
                    f"       if :: ({idents[f]} + ({delta}) <= {int_bound} && "
                    f"{idents[f]} + ({delta}) >= -{int_bound}) -> {idents[f]} = {idents[f]} + ({delta});"
                )
                lines.append("          :: else -> skip;  /* out of bound: minicheck refuses here */")
                lines.append("       fi;")
            else:
                lines.append(f"       {idents[f]} = {int(val) if isinstance(val, bool) else val};")
        for inv_name in invs:
            lines.append(f"       assert({_ident(inv_name)});")
        lines.append("     }")
    lines.append("  od;")
    lines.append("}")

    if spec.get("goal") is not None:
        expr, kind = _cond_expr(spec["goal"], "&&", idents=idents)
        goal_expr = expr if kind == "require" else f"!{expr}"
        lines += [
            "",
            "/* Liveness. minicheck checks AG-EF (every reachable state can still reach the goal);",
            " * the closest standard LTL formulation is below. Check it with:",
            " *   spin -a -f '[]<> goal' this.pml",
            " */",
            f"#define goal ({goal_expr})",
            "ltl reaches_goal { []<> goal }",
        ]
    return "\n".join(lines) + "\n"


def to_tla(spec: dict, *, int_bound: int = DEFAULT_INT_BOUND) -> str:
    """A TLA+ module for TLC.

    Emits `Init`, one action per transition, `Next` as their disjunction, and each invariant as a
    named state predicate. A companion `.cfg` is printed in a comment because TLC needs one.
    """
    validate_spec(spec, int_bound=int_bound)
    _check_exportable(spec)

    fields = list(spec["fields"])
    idents = _ident_map(fields)
    mod = _ident(spec.get("name", "Spec")) or "Spec"
    mod = mod[0].upper() + mod[1:]
    vs = ", ".join(idents[f] for f in fields)

    def lit(v):
        return int(v) if isinstance(v, bool) else v

    lines = [
        f"---------------------------- MODULE {mod} ----------------------------",
        "(* Generated from a minicheck spec.",
        " *",
        " * TLC needs a .cfg alongside this file:",
        " *",
        " *   SPECIFICATION Spec",
        *[f" *   INVARIANT {_ident(n)}" for n in (spec.get("invariants") or {})],
        " *",
        f" * Integers are bounded to +/-{int_bound}, matching the minicheck run. TypeOK enforces it,",
        " * so TLC reports a bound escape rather than exploring an infinite space.",
        " *)",
        "EXTENDS Integers",
        "",
        f"VARIABLES {vs}",
        f"vars == <<{vs}>>",
        "",
        "TypeOK == " + " /\\ ".join(f"{idents[f]} \\in -{int_bound}..{int_bound}" for f in fields),
        "",
        "Init == " + " /\\ ".join(f"{idents[f]} = {lit(spec['initial'][f])}" for f in fields),
        "",
    ]

    actions = []
    for i, t in enumerate(spec["transitions"]):
        label = _ident(t.get("label", f"t{i}"))
        actions.append(label)
        guard = [f"{idents[f]} = {lit(v)}" for f, v in (t.get("when") or {}).items()] or ["TRUE"]
        updates, unchanged = [], []
        for f in fields:
            if f in t["set"]:
                val = t["set"][f]
                if isinstance(val, dict):
                    delta = val.get("incr", 0) - val.get("decr", 0)
                    updates.append(f"{idents[f]}' = {idents[f]} + ({delta})")
                else:
                    updates.append(f"{idents[f]}' = {lit(val)}")
            else:
                unchanged.append(idents[f])
        body = guard + updates
        if unchanged:
            body.append("UNCHANGED <<" + ", ".join(unchanged) + ">>")
        # TLA+ bulleted conjunction: every line of the list carries the same /\ marker.
        conj = "/" + "\\"
        lines.append(f"{label} ==")
        for part in body:
            lines.append(f"  {conj} {part}")
        lines.append("")

    lines.append("Next == " + " \\/ ".join(actions))
    lines.append("")
    lines.append("Spec == Init /\\ [][Next]_vars")
    lines.append("")

    for inv_name, cond in (spec.get("invariants") or {}).items():
        expr, kind = _cond_expr(cond, "/\\", eq="=", idents=idents)
        lines.append(f"{_ident(inv_name)} == " + (f"~{expr}" if kind == "forbid" else expr))
    if spec.get("goal") is not None:
        expr, kind = _cond_expr(spec["goal"], "/\\", eq="=", idents=idents)
        lines.append("")
        lines.append("(* minicheck checks AG-EF; the nearest TLA+ property is below. *)")
        lines.append("Goal == " + (expr if kind == "require" else f"~{expr}"))
        lines.append("Liveness == []<>Goal")

    lines.append("")
    lines.append("=" * 72)
    return "\n".join(lines) + "\n"
