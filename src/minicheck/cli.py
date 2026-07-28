"""Command line: check a declarative spec file without writing any Python.

The declarative spec format already existed, but the only way to use it was to import the library.
That left the most common case — "I have a state machine written down, is it safe?" — needing a
Python harness. This closes that.

    minicheck check spec.json
    minicheck check spec.json --json          # machine-readable
    minicheck check spec.json --int-bound 500 # widen the bounded integer range
    minicheck example > spec.json             # a spec to start from

Exit codes are the point, because this is meant to run in CI:

    0   PROVED       every reachable state was enumerated; no invariant was violated
    2   REFUTED      a counterexample was found (it is printed, and it replays)
    3   UNDETERMINED the search did not finish, so nothing was established
    4   BAD SPEC     the file is not a well-formed spec; the message names the key

3 is deliberately NOT 0. A gate that treats "I could not tell" as success is the failure this
whole package exists to avoid, so an incomplete search fails the job by default. Pass
``--allow-undetermined`` if you consciously want it to pass.
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import Any

from ._core import check_liveness, check_safety
from .export import ExportError, to_promela, to_tla
from .render import RenderTooLarge, to_dot, to_mermaid, to_svg
from .report import to_junit, to_sarif
from .spec import DEFAULT_INT_BOUND, SpecError, protocol_from_spec, spec_warnings
from .verdict import EXIT_ERROR as EXIT_BAD_SPEC
from .verdict import EXIT_PROVED, EXIT_REFUTED, EXIT_UNDETERMINED, combine, exit_code, from_holds

# Re-exported: callers and tests import the exit codes from here as the CLI's public contract.
__all__ = [
    "main",
    "build_parser",
    "FORMATS",
    "EXIT_PROVED",
    "EXIT_REFUTED",
    "EXIT_UNDETERMINED",
    "EXIT_BAD_SPEC",
]

FORMATS = ("text", "json", "sarif", "junit", "mermaid", "dot", "svg", "promela", "tla")

EXAMPLE_SPEC = {
    "name": "mutex",
    "fields": ["a", "b", "lock"],
    "initial": {"a": 0, "b": 0, "lock": 0},
    "transitions": [
        {"label": "a_enter", "when": {"a": 0}, "set": {"a": 1, "lock": 1}},
        {"label": "b_enter", "when": {"b": 0}, "set": {"b": 1, "lock": 1}},
        {"label": "a_exit", "when": {"a": 1}, "set": {"a": 0, "lock": 0}},
        {"label": "b_exit", "when": {"b": 1}, "set": {"b": 0, "lock": 0}},
    ],
    "invariants": {"not_both": {"forbid": {"a": 1, "b": 1}}},
}


def _fmt_state(state: dict) -> str:
    return ", ".join(f"{k}={v}" for k, v in state.items())


def _load(path: str) -> dict:
    """Read a spec file, or `-` for stdin. Errors explain the fix, not just the fault."""
    try:
        raw = sys.stdin.read() if path == "-" else open(path, encoding="utf-8").read()
    except FileNotFoundError:
        raise SpecError(
            f"no such file: {path}\n"
            f"  Write a spec first, or start from the built-in one:\n"
            f"    minicheck example > spec.json"
        ) from None
    except OSError as e:
        raise SpecError(f"could not read {path}: {e}") from None
    try:
        return json.loads(raw)
    except json.JSONDecodeError as e:
        line = raw.splitlines()[e.lineno - 1] if 0 < e.lineno <= len(raw.splitlines()) else ""
        raise SpecError(
            f"{path} is not valid JSON: {e.msg} at line {e.lineno}, column {e.colno}\n"
            f"    {line.strip()}\n"
            f"  A spec is a JSON object. Trailing commas and single quotes are not JSON."
        ) from None


def _render(res: dict, live: dict | None, warnings: list, verdict: str) -> str:
    out = [f"{verdict}", ""]
    out.append(f"  states explored   {res['reachable_states']:,}")
    out.append(f"  exhaustive        {'yes' if res['exhaustive'] else 'NO'}")
    if not res["exhaustive"]:
        out.append(f"  stopped because   {res.get('incomplete_reason', 'the search did not finish')}")
    out.append("")

    for name, prop in res["properties"].items():
        if prop["holds"] is True:
            out.append(f"  [proved]       {name}")
        elif prop["holds"] is None:
            out.append(f"  [undetermined] {name}")
            out.append("                 no violation seen, but the search did not cover everything")
        else:
            cex = prop["counterexample"]
            out.append(f"  [REFUTED]      {name} — violated in {len(cex) - 1} steps")
            for i, step in enumerate(cex):
                label = step["label"] or "(initial)"
                out.append(f"      {i:>3}  {label:<16} {_fmt_state(step['state'])}")
    if live is not None:
        symbol = {True: "[proved]      ", False: "[REFUTED]     ", None: "[undetermined]"}[live["holds"]]
        out.append("")
        out.append(f"  {symbol} liveness — every reachable state can still reach the goal")
        if live["holds"] is False and live.get("counterexample"):
            trap = live["counterexample"][-1]["state"]
            out.append(f"                 trap state: {_fmt_state(trap)}")

    if warnings:
        out.append("")
        for w in warnings:
            out.append(f"  warning: {w}")
    if not res["exhaustive"]:
        out.append("")
        out.append("  To get a definite answer, either raise --int-bound, or add a 'when' guard so")
        out.append("  the growing field stops. An undetermined result is not a pass.")
    return "\n".join(out)


def _verdict(res: dict, live: dict | None) -> tuple[str, int]:
    """Aggregate to one verdict, via the shared contract in `minicheck.verdict`.

    The precedence rules live in one place so the CLI, the MCP server and every emitter cannot
    drift apart on what "undetermined" means.
    """
    exh = res["exhaustive"]
    parts = [from_holds(p["holds"], exhaustive=exh) for p in res["properties"].values()]
    if live is not None:
        parts.append(from_holds(live["holds"], exhaustive=exh))
    v = combine(parts)
    return v.value, exit_code(v)


def cmd_check(args) -> int:
    try:
        spec = _load(args.spec)
        model = protocol_from_spec(spec, int_bound=args.int_bound)
    except SpecError as e:
        if args.json:
            print(json.dumps({"ok": False, "verdict": "BAD_SPEC", "error": str(e)}, indent=2))
        else:
            print(f"BAD SPEC\n\n  {e}", file=sys.stderr)
        return EXIT_BAD_SPEC

    if not model.invariants and model.goal is None:
        msg = (
            "the spec declares no 'invariants' and no 'goal', so there is nothing to check.\n"
            '  Add an invariant, e.g.  "invariants": {"safe": {"forbid": {"a": 1, "b": 1}}}'
        )
        if args.json:
            print(json.dumps({"ok": False, "verdict": "BAD_SPEC", "error": msg}, indent=2))
        else:
            print(f"BAD SPEC\n\n  {msg}", file=sys.stderr)
        return EXIT_BAD_SPEC

    res = check_safety(model, max_states=args.max_states)
    live = check_liveness(model) if model.goal is not None else None
    warnings = spec_warnings(spec, args.int_bound)
    verdict, code = _verdict(res, live)

    if args.allow_undetermined and code == EXIT_UNDETERMINED:
        code = EXIT_PROVED

    fmt = getattr(args, "format", None) or ("json" if args.json else "text")

    if fmt in ("mermaid", "dot", "svg"):
        # A diagram needs a specific counterexample; pick the first refuted invariant.
        cex = next((p["counterexample"] for p in res["properties"].values() if p["holds"] is False), None)
        try:
            if fmt == "mermaid":
                print(to_mermaid(model, cex, verdict=verdict, max_nodes=args.max_nodes))
            elif fmt == "dot":
                print(to_dot(model, cex, verdict=verdict, max_nodes=args.max_nodes))
            else:
                if cex is None:
                    print(
                        "BAD SPEC\n\n  --format svg draws a counterexample, and this spec has none "
                        "(verdict " + verdict + "). Use --format mermaid or dot to draw the whole "
                        "reachable graph instead.",
                        file=sys.stderr,
                    )
                    return EXIT_BAD_SPEC
                print(to_svg(model, cex, verdict=verdict, max_nodes=args.max_nodes))
        except RenderTooLarge as e:
            print(f"BAD SPEC\n\n  {e}", file=sys.stderr)
            return EXIT_BAD_SPEC
        return code

    if fmt in ("promela", "tla"):
        # An export is a translation, not a verdict: emit it and exit 0 unless the spec itself is
        # unexportable. Reporting the check's verdict here would conflate "your model is broken"
        # with "the translation failed".
        try:
            print(
                to_promela(spec, int_bound=args.int_bound)
                if fmt == "promela"
                else to_tla(spec, int_bound=args.int_bound)
            )
        except ExportError as e:
            print(f"BAD SPEC\n\n  {e}", file=sys.stderr)
            return EXIT_BAD_SPEC
        return EXIT_PROVED

    if fmt == "sarif":
        print(to_sarif(res, spec_path=args.spec))
        return code
    if fmt == "junit":
        print(to_junit(res, spec_path=args.spec))
        return code

    if fmt == "json":
        payload: dict[str, Any] = {
            "ok": True,
            "verdict": verdict,
            "exhaustive": res["exhaustive"],
            "reachable_states": res["reachable_states"],
            "invariants": res["properties"],
            "exit_code": code,
        }
        if not res["exhaustive"]:
            payload["incomplete_reason"] = res.get("incomplete_reason")
        if live is not None:
            payload["liveness"] = live
        if warnings:
            payload["warnings"] = warnings
        print(json.dumps(payload, indent=2, default=str))
    else:
        print(_render(res, live, warnings, verdict))
    return code


def cmd_validate(args) -> int:
    """Schema-check without running the search. Fast, and safe on an untrusted spec."""
    try:
        spec = _load(args.spec)
        protocol_from_spec(spec, int_bound=args.int_bound)
    except SpecError as e:
        if args.json:
            print(json.dumps({"ok": False, "valid": False, "error": str(e)}, indent=2))
        else:
            print(f"INVALID\n\n  {e}", file=sys.stderr)
        return EXIT_BAD_SPEC
    warnings = spec_warnings(spec, args.int_bound)
    if args.json:
        print(json.dumps({"ok": True, "valid": True, "warnings": warnings}, indent=2))
    else:
        print("VALID")
        for w in warnings:
            print(f"  warning: {w}")
    return EXIT_PROVED


def cmd_example(args) -> int:
    print(json.dumps(EXAMPLE_SPEC, indent=2))
    return EXIT_PROVED


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="minicheck",
        description="Check a declarative state-machine spec. Exit 0 proved, 2 refuted, 3 undetermined, 4 bad spec.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "examples:\n"
            "  minicheck example > spec.json      write a starting spec\n"
            "  minicheck check spec.json          check it\n"
            "  minicheck check - < spec.json      read from stdin\n"
            "  minicheck check spec.json --json   machine-readable output\n"
        ),
    )
    sub = p.add_subparsers(dest="command", required=True)

    def add_common(sp):
        sp.add_argument("spec", help="path to a spec JSON file, or - for stdin")
        sp.add_argument("--json", action="store_true", help="emit JSON instead of text")
        sp.add_argument(
            "--int-bound",
            type=int,
            default=DEFAULT_INT_BOUND,
            metavar="N",
            help=f"largest magnitude an integer field may take (default {DEFAULT_INT_BOUND}). "
            "Leaving it stops the search rather than truncating it.",
        )

    c = sub.add_parser("check", help="check the spec's invariants and goal")
    add_common(c)
    c.add_argument(
        "--max-states",
        type=int,
        default=200000,
        metavar="N",
        help="stop after this many reachable states (default 200000)",
    )
    c.add_argument(
        "--format",
        choices=FORMATS,
        default=None,
        help="output format (default text). sarif -> GitHub code scanning; junit -> CI test "
        "reports; mermaid/dot/svg -> a diagram of the counterexample.",
    )
    c.add_argument(
        "--max-nodes",
        type=int,
        default=60,
        metavar="N",
        help="refuse to draw a graph larger than this (default 60). A diagram nobody can read is not a diagram.",
    )
    c.add_argument(
        "--allow-undetermined",
        action="store_true",
        help="exit 0 instead of 3 when the search does not finish. Off by default: an "
        "undetermined result is not a pass.",
    )
    c.set_defaults(func=cmd_check)

    v = sub.add_parser("validate", help="schema-check the spec without running the search")
    add_common(v)
    v.set_defaults(func=cmd_validate)

    e = sub.add_parser("example", help="print a worked example spec to stdout")
    e.set_defaults(func=cmd_example)
    return p


def main(argv=None) -> int:
    args = build_parser().parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
