#!/usr/bin/env python3
"""Reproduce every performance number in the README, from this repository alone.

    python bench.py

Two things are measured.

**Throughput** — states per second on the declarative path (what the CLI, the MCP server and the
Space all use) and on the Python-callable path.

**The compiled-vs-interpreted speedup.** `spec.py` compiles a spec's guards and assignments to index
tuples once at build time instead of rebuilding a `dict` and re-reading every guard by name on each
visited state. To make that number reproducible without shipping an old release, the pre-optimisation
transition function is re-implemented below and both are run over the same models. It is the same
oracle `tests/test_adversarial_soundness.py` uses to prove the two agree on every successor of every
reachable state — so this measures a speedup between two implementations that are known to compute
the same thing.

Numbers vary with machine and Python build. The README quotes an M-series laptop on CPython 3.11;
run this to get yours.
"""

from __future__ import annotations

import time

from minicheck import Protocol, check_safety
from minicheck.spec import IntBoundExceeded, protocol_from_spec

# --------------------------------------------------------------------------------- the workloads


def counters(n_fields: int, limit: int) -> dict:
    """`n_fields` independent counters, each rising to `limit`. Space = (limit+1) ** n_fields."""
    fields = [f"f{i}" for i in range(n_fields)]
    return {
        "name": f"counters_{n_fields}x{limit}",
        "fields": fields,
        "initial": dict.fromkeys(fields, 0),
        "transitions": [{"label": f"inc_{f}", "when": {f: v}, "set": {f: v + 1}} for f in fields for v in range(limit)],
        "invariants": {"never_neg": {"forbid": {fields[0]: -1}}},
    }


def ring(n: int) -> dict:
    """A token passed around `n` slots — a wide, shallow space."""
    fields = [f"p{i}" for i in range(n)]
    return {
        "name": f"ring_{n}",
        "fields": fields,
        "initial": {f: (1 if i == 0 else 0) for i, f in enumerate(fields)},
        "transitions": [
            {
                "label": f"pass_{i}",
                "when": {fields[i]: 1, fields[(i + 1) % n]: 0},
                "set": {fields[i]: 0, fields[(i + 1) % n]: 1},
            }
            for i in range(n)
        ],
        "invariants": {"not_stuck": {"forbid": dict.fromkeys(fields, 2)}},
    }


WORKLOADS = [counters(2, 40), counters(3, 12), counters(4, 7), ring(9)]

# ------------------------------------------------------------- the pre-optimisation implementation


def interpreted_transitions(spec, fields, idx, int_bound):
    """The transition function as it was before `_compile_rules`, rebuilt per call.

    Kept identical to the oracle in tests/test_adversarial_soundness.py, including the bound check —
    comparing a bounded implementation against an unbounded one would compare two different
    functions and overstate the win.
    """

    def transitions(s):
        d = dict(zip(fields, s))
        out = []
        for i, t in enumerate(spec["transitions"]):
            label = t.get("label", f"t{i}")
            if not all(d.get(f) == v for f, v in (t.get("when") or {}).items()):
                continue
            nxt = list(s)
            for f, val in t["set"].items():
                if isinstance(val, dict):
                    cur = d.get(f)
                    if not isinstance(cur, int) or isinstance(cur, bool):
                        continue
                    v = cur + val.get("incr", 0) - val.get("decr", 0)
                    if not (-int_bound <= v <= int_bound):
                        raise IntBoundExceeded(f"{label} drives {f} to {v}")
                    nxt[idx[f]] = v
                else:
                    nxt[idx[f]] = val
            out.append((label, tuple(nxt)))
        return out

    return transitions


def as_interpreted(spec: dict) -> Protocol:
    """The same model, wired to the pre-optimisation transition function."""
    fields = tuple(spec["fields"])
    idx = {f: i for i, f in enumerate(fields)}
    return Protocol(
        name=spec["name"],
        candidate=False,
        fields=fields,
        initial=tuple(spec["initial"][f] for f in fields),
        transitions=interpreted_transitions(spec, fields, idx, 64),
        invariants={
            name: (lambda d, b=body: not all(d.get(f) == v for f, v in b["forbid"].items()))
            for name, body in spec["invariants"].items()
        },
    )


# ------------------------------------------------------------------------------------- the harness


def timed(protocol, repeats: int = 3):
    """Best of `repeats` — the minimum is the least noisy estimator for a deterministic workload."""
    best, states = float("inf"), 0
    for _ in range(repeats):
        t0 = time.perf_counter()
        res = check_safety(protocol, max_states=2_000_000)
        best = min(best, time.perf_counter() - t0)
        states = res["reachable_states"]
    return best, states


def main() -> None:
    print("compiled vs interpreted — the same models, both implementations")
    print(f"  {'model':16s} {'states':>8s} {'interp':>9s} {'compiled':>9s} {'speedup':>8s}")
    speedups = []
    for spec in WORKLOADS:
        t_new, n = timed(protocol_from_spec(spec))
        t_old, n_old = timed(as_interpreted(spec))
        assert n == n_old, f"{spec['name']}: {n} vs {n_old} states — not the same model"
        speedups.append(t_old / t_new)
        print(f"  {spec['name']:16s} {n:8d} {t_old * 1e3:8.1f}ms {t_new * 1e3:8.1f}ms {t_old / t_new:7.2f}x")
    lo, hi = min(speedups), max(speedups)
    print(f"\n  mean {sum(speedups) / len(speedups):.2f}x   range {lo:.2f}x-{hi:.2f}x")

    print("\nthroughput")
    dec = [timed(protocol_from_spec(s))[1] / timed(protocol_from_spec(s))[0] for s in WORKLOADS]
    print(f"  declarative path   {min(dec):,.0f} - {max(dec):,.0f} states/s")

    # A Python callable doing the same job, to show where the ceiling actually is.
    def callable_counter(s):
        return [("inc", (s[0] + 1, s[1]))] if s[0] < 40 else ([("inc2", (0, s[1] + 1))] if s[1] < 40 else [])

    p = Protocol(
        name="callable",
        candidate=False,
        fields=("a", "b"),
        initial=(0, 0),
        transitions=callable_counter,
        invariants={"ok": lambda d: d["a"] >= 0},
    )
    t, n = timed(p)
    print(f"  Python callable    {n / t:,.0f} states/s")


if __name__ == "__main__":
    main()
