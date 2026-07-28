# minicheck

[![install](https://img.shields.io/badge/install-from%20GitHub-blue)](https://github.com/nickharris808/minicheck#install)
[![CI](https://img.shields.io/badge/ci-passing-brightgreen)](https://github.com/nickharris808/minicheck/actions/workflows/ci.yml)
[![tests](https://img.shields.io/badge/tests-99%20passing-brightgreen)](tests/)
[![python](https://img.shields.io/badge/python-3.9%2B-blue)](pyproject.toml)
[![license](https://img.shields.io/badge/license-MIT-green)](LICENSE)
![deps](https://img.shields.io/badge/required%20deps-none-brightgreen)

**An explicit-state model checker in ~1308 lines. Shortest counterexamples. No required dependencies.**

## Why this exists

Model checkers are excellent and almost nobody uses them, because adopting one means adopting a
toolchain: a separate model language, a separate binary, a separate build step, and a translation
layer between your code and the thing being verified. So the state machines that most need checking —
retry logic, lock protocols, session lifecycles — get reasoned about in a code review instead, and
the missed interleaving ships.

`minicheck` trades capability for zero friction. It is a Python object, it runs in your existing test
suite, it has no required dependencies, and the whole engine is short enough to read before you trust
it. Use SPIN or TLC for serious work; use this for the invariant you would otherwise not check at
all.

Describe a finite state machine, assert an invariant, and get back a concrete, shortest trace of how it
breaks. The breadth-first engine is standard library only — `collections`, `dataclasses`, `typing`. SMT
induction is optional and lazily imported.

## Install

```
# from GitHub (PyPI release pending)
pip install "minicheck @ git+https://github.com/nickharris808/minicheck.git"
pip install "minicheck[smt] @ git+https://github.com/nickharris808/minicheck.git"   # + z3 induction
```

> `pip install minicheck` does not work yet — the package is not on PyPI. Install from GitHub as
> shown above. The distribution builds and is `twine check`-clean, with no unpublished
> dependencies, so it is ready to upload whenever that happens.

## 30-second quickstart

```python
from minicheck import Protocol, check_safety

m = Protocol(
    name="counter", candidate=False,
    fields=("n",), initial=(0,),
    transitions=lambda s: [("inc", (s[0] + 1,))] if s[0] < 3 else [],
    invariants={"n_below_3": lambda d: d["n"] < 3},
)

r = check_safety(m)
r["properties"]["n_below_3"]["holds"]          # False
[step["state"]["n"] for step in r["properties"]["n_below_3"]["counterexample"]]
# [0, 1, 2, 3]   <- the shortest way to break it
```

A `Protocol` is: named `fields`, an `initial` tuple, a `transitions` function returning
`[(label, next_state), ...]`, a dict of `invariants` over `{field: value}`, and an optional liveness
`goal`.

## Worked example — a mutual-exclusion bug, found and fixed

Two processes take a lock. The buggy version lets both in.

```python
from minicheck import Protocol, check_safety

def mutex(guarded: bool):
    def step(s):
        a, b, lock = s
        out = []
        if a == 0 and (not guarded or lock == 0):
            out.append(("a_enter", (1, b, 1)))
        if b == 0 and (not guarded or lock == 0):
            out.append(("b_enter", (a, 1, 1)))
        if a == 1:
            out.append(("a_exit", (0, b, 0)))
        if b == 1:
            out.append(("b_exit", (a, 0, 0)))
        return out
    return Protocol(
        name="mutex", candidate=guarded, fields=("a", "b", "lock"), initial=(0, 0, 0),
        transitions=step,
        invariants={"not_both_in": lambda d: not (d["a"] == 1 and d["b"] == 1)},
    )

bad = check_safety(mutex(guarded=False))["properties"]["not_both_in"]
bad["holds"]                                   # False
[s["label"] for s in bad["counterexample"][1:]]  # ['a_enter', 'b_enter']

good = check_safety(mutex(guarded=True))["properties"]["not_both_in"]
good["holds"]                                  # True
```

Two states, two labels, and the exact interleaving that breaks it.

## Liveness is AG-EF, not plain reachability

`check_liveness` asks whether **every reachable state can still reach a goal state** — not merely
whether the goal is reachable from the start. That difference is the point: a run that wanders into a
corner it can never leave passes a reachability check and fails this one.

```python
# 0 -> 1 (the goal), and 0 -> 2 (a dead end)
m = Protocol(name="fork", candidate=False, fields=("n",), initial=(0,),
             transitions=lambda s: [("goal", (1,)), ("dead", (2,))] if s[0] == 0 else [],
             invariants={"trivial": lambda d: True},
             goal=lambda d: d["n"] == 1)

check_liveness(m)["holds"]      # False — state 2 is a trap
```

## What else is in there

| Function | Checks |
|---|---|
| `check_safety` | Invariants over all reachable states; shortest counterexample |
| `check_liveness` | AG-EF co-reachability; reports the trap state |
| `check_bounded_time` | Goal reached within a step bound |
| `check_refinement` | An implementation refines a spec under an abstraction map |
| `check_composition` | Joint invariants over a product of models |
| `check_probabilistic` / `check_statistical` | Absorbing-chain miss probability, exactly and by sampling |
| `check_timed_safety` | Timed-automaton safety |
| `prove_inductive` / `prove_k_induction` | Unbounded SMT induction (needs the `smt` extra) |
| `prove_composition_inductive` | Compositional induction over components |
| `z3_available()` | Whether the SMT half can run |

### Calling conventions worth knowing

Three of these have shapes that are easy to get wrong. Each is pinned by a test.

```python
# components must have DISJOINT fields; invariants are a dict, not a list
check_composition([a, b], {"not_both": lambda d: not (d["x"] and d["y"])})

# decls() is zero-arg and returns a (vars, vars_next) PAIR
prove_inductive(lambda: ({"n": z3.Int("n")}, {"n": z3.Int("n_next")}), init, trans, inv)

# builder() returns a 4-tuple: (clock_vars, constraints, deadline_expr, delay_expr)
def builder():
    a, b = z3.Real("a"), z3.Real("b")
    return [a, b], [a >= 1, a <= 2, b >= 1, b <= 2], z3.RealVal(3), a + b

check_timed_safety(builder)
# {'proven': False, 'counterexample': {'a': '3/2', 'b': '2'}}   <- exact rationals, dense time
```

Every z3 entry point returns `{"available": False, "proven": None}` when z3 is absent. It never raises,
and it never reports `proven` on a solver timeout.

## Why this and not SPIN, TLC, or Storm?

Those are better model checkers with more users and far more capability. Use them for serious work.
`minicheck` is for the case where you want an invariant checked inside a Python test suite without a
toolchain, a model file format, or a subprocess — and where being able to read the whole engine before
you trust it matters more than raw state-space throughput.

## Honest scope

**Verdicts are three-valued, and the third value is the important one.**

| verdict | means | what it took to earn |
|---|---|---|
| `holds: true` | proved | the *entire* reachable space was enumerated and nothing violated the invariant |
| `holds: false` | refuted | one violating state was reached; the attached trace replays |
| `holds: None` | **undetermined** | the search stopped early. Not a pass. |

The asymmetry is deliberate. Refuting a safety property needs one witness, so `false` is sound even
from a partial search. Proving one is a claim about every reachable state, so `true` is only issued
when `exhaustive` is also true. **Never treat `None` as success** — check `exhaustive` and
`incomplete_reason`, which say exactly what stopped the sweep.

**What it proves.** That a finite, explicitly-enumerated model does or does not satisfy an invariant,
over every interleaving. Counterexamples are shortest by construction, because the search is
breadth-first.

**What it does not prove.**

- Nothing about your *implementation*. It checks the model you wrote, and a model abstracts. An
  abstraction can hide a real defect.
- Nothing beyond the bound. The sweep caps at 200,000 states by default and integer fields at
  `int_bound`. Exceeding either downgrades unrefuted invariants to `None` rather than truncating
  silently — but it still means those states were not examined.
- Nothing about liveness under fairness assumptions beyond the AG-EF check, and nothing in LTL.
  There is no partial-order reduction, no symmetry reduction, and no CTL\* fragment beyond AG-EF.
- Nothing when an invariant is trivially satisfied. `spec_warnings` reports a condition that names a
  value the bounded space cannot represent; such a condition genuinely holds, but it verifies nothing.

**Measured performance.** Roughly 1.4×10⁵ to 3.2×10⁵ states/second in CPython on an M-series laptop
(65,536 states in 0.46 s). That is the honest ceiling: this is a readable reference implementation,
not a competitor to SPIN, TLC or NuSMV on industrial models.

**A soundness bug shipped in 0.1.0 and is fixed here.** `int_bound` was applied as a *clamp*, so a
counter that genuinely reached 100 saturated at 64 and a `never reach 100` invariant was reported as
holding. See [SECURITY-ADVISORY.md](SECURITY-ADVISORY.md).

## Tests

```
pip install -e ".[test,smt]" && pytest
```

99 tests, including a check that the core module acquires no third-party import at module level, and
one test per documented function using the exact calling convention shown above.

## Where this came from, and what is not here

`minicheck` is the verification kernel extracted from a larger formal-methods system for
communication protocols. What that system adds on top — and what is deliberately not in this
package — is the part that is hard to rebuild: maintained hazard-property corpora, composition
analysis with a trust-model sensitivity sweep, an evidence-integrity spine that binds a result to
the artifact that produced it, and faithful models of standardized procedures.

If you want the engine, it is here under MIT and always will be. If you want the corpora and the
audit trail, that is the commercial offering.

## The portfolio

Five small, independently useful tools built around one idea: **a verdict you cannot check is not a verdict.**

| | |
|---|---|
| [`minicheck`](https://github.com/nickharris808/minicheck) ← *you are here* | An explicit-state model checker in ~1308 lines. Shortest counterexamples, no required dependencies. |
| [`protocol-bench`](https://github.com/nickharris808/protocol-bench) | 15 published IEEE 802.11 / 3GPP procedures with ground truth. A claimed detection must **replay**. |
| [`minicheck-mcp`](https://github.com/nickharris808/minicheck-mcp) | The checker as an **MCP server** — let an agent verify a state machine instead of guessing. |
| [`polyfrac`](https://github.com/nickharris808/polyfrac) | Exact polynomial + rational-function arithmetic over ℚ with Sturm real-root counting. Zero deps. |
| [`failclosed`](https://github.com/nickharris808/failclosed) | Default-deny ASGI middleware: a gated endpoint succeeds only on an affirmative verdict. |
| [`protocol-bench-action`](https://github.com/nickharris808/protocol-bench-action) | Score a submission in CI and fail the build if a claimed detection cannot be proved |

Try it in your browser: **[live demo](https://huggingface.co/spaces/nickh007/protocol-bench-demo)** · Ground-truth tasks: **[dataset](https://huggingface.co/datasets/nickh007/protocol-bench)**

### The commercial offering

These are the engine. What is **not** open source is what makes it useful at scale: the maintained
hazard-property corpora, composition analysis that finds hazards existing only when two components
are combined, the trust-model sensitivity sweep, and the evidence trail that makes a verdict auditable
after the fact. The tools above are MIT and stay that way.

## Licence

MIT. See `LICENSE`.
