# minicheck

[![install](https://img.shields.io/badge/install-from%20GitHub-blue)](https://github.com/nickharris808/minicheck#install)
[![CI](https://img.shields.io/badge/ci-passing-brightgreen)](https://github.com/nickharris808/minicheck/actions/workflows/ci.yml)
[![tests](https://img.shields.io/badge/tests-270%20passing-brightgreen)](tests/)
[![python](https://img.shields.io/badge/python-3.9%2B-blue)](pyproject.toml)
[![license](https://img.shields.io/badge/license-MIT-green)](LICENSE)
![deps](https://img.shields.io/badge/required%20deps-none-brightgreen)

**An explicit-state model checker in ~2888 lines. Shortest counterexamples. No required dependencies.**

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

## Command line

No Python needed. Write the state machine as JSON and check it:

```console
$ minicheck example > spec.json
$ minicheck check spec.json
REFUTED

  states explored   6
  exhaustive        yes

  [REFUTED]      not_both — violated in 2 steps
        0  (initial)        a=0, b=0, lock=0
        1  a_enter          a=1, b=0, lock=1
        2  b_enter          a=1, b=1, lock=1
$ echo $?
2
```

Add the missing `lock` guard to both `when` clauses and it proves:

```console
$ minicheck check spec.json
PROVED

  states explored   3
  exhaustive        yes

  [proved]       not_both
$ echo $?
0
```

### Output formats

`--format` puts the verdict where you already look.

| Format | For |
|---|---|
| `text` *(default)* | reading in a terminal |
| `json` | scripting; carries `exit_code`, `exhaustive`, `incomplete_reason` |
| `sarif` | **GitHub code scanning** — a refuted invariant appears in the Security tab, trace and all |
| `junit` | any CI test reporter |
| `mermaid` | a state diagram that **renders natively in a GitHub PR or issue** |
| `dot` | Graphviz, for papers and full layout control |
| `svg` | self-contained image of the trace, no toolchain |

```console
$ minicheck check spec.json --format mermaid
stateDiagram-v2
    %% verdict: REFUTED
    [*] --> S0
    S0 : a=0, b=0, lock=0
    S1 : a=1, b=0, lock=1
    ...
    S0 --> S1 : 1. a_enter
    S1 --> S3 : 2. b_enter
    classDef cex fill:#fdd,stroke:#c00,stroke-width:2px
```

Paste that into a PR comment and GitHub draws it. The counterexample path is highlighted and its
steps are **numbered**, so the order is unambiguous rather than left to the reader.

**How a three-valued verdict maps onto two-valued formats.** This is the part that is easy to get
wrong, and it is resolved the same way everywhere: *UNDETERMINED is not a pass.*

| Verdict | SARIF | JUnit |
|---|---|---|
| PROVED | `kind: pass` | passing test case |
| REFUTED | `level: error, kind: fail` + `codeFlows` with the trace | `<failure>` |
| **UNDETERMINED** | `kind: informational, level: warning` — never `pass` | **`<error>`** |

JUnit's `<skipped>` would have been the tempting choice for UNDETERMINED. It is wrong: every CI
dashboard renders a skipped test green, which would quietly restore the exact defect this package
exists to prevent. It is reported as `<error>`, with `skipped="0"`.

A graph above `--max-nodes` (default 60) is **refused rather than drawn**. A hairball is not a
diagram, and the point of the picture is to understand one counterexample, not to survey a space.

### Exit codes

Designed for CI, so the shell sees the verdict:

| Code | Verdict | Meaning |
|---|---|---|
| `0` | `PROVED` | the whole reachable space was enumerated; nothing violated an invariant |
| `2` | `REFUTED` | a counterexample was found. It is printed, and it replays |
| `3` | `UNDETERMINED` | **the search did not finish, so nothing was established** |
| `4` | `BAD SPEC` | the file is not a well-formed spec; the message names the key |

**3 is deliberately not 0.** A gate that treats "I could not tell" as success is exactly the failure
this package exists to prevent. Pass `--allow-undetermined` if you consciously want it to pass —
that flag widens only the undetermined case and never masks a real counterexample.

```yaml
# in a workflow
- run: pip install "minicheck @ git+https://github.com/nickharris808/minicheck.git"
- run: minicheck check protocol.json
```

### Commands and flags

| | |
|---|---|
| `minicheck check SPEC` | check invariants, and liveness if the spec has a `goal` |
| `minicheck validate SPEC` | schema-check only. Does not run the search, so it terminates on any spec |
| `minicheck example` | print a worked spec to stdout |
| `--format F` | `text`, `json`, `sarif`, `junit`, `mermaid`, `dot`, `svg`, `promela`, `tla` |
| `--json` | shorthand for `--format json` |
| `--max-nodes N` | refuse to draw a graph larger than this (default 60) |
| `--int-bound N` | largest magnitude an integer field may take (default 64) |
| `--max-states N` | stop after this many reachable states (default 200000) |
| `--allow-undetermined` | exit 0 instead of 3 when the search does not finish |

`SPEC` may be `-` to read from stdin.

## Tutorial — from a bug to a proof

A worked end-to-end pass over a retry loop, the kind of thing that ships unchecked because it "looks
obviously right". Every console block below is real output; you can reproduce it verbatim.

**The claim to check.** *A request is retried at most three times, and always finishes.*

**1. Write it down.** Save as `retry.json`:

```json
{
  "name": "retry",
  "fields": ["tries", "done"],
  "initial": {"tries": 0, "done": 0},
  "transitions": [
    {"label": "attempt", "when": {"done": 0}, "set": {"tries": {"incr": 1}}},
    {"label": "succeed", "when": {"done": 0}, "set": {"done": 1}}
  ],
  "invariants": {"at_most_3": {"forbid": {"tries": 4}}},
  "goal": {"require": {"done": 1}}
}
```

**2. Check it.**

```console
$ minicheck check retry.json
REFUTED

  states explored   129
  exhaustive        NO
  stopped because   IntBoundExceeded: transition 'attempt' drives field 'tries' to 65, outside int_bound 64. The state space is not finite under this bound, so no exhaustive verdict is available. Re-run with int_bound >= 65.

  [REFUTED]      at_most_3 — violated in 4 steps
        0  (initial)        tries=0, done=0
        1  attempt          tries=1, done=0
        2  attempt          tries=2, done=0
        3  attempt          tries=3, done=0
        4  attempt          tries=4, done=0

  [undetermined] liveness — every reachable state can still reach the goal

  To get a definite answer, either raise --int-bound, or add a 'when' guard so
  the growing field stops. An undetermined result is not a pass.
$ echo $?
2
```

Three things are happening at once, and it is worth separating them.

* **`at_most_3` is REFUTED** — the exact four steps that break it. Nothing bounds `attempt`, so it
  fires forever. This verdict is trustworthy even though the search never finished: a counterexample
  carries its own witness, and that trace replays.
* **`exhaustive NO`** — `tries` grows without limit, so the search stopped at the bound rather than
  saturating there and reporting a proof it had not performed.
* **liveness is `undetermined`, not refuted** — proving that *every* state can still reach the goal
  is a claim about the whole space, and the whole space was not explored. So it abstains.

**3. Fix it.** Guard each attempt on the counter, so the loop is genuinely bounded:

```json
{
  "name": "retry",
  "fields": ["tries", "done"],
  "initial": {"tries": 0, "done": 0},
  "transitions": [
    {"label": "attempt1", "when": {"done": 0, "tries": 0}, "set": {"tries": {"incr": 1}}},
    {"label": "attempt2", "when": {"done": 0, "tries": 1}, "set": {"tries": {"incr": 1}}},
    {"label": "attempt3", "when": {"done": 0, "tries": 2}, "set": {"tries": {"incr": 1}}},
    {"label": "succeed",  "when": {"done": 0},             "set": {"done": 1}}
  ],
  "invariants": {"at_most_3": {"forbid": {"tries": 4}}},
  "goal": {"require": {"done": 1}}
}
```

```console
$ minicheck check retry.json
PROVED

  states explored   8
  exhaustive        yes

  [proved]       at_most_3

  [proved]       liveness — every reachable state can still reach the goal
$ echo $?
0
```

Eight states, all of them examined. That is a proof over the model, not a sample of it.

**4. See what the liveness check is actually doing.** Delete the `succeed` transition and re-run:

```console
$ minicheck check retry.json
REFUTED

  states explored   4
  exhaustive        yes

  [proved]       at_most_3

  [REFUTED]      liveness — every reachable state can still reach the goal
                 trap state: tries=0, done=0
$ echo $?
2
```

`at_most_3` still holds — the retry bound is fine. But the goal `done=1` is now unreachable from
everywhere, including the initial state, so every state is a trap. A plain "is the goal reachable"
check reports the same thing; the difference shows up in models where the goal *is* reachable down
one branch and permanently lost down another. AG-EF catches that; reachability does not.

**5. Put it in CI.**

```yaml
- run: pip install "minicheck @ git+https://github.com/nickharris808/minicheck.git"
- run: minicheck check retry.json
```

Exit 0 as it stands, 2 if someone removes a guard, 3 if a later edit makes the space unbounded again.
All three are the right answer, and none of them is a silent pass.

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

## Describe the model as a Python class

The `Protocol` constructor above is honest and hostile — positional tuples, index arithmetic. The
same machine, written as a class:

```python
from minicheck import Model, check_safety, invariant, transition

class Mutex(Model):
    a: int = 0
    b: int = 0
    lock: int = 0

    @transition(when=lambda s: s.a == 0 and s.lock == 0)
    def a_enter(s):
        s.a = 1
        s.lock = 1

    @transition(when=lambda s: s.b == 0 and s.lock == 0)
    def b_enter(s):
        s.b = 1
        s.lock = 1

    @transition(when=lambda s: s.a == 1)
    def a_exit(s):
        s.a = 0
        s.lock = 0

    @invariant
    def not_both(s):
        return not (s.a and s.b)

check_safety(Mutex.protocol())["properties"]["not_both"]["holds"]   # True
```

Fields come from annotations, so the state tuple is in the order you wrote them. This compiles to
exactly the same `Protocol`, and a test asserts the two forms produce identical reachable sets.

**The guard is separate from the body deliberately.** Inferring "enabled" from "the body changed
something" would make a legitimate self-loop indistinguishable from a disabled transition. A bare
`@transition` is always enabled; `when=` narrows it.

Assigning a field you did not declare raises rather than inventing state the search never explores.

## Export to SPIN and TLA+

`minicheck` is small on purpose, and explicit-state search in CPython runs out of room somewhere
around 10⁵–10⁶ states. When your model outgrows that, the honest answer is to use a real one — so it
exports rather than stranding you:

```console
$ minicheck check spec.json --format promela > model.pml
$ spin -a model.pml && gcc -o pan pan.c && ./pan -a
pan:1: assertion violated  !(((a==1)&&(b==1))) (at depth 3)
State-vector 20 byte, depth reached 3, errors: 1
```

`--format tla` emits a TLA+ module for TLC, with `Init`, one action per transition, `Next`, and each
invariant as a named state predicate.

**These are cross-checked, not just generated.** The test suite runs SPIN on the exported model and
requires its verdict to match `minicheck`'s, on models where the answer is known both ways. CI
installs SPIN so that differential actually runs rather than skipping. An export that encodes a
subtly different machine would give you two green results where one is about the wrong system — that
is the failure this guards against.

Non-integer fields are **refused**, not mapped onto integers: a silent encoding would produce
counterexamples that do not correspond to yours.

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

**Measured performance — run `python bench.py` to reproduce all of it on your own machine.**
Declarative specs (`protocol_from_spec`, the CLI, the MCP server) run at roughly **2.5×10⁵ to 7.5×10⁵
states/second** in CPython 3.11 on an M-series laptop — the spread is across workload shapes, and it
moves by ±15% between runs on the same machine, so treat it as an order of magnitude rather than a
figure.

The spec's guards and assignments are compiled to index tuples once at build time rather than
re-interpreted on every visited state. `bench.py` measures that against the *pre-optimisation*
transition function, which it re-implements inline — so the comparison needs nothing but this
repository, and the baseline is the same oracle `tests/test_adversarial_soundness.py` uses to prove
the two agree on every successor of every reachable state. The optimisation therefore cannot change
a verdict. On the reference machine the mean is **4.7×** (range 2.7×–6.6×); the guarantee the test
suite enforces is the floor, **never below 2× on any benchmarked workload**.

Models built from a Python `transitions` callable are bounded by *your* function, not by the engine —
profiling puts ~80% of the time inside it. `bench.py`'s deliberately trivial callable reaches
~2×10⁶ states/second, which is the ceiling you approach as the callable gets cheaper, not a figure to
expect from a real one. That is the honest ceiling overall: this is a readable reference
implementation, not a competitor to SPIN, TLC or NuSMV on industrial models.

**A soundness bug shipped in 0.1.0 and is fixed here.** `int_bound` was applied as a *clamp*, so a
counter that genuinely reached 100 saturated at 64 and a `never reach 100` invariant was reported as
holding. See [SECURITY-ADVISORY.md](SECURITY-ADVISORY.md).

## Troubleshooting

**`UNDETERMINED`, `exhaustive NO`, `IntBoundExceeded`.** A field grows without limit, so the space is
not finite. Either bound it in the model — a `when` guard that stops the increment — or raise
`--int-bound` if the real range is genuinely larger. Do not reach for `--allow-undetermined` to make
this go away; it converts a non-answer into a pass.

**`UNDETERMINED` with `state space > 200000`.** The model is finite but large. Raise `--max-states`,
or cut the state space: fewer fields, smaller ranges, or a coarser abstraction. Throughput is roughly
2.5×10⁵–7.5×10⁵ states/second on the declarative path (measured, see *Honest scope*), so a million
states is a few seconds and tens of millions is not this tool.

**`holds` is `None` and I expected `True`.** That is the same case as above, surfaced through the
library rather than the CLI. Check `result["exhaustive"]` and `result["incomplete_reason"]`. A `None`
is never a pass.

**`warning: ... trivially satisfied`.** An invariant names a value the bounded space cannot
represent, so it holds for a reason unrelated to your protocol. Usually a typo in the literal, or an
`int_bound` set below the value you meant to forbid.

**`SpecError: 'initial' must assign exactly the declared fields`.** Every name in `fields` needs a
starting value, and `initial` may not name anything else. The message lists what is missing and what
is unknown.

**`ValueError: composed models must have disjoint field names`.** `check_composition` keys the
product state by field name, so two components both called `x` would silently become one variable.
Prefix them with the component name.

**`prove_inductive` returns `vacuous: True`.** The encoding makes every obligation trivially valid —
usually `decls()` returning the *same* z3 variable for the current and next state, which makes the
transition relation unsatisfiable. Return two disjoint copies.

**`{"available": false}` from a `prove_*` function.** z3 is not installed. `pip install
"minicheck[smt] @ git+https://github.com/nickharris808/minicheck.git"`. The BFS half never needs it.

**The counterexample looks longer than necessary.** It is not — the search is breadth-first, so the
first violating state found is at minimum depth. If a shorter path exists in your head, the model
probably permits a transition you did not intend.

## Tests

```
pip install -e ".[test,smt]" && pytest
```

270 tests, including a check that the core module acquires no third-party import at module level, and
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
| [`minicheck`](https://github.com/nickharris808/minicheck) ← *you are here* | An explicit-state model checker in ~2888 lines, with a CLI. Shortest counterexamples, no required dependencies. |
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
