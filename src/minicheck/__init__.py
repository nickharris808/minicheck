"""minicheck — an explicit-state model checker in ~560 lines, no required dependencies.

Define a finite state machine, assert an invariant, get a SHORTEST counterexample trace when it fails.

>>> from minicheck import Protocol, check_safety
>>> m = Protocol(
...     name="counter", candidate=False, fields=("n",), initial=(0,),
...     transitions=lambda s: [("inc", (s[0] + 1,))] if s[0] < 3 else [],
...     invariants={"n_below_3": lambda d: d["n"] < 3},
... )
>>> r = check_safety(m)
>>> r["properties"]["n_below_3"]["holds"]
False
>>> len(r["properties"]["n_below_3"]["counterexample"])   # initial + 3 increments
4

The breadth-first engine is standard library only. SMT-backed induction (`prove_inductive`,
`prove_k_induction`) imports z3 lazily; call `z3_available()` to check, and install the `smt` extra to
enable it.

**When in doubt, minicheck refuses.** Every entry point is built so that "I could not determine this"
is a distinct outcome from "this holds", and it is never quietly upgraded:

* a search that exceeds `max_states` raises `RuntimeError` rather than reporting a partial sweep;
* a spec whose integers leave `int_bound` raises `IntBoundExceeded` rather than saturating them;
* a vacuous SMT encoding returns ``proven=False, vacuous=True`` with the reason named;
* a singular probability system raises `SingularSystem` rather than returning a sentinel;
* an unasked question (no goal) returns ``holds=None``, not ``True``.
"""

from ._core import (
    Protocol,
    SingularSystem,
    check_bounded_time,
    check_composition,
    check_liveness,
    check_probabilistic,
    check_refinement,
    check_safety,
    check_statistical,
    check_timed_safety,
    prove_composition_inductive,
    prove_inductive,
    prove_k_induction,
    prove_latency_bound,
    z3_available,
)
from .spec import (
    DEFAULT_INT_BOUND,
    IntBoundExceeded,
    SpecError,
    protocol_from_spec,
    spec_warnings,
    validate_spec,
)

__all__ = [
    "Protocol",
    "check_safety",
    "check_liveness",
    "check_bounded_time",
    "check_refinement",
    "check_composition",
    "check_probabilistic",
    "check_statistical",
    "check_timed_safety",
    "prove_inductive",
    "prove_k_induction",
    "prove_composition_inductive",
    "prove_latency_bound",
    "z3_available",
    "protocol_from_spec",
    "validate_spec",
    "spec_warnings",
    "SpecError",
    "IntBoundExceeded",
    "SingularSystem",
    "DEFAULT_INT_BOUND",
    "__version__",
]
__version__ = "0.2.0"
