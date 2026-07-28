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
"""

from ._core import (
    Protocol,
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
from .spec import SpecError, protocol_from_spec, validate_spec

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
    "SpecError",
    "__version__",
]
__version__ = "0.1.0"
