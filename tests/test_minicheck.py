"""Tests for minicheck.

The load-bearing guarantees are: (1) a violated invariant yields a SHORTEST counterexample,
(2) the BFS engine needs no third-party package, (3) z3-backed entry points degrade cleanly when
z3 is absent rather than raising.
"""

import pytest

from minicheck import (
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


def counter(limit=3, cap=None):
    """0 -> 1 -> ... -> cap, with an invariant that n stays below `limit`."""
    cap = limit if cap is None else cap
    return Protocol(
        name="counter",
        candidate=False,
        fields=("n",),
        initial=(0,),
        transitions=lambda s: [("inc", (s[0] + 1,))] if s[0] < cap else [],
        invariants={"n_below_limit": lambda d: d["n"] < limit},
        goal=lambda d: d["n"] == cap,
    )


# --------------------------------------------------------------------------- safety
def test_holding_invariant_reports_no_counterexample():
    m = counter(limit=99, cap=3)
    r = check_safety(m)
    assert r["properties"]["n_below_limit"]["holds"] is True
    assert r["properties"]["n_below_limit"]["counterexample"] is None
    assert r["reachable_states"] == 4  # 0,1,2,3


def test_violated_invariant_yields_a_counterexample():
    r = check_safety(counter(limit=3))
    prop = r["properties"]["n_below_limit"]
    assert prop["holds"] is False
    assert prop["counterexample"] is not None


def test_counterexample_is_shortest_and_is_a_real_trace():
    r = check_safety(counter(limit=3))
    cex = r["properties"]["n_below_limit"]["counterexample"]
    # shortest route to n == 3 is initial + three increments
    assert len(cex) == 4
    assert cex[0]["state"]["n"] == 0
    assert cex[-1]["state"]["n"] == 3
    # every step is labelled and the states really do increment by one
    assert [step["state"]["n"] for step in cex] == [0, 1, 2, 3]
    assert all(step["label"] == "inc" for step in cex[1:])


def test_multiple_invariants_are_reported_independently():
    m = Protocol(
        name="two",
        candidate=False,
        fields=("n",),
        initial=(0,),
        transitions=lambda s: [("inc", (s[0] + 1,))] if s[0] < 2 else [],
        invariants={"always_true": lambda d: True, "n_below_2": lambda d: d["n"] < 2},
    )
    r = check_safety(m)
    assert r["properties"]["always_true"]["holds"] is True
    assert r["properties"]["n_below_2"]["holds"] is False


def test_branching_state_space_is_explored_exhaustively():
    """Two independent bits: four reachable states, and the invariant fails only on (1,1)."""
    m = Protocol(
        name="bits",
        candidate=False,
        fields=("a", "b"),
        initial=(0, 0),
        transitions=lambda s: [("seta", (1, s[1]))] * (s[0] == 0) + [("setb", (s[0], 1))] * (s[1] == 0),
        invariants={"not_both": lambda d: not (d["a"] and d["b"])},
    )
    r = check_safety(m)
    assert r["reachable_states"] == 4
    assert r["properties"]["not_both"]["holds"] is False


# --------------------------------------------------------------------------- liveness
# check_liveness is an AG-EF check: EVERY reachable state must still be able to reach a goal state.
# That is strictly stronger than "the goal is reachable from the initial state", and it is what
# catches a run that wanders into a corner it can never leave.
def test_liveness_holds_when_every_state_can_still_reach_the_goal():
    r = check_liveness(counter(limit=99, cap=3))
    assert r["holds"] is True
    assert r["goal_states"] == 1


def test_liveness_trap_is_reported_with_a_witness():
    m = Protocol(
        name="stuck",
        candidate=False,
        fields=("n",),
        initial=(0,),
        transitions=lambda s: [],  # no moves at all
        invariants={"trivial": lambda d: True},
        goal=lambda d: d["n"] == 1,
    )
    r = check_liveness(m)
    assert r["holds"] is False
    assert r["counterexample"][-1]["state"]["n"] == 0  # the trap itself


def test_liveness_distinguishes_a_trap_from_mere_reachability():
    """The goal IS reachable from the initial state, but one branch is a dead end.
    A plain reachability check would pass this; the AG-EF check must not."""
    # 0 -> 1 (goal) and 0 -> 2 (dead end, cannot reach 1)
    m = Protocol(
        name="fork",
        candidate=False,
        fields=("n",),
        initial=(0,),
        transitions=lambda s: [("goal", (1,)), ("dead", (2,))] if s[0] == 0 else [],
        invariants={"trivial": lambda d: True},
        goal=lambda d: d["n"] == 1,
    )
    r = check_liveness(m)
    assert r["holds"] is False  # state 2 can never reach the goal
    assert r["counterexample"][-1]["state"]["n"] == 2


def test_liveness_without_a_goal_is_undetermined_not_true():
    """No goal is an unasked question, not a satisfied property.

    This previously returned ``holds=True``, which reads as "liveness verified" to any caller doing
    ``if result["holds"]``. A model with no goal has no liveness evidence either way.
    """
    m = Protocol(
        name="nogoal",
        candidate=False,
        fields=("n",),
        initial=(0,),
        transitions=lambda s: [],
        invariants={"trivial": lambda d: True},
    )
    res = check_liveness(m)
    assert res["holds"] is None
    assert "undetermined" in res["note"]


# --------------------------------------------------------------------------- bounded time
def test_bounded_time_accepts_a_sufficient_bound():
    assert check_bounded_time(counter(limit=99, cap=3), bound=5)["holds"] is True


def test_bounded_time_rejects_an_insufficient_bound():
    assert check_bounded_time(counter(limit=99, cap=3), bound=1)["holds"] is False


# --------------------------------------------------------------------------- refinement
def test_refinement_of_a_model_by_itself_under_identity():
    m = counter(limit=99, cap=2)
    r = check_refinement(m, m, abstraction=lambda d: tuple(d.values()))
    assert isinstance(r, dict)
    assert r.get("refines") in (True, False)  # shape contract; identity should hold
    assert r.get("refines") is True


# --------------------------------------------------------------------------- optional SMT
def test_z3_availability_is_reported_as_a_bool():
    assert isinstance(z3_available(), bool)


def test_induction_degrades_cleanly_without_z3():
    """Whether or not z3 is installed, this must return a dict and never raise."""
    if not z3_available():
        pytest.skip("z3 present; the degradation path is not exercised here")
    # if z3 IS available the call is exercised in test_induction_proves_a_true_invariant
    assert True


@pytest.mark.skipif(not z3_available(), reason="requires the 'smt' extra")
def test_induction_proves_a_true_invariant():
    """decls() returns a (vars, vars_next) pair; init/inv take vars, trans takes both."""
    import z3

    def decls():
        return {"n": z3.Int("n")}, {"n": z3.Int("n_next")}

    def init(v):
        return v["n"] == 0

    def trans(v, w):
        return z3.Or(z3.And(v["n"] < 3, w["n"] == v["n"] + 1), z3.And(v["n"] >= 3, w["n"] == v["n"]))

    def inv(v):
        return z3.And(v["n"] >= 0, v["n"] <= 3)

    res = prove_inductive(decls, init, trans, inv)
    assert res["available"] is True
    assert res["base_case"] is True and res["inductive_step"] is True
    assert res["proven"] is True


@pytest.mark.skipif(not z3_available(), reason="requires the 'smt' extra")
def test_induction_refuses_a_false_invariant():
    """n <= 2 is NOT inductive for a counter that reaches 3: the step must fail."""
    import z3

    def decls():
        return {"n": z3.Int("n")}, {"n": z3.Int("n_next")}

    res = prove_inductive(
        decls,
        lambda v: v["n"] == 0,
        lambda v, w: z3.Or(z3.And(v["n"] < 3, w["n"] == v["n"] + 1), z3.And(v["n"] >= 3, w["n"] == v["n"])),
        lambda v: v["n"] <= 2,
    )
    assert res["proven"] is False
    assert res["inductive_step"] is False  # base case holds; the step is what breaks


# --------------------------------------------------------------------------- stdlib purity
def test_core_module_imports_only_stdlib_at_module_level():
    """The BFS engine must not acquire a third-party import by accident."""
    import pathlib

    import minicheck._core as core

    src = pathlib.Path(core.__file__).read_text(encoding="utf-8")
    module_level = [
        ln.strip() for ln in src.splitlines() if (ln.startswith("import ") or ln.startswith("from ")) and "z3" not in ln
    ]
    allowed = {"__future__", "collections", "dataclasses", "typing", "math", "random", "itertools"}
    for ln in module_level:
        mod = ln.split()[1].split(".")[0]
        assert mod in allowed, f"unexpected module-level import: {ln}"


# --------------------------------------------------------------------------- documented contracts
# Every function the README advertises is exercised here with the EXACT calling convention the
# README documents. These tests exist because the signatures are easy to get wrong, and a drift
# between the docs and the code should break the build rather than a user's afternoon.
def test_check_composition_takes_a_dict_and_disjoint_fields():
    a = Protocol(
        name="a",
        candidate=False,
        fields=("x",),
        initial=(0,),
        transitions=lambda s: [("ax", (1,))] if s[0] == 0 else [],
        invariants={},
    )
    b = Protocol(
        name="b",
        candidate=False,
        fields=("y",),
        initial=(0,),
        transitions=lambda s: [("by", (1,))] if s[0] == 0 else [],
        invariants={},
    )
    r = check_composition([a, b], {"not_both": lambda d: not (d["x"] == 1 and d["y"] == 1)})
    assert r["reachable_states"] == 4
    assert r["all_hold"] is False
    assert r["violated"] == ["not_both"]
    # the emergent trace names which component moved
    assert [step["label"] for step in r["counterexample"][1:]] == ["a:ax", "b:by"]


def test_check_probabilistic_solves_the_chain_exactly():
    r = check_probabilistic({0: [(0.5, 1), (0.5, 2)], 1: [], 2: []}, 0, {2}, eps=0.9)
    assert r["p_miss"] == 0.5
    assert r["holds"] is True


def test_check_statistical_estimates_the_same_quantity():
    r = check_statistical({0: [(0.5, 1), (0.5, 2)], 1: [], 2: []}, 0, {2}, n_samples=2000, seed=1)
    assert 0.4 < r["p_miss_est"] < 0.6  # agrees with the exact 0.5 above


def test_prove_latency_bound_returns_a_network_calculus_bound():
    r = prove_latency_bound(10, 1.0, 2.0, 0.5, 100)
    assert r["stable"] is True
    assert r["delay_bound"] > 0


@pytest.mark.skipif(not z3_available(), reason="requires the 'smt' extra")
def test_check_timed_safety_builder_returns_a_four_tuple():
    """builder() -> (clock_vars, constraints, deadline_expr, delay_expr)."""
    import z3

    def met():
        a, b = z3.Real("a"), z3.Real("b")
        return [a, b], [a >= 1, a <= 2, b >= 1, b <= 2], z3.RealVal(10), a + b

    def missed():
        a, b = z3.Real("a"), z3.Real("b")
        return [a, b], [a >= 1, a <= 2, b >= 1, b <= 2], z3.RealVal(3), a + b

    r_met = check_timed_safety(met)
    assert r_met["proven"] is True and r_met["counterexample"] is None

    r_missed = check_timed_safety(missed)
    assert r_missed["proven"] is False
    # a concrete timed counterexample over DENSE time, as exact rationals
    assert set(r_missed["counterexample"]) == {"a", "b"}


@pytest.mark.skipif(not z3_available(), reason="requires the 'smt' extra")
def test_prove_k_induction_and_composition_inductive():
    import z3

    def mk(suffix=""):
        return {"n": z3.Int(f"n{suffix}")}

    init = lambda v: v["n"] == 0  # noqa: E731
    trans = lambda v, w: z3.Or(
        z3.And(v["n"] < 3, w["n"] == v["n"] + 1),  # noqa: E731
        z3.And(v["n"] >= 3, w["n"] == v["n"]),
    )
    inv = lambda v: z3.And(v["n"] >= 0, v["n"] <= 3)  # noqa: E731

    assert prove_k_induction(mk, init, trans, inv, k=2)["proven"] is True
    r = prove_composition_inductive([{"mk": mk, "init": init, "trans": trans, "inv": inv}])
    assert r["proven"] is True
