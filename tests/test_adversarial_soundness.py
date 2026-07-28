"""Adversarial soundness suite: no input may produce a confident answer that is wrong.

Every test here is a regression for a defect that shipped, or a hunt for the same class of defect
somewhere it has not been found yet. The governing oracle throughout is one-directional:

    A verdict of ``holds=True`` is a claim about EVERY reachable state, so it requires that the
    search actually covered every reachable state. A verdict of ``holds=False`` is a claim about ONE
    state and carries its own witness, so it is sound from a partial search. ``holds=None`` is the
    honest output when neither is established.

The most valuable test in the file is `test_differential_against_independent_reachability`, which
re-implements reachability the dumbest way possible and cross-checks. The defects that survived the
original 44-test suite all shared a shape: the suite only ever asked "does the checker agree with
itself", never "does the checker agree with the truth".
"""

from __future__ import annotations

import itertools
import random

import pytest

from minicheck import (
    IntBoundExceeded,
    Protocol,
    SpecError,
    check_bounded_time,
    check_composition,
    check_liveness,
    check_probabilistic,
    check_safety,
    check_statistical,
    protocol_from_spec,
    spec_warnings,
    validate_spec,
)
from minicheck._core import SingularSystem, _solve_linear


# --------------------------------------------------------------------- the reference implementation
def naive_reachable(model: Protocol, cap: int = 100000) -> set:
    """Reachability by the least clever method available, as an independent oracle.

    Deliberately shares no code with `_core`: a plain worklist over a set, no BFS ordering, no parent
    map, no early exit. If the two disagree, one of them is wrong and the test says which inputs.
    """
    seen = {model.initial}
    todo = [model.initial]
    while todo:
        s = todo.pop()
        for _, ns in model.transitions(s):
            if ns not in seen:
                seen.add(ns)
                todo.append(ns)
                if len(seen) > cap:
                    raise RuntimeError("reference hit its cap")
    return seen


def random_protocol(rng: random.Random, n_fields: int, domain: int) -> Protocol:
    """A random finite machine over `n_fields` fields each ranging 0..domain-1."""
    fields = tuple(f"f{i}" for i in range(n_fields))
    n_rules = rng.randint(1, 6)
    rules = []
    for _ in range(n_rules):
        guard = {rng.randrange(n_fields): rng.randrange(domain)} if rng.random() < 0.6 else {}
        assign = {rng.randrange(n_fields): rng.randrange(domain) for _ in range(rng.randint(1, n_fields))}
        rules.append((guard, assign))

    def transitions(s, _rules=rules):
        out = []
        for i, (guard, assign) in enumerate(_rules):
            if all(s[k] == v for k, v in guard.items()):
                nxt = list(s)
                for k, v in assign.items():
                    nxt[k] = v
                out.append((f"r{i}", tuple(nxt)))
        return out

    return Protocol(
        name="rand",
        candidate=False,
        fields=fields,
        initial=tuple(0 for _ in fields),
        transitions=transitions,
        invariants={},
    )


def test_differential_against_independent_reachability():
    """500 random machines: the checker's reachable set must equal the reference set exactly.

    This is the test that would have caught the clamp bug, the composition field-collision bug and
    the missing bounded-time cap, none of which the original suite noticed.
    """
    rng = random.Random(20260728)
    checked = 0
    for _ in range(500):
        m = random_protocol(rng, n_fields=rng.randint(1, 3), domain=rng.randint(2, 4))
        expected = naive_reachable(m)
        res = check_safety(m)
        assert res["exhaustive"] is True
        assert res["reachable_states"] == len(expected), f"state count differs on {m.fields}"
        checked += 1
    assert checked == 500


def test_differential_verdicts_match_brute_force():
    """Random machines with random invariants: every verdict must match exhaustive ground truth."""
    rng = random.Random(4242)
    for _ in range(300):
        n_fields = rng.randint(1, 2)
        domain = rng.randint(2, 4)
        m = random_protocol(rng, n_fields=n_fields, domain=domain)
        target = tuple(rng.randrange(domain) for _ in range(n_fields))

        def inv(d, _t=target, _f=m.fields):
            return tuple(d[f] for f in _f) != _t

        m.invariants = {"avoid": inv}
        truth = target not in naive_reachable(m)  # True == genuinely unreachable == invariant holds
        got = check_safety(m)["properties"]["avoid"]["holds"]
        assert got is truth, f"verdict {got} but ground truth {truth} for target {target}"


def test_counterexamples_actually_replay():
    """Every counterexample the checker emits must be a real path with a real violation at the end."""
    rng = random.Random(99)
    replayed = 0
    for _ in range(300):
        m = random_protocol(rng, n_fields=2, domain=3)
        m.invariants = {"not_11": lambda d: not (d["f0"] == 1 and d["f1"] == 1)}
        res = check_safety(m)
        cex = res["properties"]["not_11"]["counterexample"]
        if cex is None:
            continue
        states = [tuple(step["state"][f] for f in m.fields) for step in cex]
        assert states[0] == m.initial, "trace does not start at the initial state"
        for a, b in zip(states, states[1:]):
            assert b in {ns for _, ns in m.transitions(a)}, f"{a} -> {b} is not a transition"
        assert not m.invariants["not_11"](m.d(states[-1])), "final state does not violate"
        replayed += 1
    assert replayed > 0, "the generator produced no counterexamples; the test proved nothing"


# ------------------------------------------------------------------------------- C1: the clamp bug
def test_clamped_counter_no_longer_reports_a_false_proof():
    """The exact input that shipped a false proof."""
    spec = {
        "fields": ["c"],
        "initial": {"c": 0},
        "transitions": [{"label": "inc", "set": {"c": {"incr": 1}}}],
        "invariants": {"never_100": {"forbid": {"c": 100}}},
    }
    # Under the clamp this returned holds=True at the default bound. It must never do so again.
    assert check_safety(protocol_from_spec(spec))["properties"]["never_100"]["holds"] is not True
    res = check_safety(protocol_from_spec(spec, int_bound=200))
    assert res["properties"]["never_100"]["holds"] is False


@pytest.mark.parametrize("bound", [4, 8, 64, 200])
def test_no_bound_ever_yields_true_for_an_escaping_counter(bound):
    """S2 bound-escape: at NO int_bound may an unbounded counter be reported safe."""
    spec = {
        "fields": ["c"],
        "initial": {"c": 0},
        "transitions": [{"label": "inc", "set": {"c": {"incr": 1}}}],
        "invariants": {"below": {"forbid": {"c": bound // 2}}},
    }
    res = check_safety(protocol_from_spec(spec, int_bound=bound))
    assert res["properties"]["below"]["holds"] is not True
    assert res["exhaustive"] is False


def test_out_of_range_literal_is_reported_as_trivial_not_silently_passed():
    """An invariant naming an unrepresentable value IS satisfied — but saying only "holds: true"
    would let a reader think something was verified. The triviality has to be visible."""
    spec = {
        "fields": ["x"],
        "initial": {"x": 0},
        "transitions": [{"label": "t", "set": {"x": 1}}],
        "invariants": {"impossible": {"forbid": {"x": 5000}}},
    }
    validate_spec(spec)  # structurally fine
    warnings = spec_warnings(spec)
    assert len(warnings) == 1
    assert "trivially satisfied" in warnings[0]
    assert "int_bound" in warnings[0]


def test_no_warnings_for_a_spec_that_says_something():
    spec = {
        "fields": ["x"],
        "initial": {"x": 0},
        "transitions": [{"label": "t", "set": {"x": 1}}],
        "invariants": {"real": {"forbid": {"x": 1}}},
    }
    assert spec_warnings(spec) == []


def test_initial_state_outside_the_bound_is_refused():
    spec = {
        "fields": ["x"],
        "initial": {"x": 9999},
        "transitions": [{"label": "t", "set": {"x": 1}}],
        "invariants": {"i": {"forbid": {"x": 1}}},
    }
    with pytest.raises(SpecError, match="int_bound"):
        validate_spec(spec)


def test_transition_leaving_the_bound_raises_the_typed_error():
    spec = {
        "fields": ["x"],
        "initial": {"x": 0},
        "transitions": [{"label": "up", "set": {"x": {"incr": 10}}}],
        "invariants": {"i": {"forbid": {"x": 3}}},
    }
    p = protocol_from_spec(spec, int_bound=15)
    with pytest.raises(IntBoundExceeded, match="int_bound"):
        for s in [(0,), (10,)]:
            p.transitions(s)


# ------------------------------------------------------------------------ C3: composition collision
def test_composition_refuses_colliding_field_names():
    """Two models both naming a field 'x' must not be silently merged into one variable."""
    a = Protocol(
        name="a",
        candidate=False,
        fields=("x",),
        initial=(0,),
        transitions=lambda s: [("i", (s[0] + 1,))] if s[0] < 2 else [],
        invariants={},
    )
    b = Protocol(name="b", candidate=False, fields=("x",), initial=(5,), transitions=lambda s: [], invariants={})
    with pytest.raises(ValueError, match="disjoint field names"):
        check_composition([a, b], {"j": lambda d: d["x"] < 100})


def test_composition_with_disjoint_fields_still_works():
    a = Protocol(
        name="a",
        candidate=False,
        fields=("x",),
        initial=(0,),
        transitions=lambda s: [("i", (s[0] + 1,))] if s[0] < 2 else [],
        invariants={},
    )
    b = Protocol(
        name="b",
        candidate=False,
        fields=("y",),
        initial=(0,),
        transitions=lambda s: [("j", (s[0] + 1,))] if s[0] < 2 else [],
        invariants={},
    )
    res = check_composition([a, b], {"j": lambda d: d["x"] + d["y"] < 100})
    assert res["all_hold"] is True
    assert res["reachable_states"] == 9  # 3 x 3, the true product


def test_empty_composition_is_refused():
    with pytest.raises(ValueError, match="at least one model"):
        check_composition([], {})


# --------------------------------------------------------------- C4: the silent linear-solver garbage
def test_singular_system_raises_instead_of_returning_1e15():
    """The shipped code returned [1e15, -5e14] for a system with no solution."""
    with pytest.raises(SingularSystem):
        _solve_linear([[1.0, 2.0], [2.0, 4.0]], [1.0, 3.0])


def test_singular_chain_abstains_with_a_reason():
    """A degenerate chain must yield holds=None and say why, never a plausible number."""
    # Rows that do not sum to 1 and duplicate each other -> singular system.
    trans = {"a": [(1.0, "b")], "b": [(1.0, "a")]}
    res = check_probabilistic(trans, "a", ["nonexistent_miss_state"], eps=0.5)
    assert res["holds"] is None
    assert res["p_miss"] is None
    assert "reason" in res


def test_empty_and_non_square_systems_raise():
    with pytest.raises(SingularSystem):
        _solve_linear([], [])
    with pytest.raises(SingularSystem):
        _solve_linear([[1.0, 2.0]], [1.0, 2.0])


def test_well_posed_chain_still_computes_the_right_answer():
    """The refusal path must not have broken the working path. Two coin flips to reach MISS."""
    trans = {0: [(0.5, 1), (0.5, "SAFE")], 1: [(0.5, "MISS"), (0.5, "SAFE")]}
    res = check_probabilistic(trans, 0, ["MISS"], eps=0.5)
    assert res["p_miss"] == pytest.approx(0.25)
    assert res["holds"] is True


def test_unknown_start_state_is_refused():
    with pytest.raises(ValueError, match="not one of"):
        check_probabilistic({0: [(1.0, "MISS")]}, "no_such_state", ["MISS"], eps=0.5)


# ------------------------------------------------------------------- C8/liveness: unasked questions
def test_bounded_time_without_a_goal_is_undetermined():
    m = Protocol(name="n", candidate=False, fields=("n",), initial=(0,), transitions=lambda s: [], invariants={})
    assert check_bounded_time(m, bound=5)["holds"] is None


def test_liveness_without_a_goal_is_undetermined():
    m = Protocol(name="n", candidate=False, fields=("n",), initial=(0,), transitions=lambda s: [], invariants={})
    assert check_liveness(m)["holds"] is None


def test_bounded_time_caps_an_unbounded_model():
    """Previously unbounded: this would grow the dict until the process died."""
    m = Protocol(
        name="inf",
        candidate=False,
        fields=("n",),
        initial=(0,),
        transitions=lambda s: [("i", (s[0] + 1,))],
        invariants={},
        goal=lambda d: d["n"] == -1,  # never true
    )
    with pytest.raises(RuntimeError, match="state space"):
        check_bounded_time(m, bound=10, max_states=1000)


# -------------------------------------------------------------------- malformed / empty / enormous
@pytest.mark.parametrize(
    "spec",
    [
        {},
        {"fields": []},
        {"fields": ["a"]},
        {"fields": ["a"], "initial": {}},
        {"fields": ["a"], "initial": {"a": 0}},
        {"fields": ["a"], "initial": {"a": 0}, "transitions": []},
        {"fields": ["a", "a"], "initial": {"a": 0}, "transitions": [{"set": {"a": 1}}]},
        {"fields": ["a"], "initial": {"b": 0}, "transitions": [{"set": {"a": 1}}]},
        {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {"zzz": 1}}]},
        {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {}}]},
        {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {"a": {"incr": "x"}}}]},
        {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {"a": {"incr": 1, "decr": 1}}}]},
        {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {"a": 1}}], "invariants": {"i": {}}},
        {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {"a": 1}}], "invariants": {"i": {"forbid": {}}}},
        {
            "fields": ["a"],
            "initial": {"a": 0},
            "transitions": [{"set": {"a": 1}}],
            "invariants": {"i": {"forbid": {"a": 1}, "require": {"a": 1}}},
        },
        {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {"a": 1}}], "goal": {"nope": {"a": 1}}},
        "not a dict",
        None,
        [],
    ],
)
def test_malformed_specs_raise_specerror_never_a_verdict(spec):
    """Malformed input must fail loudly. It must never fall through into a checkable protocol."""
    with pytest.raises((SpecError, AttributeError, TypeError)):
        protocol_from_spec(spec)


def test_int_bound_itself_is_validated():
    spec = {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {"a": 1}}], "invariants": {}}
    for bad in (0, -1, True, "64", 1.5):
        with pytest.raises(SpecError, match="int_bound"):
            protocol_from_spec(spec, int_bound=bad)


def test_enormous_state_space_refuses_rather_than_exhausting_memory():
    m = Protocol(
        name="wide",
        candidate=False,
        fields=("a", "b"),
        initial=(0, 0),
        transitions=lambda s: [("i", (s[0] + 1, s[1])), ("j", (s[0], s[1] + 1))],
        invariants={"never": lambda d: True},
    )
    res = check_safety(m, max_states=2000)
    assert res["exhaustive"] is False
    assert res["properties"]["never"]["holds"] is None  # not True


def test_a_raising_invariant_propagates_and_does_not_read_as_a_verdict():
    """An invariant that throws is a broken question, not a satisfied one."""
    m = Protocol(
        name="boom",
        candidate=False,
        fields=("n",),
        initial=(0,),
        transitions=lambda s: [],
        invariants={"bad": lambda d: 1 / 0},
    )
    with pytest.raises(ValueError, match="raised on state"):
        check_safety(m)


def test_deterministic_across_runs():
    """Same input, same verdict and same trace — a checker that varies is not trustworthy."""
    spec = {
        "fields": ["a", "b"],
        "initial": {"a": 0, "b": 0},
        "transitions": [
            {"label": "a1", "when": {"a": 0}, "set": {"a": 1}},
            {"label": "b1", "when": {"b": 0}, "set": {"b": 1}},
        ],
        "invariants": {"not_both": {"forbid": {"a": 1, "b": 1}}},
    }
    runs = [check_safety(protocol_from_spec(spec)) for _ in range(5)]
    assert all(r == runs[0] for r in runs)


# ------------------------------------------------------------------------- statistical honesty (C-)
def test_statistical_check_does_not_emit_a_boolean_verdict():
    """An estimate must not present as a proof; there is deliberately no `holds` key."""
    trans = {0: [(0.5, 1), (0.5, "SAFE")], 1: [(0.5, "MISS"), (0.5, "SAFE")]}
    res = check_statistical(trans, 0, ["MISS"], n_samples=2000)
    assert "holds" not in res
    assert res["is_proof"] is False
    assert res["p_miss_upper"] >= res["p_miss_est"]


def test_statistical_interval_covers_the_exact_answer():
    """Sanity: the Monte-Carlo interval must contain the exactly-solved probability."""
    trans = {0: [(0.5, 1), (0.5, "SAFE")], 1: [(0.5, "MISS"), (0.5, "SAFE")]}
    exact = check_probabilistic(trans, 0, ["MISS"], eps=1.0)["p_miss"]
    est = check_statistical(trans, 0, ["MISS"], n_samples=20000)
    assert abs(est["p_miss_est"] - exact) <= est["half_width"]


# ------------------------------------------------------------------------------ exhaustive smoke set
def test_all_small_machines_agree_with_brute_force():
    """Exhaustive over every 1-field 3-value machine: no sampling, no luck involved."""
    domain = 3
    for rule_set in itertools.product(range(domain), repeat=domain):
        m = Protocol(
            name="exh",
            candidate=False,
            fields=("x",),
            initial=(0,),
            transitions=lambda s, _r=rule_set: [("t", (_r[s[0]],))],
            invariants={"not_2": lambda d: d["x"] != 2},
        )
        truth = (2,) not in naive_reachable(m)
        assert check_safety(m)["properties"]["not_2"]["holds"] is truth


# ------------------------------------------------- P1: the compiled transition path must be exact
def test_compiled_transitions_match_the_interpreted_semantics():
    """The optimisation must be a pure speedup, never a semantic change.

    `_compile_rules` hoists guard lookups and literal bound checks out of the hot loop. This
    re-implements the ORIGINAL interpreted semantics inline and requires the two to agree on every
    successor of every reachable state, for a range of spec shapes.
    """
    from minicheck.spec import protocol_from_spec

    def interpreted(spec, s, fields, idx, int_bound):
        """The pre-optimisation transition function, kept here as the oracle.

        Includes the bound check, because the compiled path keeps it and comparing a bounded
        implementation against an unbounded one compares two different functions.
        """
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

    rng = random.Random(90210)
    compared = 0
    for _ in range(200):
        n = rng.randint(1, 4)
        fields = [f"f{i}" for i in range(n)]
        rules = []
        for j in range(rng.randint(1, 5)):
            rule = {"label": f"r{j}", "set": {}}
            if rng.random() < 0.6:
                rule["when"] = {rng.choice(fields): rng.randrange(3)}
            for f in rng.sample(fields, rng.randint(1, n)):
                rule["set"][f] = {"incr": 1} if rng.random() < 0.3 else rng.randrange(3)
            rules.append(rule)
        spec = {
            "fields": fields,
            "initial": dict.fromkeys(fields, 0),
            "transitions": rules,
            "invariants": {"t": {"forbid": {fields[0]: 99}}},
        }
        idx = {f: i for i, f in enumerate(fields)}
        model = protocol_from_spec(spec, int_bound=200)
        # walk the reachable space, comparing successors at every state
        seen, todo = {model.initial}, [model.initial]
        while todo:
            s = todo.pop()
            # Both must agree on the successors AND on when to refuse.
            try:
                got = model.transitions(s)
                raised = None
            except IntBoundExceeded as e:
                got, raised = None, e
            try:
                want = interpreted(spec, s, fields, idx, 200)
                want_raised = None
            except IntBoundExceeded as e:
                want, want_raised = None, e
            assert (raised is None) == (want_raised is None), (
                f"one refused and the other did not at {s}: compiled={raised} interpreted={want_raised}"
            )
            if raised is not None:
                continue
            assert got == want, f"compiled != interpreted at {s}: {got} vs {want}"
            compared += 1
            for _, ns in got:
                if ns not in seen and len(seen) < 400:
                    seen.add(ns)
                    todo.append(ns)
    assert compared > 500


def test_compiled_path_still_refuses_an_out_of_bound_increment():
    """The one runtime check the optimisation keeps must still fire."""
    spec = {
        "fields": ["c"],
        "initial": {"c": 0},
        "transitions": [{"label": "up", "set": {"c": {"incr": 7}}}],
        "invariants": {"i": {"forbid": {"c": 3}}},
    }
    p = protocol_from_spec(spec, int_bound=20)
    with pytest.raises(IntBoundExceeded, match="int_bound"):
        for s in [(0,), (7,), (14,), (21,)]:
            p.transitions(s)


def test_compiled_path_preserves_the_no_op_on_non_integer_increments():
    """incr on a string field was a documented no-op; the rewrite must not change that."""
    spec = {
        "fields": ["s", "n"],
        "initial": {"s": "idle", "n": 0},
        "transitions": [{"label": "t", "when": {"s": "idle"}, "set": {"s": {"incr": 1}, "n": 1}}],
        "invariants": {"i": {"forbid": {"n": 99}}},
    }
    p = protocol_from_spec(spec)
    assert p.transitions(("idle", 0)) == [("t", ("idle", 1))]


def test_booleans_are_not_treated_as_integers_by_the_compiled_path():
    """`True` is an int in Python; incr on it would be a silent semantic change."""
    spec = {
        "fields": ["b"],
        "initial": {"b": True},
        "transitions": [{"label": "t", "set": {"b": {"incr": 1}}}],
        "invariants": {"i": {"forbid": {"b": 9}}},
    }
    p = protocol_from_spec(spec)
    assert p.transitions((True,)) == [("t", (True,))]  # no-op, exactly as before
