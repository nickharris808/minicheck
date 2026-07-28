"""Tests for the declarative spec loader.

This is the untrusted-input path: a spec may arrive over a network or from a language model, so the
tests care as much about what it REFUSES as about what it builds.
"""

import pytest

from minicheck import SpecError, check_liveness, check_safety, protocol_from_spec, validate_spec

MUTEX = {
    "name": "mutex",
    "fields": ["a", "b", "lock"],
    "initial": {"a": 0, "b": 0, "lock": 0},
    "transitions": [
        {"label": "a_enter", "when": {"a": 0, "lock": 0}, "set": {"a": 1, "lock": 1}},
        {"label": "b_enter", "when": {"b": 0, "lock": 0}, "set": {"b": 1, "lock": 1}},
        {"label": "a_exit", "when": {"a": 1}, "set": {"a": 0, "lock": 0}},
        {"label": "b_exit", "when": {"b": 1}, "set": {"b": 0, "lock": 0}},
    ],
    "invariants": {"not_both": {"forbid": {"a": 1, "b": 1}}},
}

BROKEN_MUTEX = {
    **MUTEX,
    "transitions": [
        {"label": "a_enter", "when": {"a": 0}, "set": {"a": 1}},  # no lock guard
        {"label": "b_enter", "when": {"b": 0}, "set": {"b": 1}},
    ],
}


# --------------------------------------------------------------------------- building
def test_a_guarded_spec_is_safe():
    r = check_safety(protocol_from_spec(MUTEX))["properties"]["not_both"]
    assert r["holds"] is True


def test_an_unguarded_spec_yields_a_labelled_counterexample():
    r = check_safety(protocol_from_spec(BROKEN_MUTEX))["properties"]["not_both"]
    assert r["holds"] is False
    assert [s["label"] for s in r["counterexample"][1:]] == ["a_enter", "b_enter"]


def test_fields_initial_and_name_survive():
    p = protocol_from_spec(MUTEX)
    assert p.fields == ("a", "b", "lock")
    assert p.initial == (0, 0, 0)
    assert p.name == "mutex"


def test_a_transition_without_a_guard_is_always_enabled():
    spec = {
        "fields": ["n"],
        "initial": {"n": 0},
        "transitions": [{"label": "bump", "set": {"n": {"incr": 1}}}],
        "invariants": {"small": {"forbid": {"n": 5}}},
    }
    r = check_safety(protocol_from_spec(spec))["properties"]["small"]
    assert r["holds"] is False  # counts up to 5


def test_incr_and_decr_move_integers():
    spec = {
        "fields": ["n"],
        "initial": {"n": 0},
        "transitions": [
            {"label": "up", "when": {"n": 0}, "set": {"n": {"incr": 3}}},
            {"label": "down", "when": {"n": 3}, "set": {"n": {"decr": 3}}},
        ],
        "invariants": {"never_two": {"forbid": {"n": 2}}},
    }
    assert check_safety(protocol_from_spec(spec))["properties"]["never_two"]["holds"] is True


def test_integers_are_clamped_so_the_space_stays_finite():
    """An unbounded counter must not produce an unbounded search."""
    spec = {
        "fields": ["n"],
        "initial": {"n": 0},
        "transitions": [{"label": "up", "set": {"n": {"incr": 1}}}],
        "invariants": {"t": {"forbid": {"n": -999}}},
    }
    res = check_safety(protocol_from_spec(spec, int_bound=8))
    assert res["reachable_states"] == 9  # 0..8 inclusive, then clamped


def test_require_and_forbid_are_duals():
    base = {"fields": ["x"], "initial": {"x": 0}, "transitions": [{"label": "set1", "when": {"x": 0}, "set": {"x": 1}}]}
    forbid = check_safety(protocol_from_spec({**base, "invariants": {"c": {"forbid": {"x": 1}}}}))
    require = check_safety(protocol_from_spec({**base, "invariants": {"c": {"require": {"x": 0}}}}))
    assert forbid["properties"]["c"]["holds"] is False
    assert require["properties"]["c"]["holds"] is False


def test_goal_drives_liveness():
    spec = {**MUTEX, "goal": {"require": {"a": 1}}}
    assert isinstance(check_liveness(protocol_from_spec(spec))["holds"], bool)


# --------------------------------------------------------------------------- refusing bad input
@pytest.mark.parametrize(
    "bad,msg",
    [
        ({}, "fields"),
        ({"fields": [], "initial": {}, "transitions": []}, "non-empty"),
        ({"fields": ["a", "a"], "initial": {"a": 0}, "transitions": [{"set": {"a": 1}}]}, "unique"),
        ({"fields": ["a"], "initial": {}, "transitions": [{"set": {"a": 1}}]}, "exactly the declared"),
        ({"fields": ["a"], "initial": {"a": 0}, "transitions": []}, "non-empty"),
        ({"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {"zz": 1}}]}, "unknown fields"),
        (
            {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"when": {"zz": 1}, "set": {"a": 1}}]},
            "unknown fields",
        ),
        ({"fields": ["a"], "initial": {"a": 0}, "transitions": [{"label": "x"}]}, "'set' is required"),
    ],
)
def test_malformed_specs_are_refused_with_a_useful_message(bad, msg):
    with pytest.raises(SpecError) as e:
        protocol_from_spec(bad)
    assert msg in str(e.value)


def test_an_invariant_naming_an_unknown_field_is_refused():
    spec = {
        "fields": ["a"],
        "initial": {"a": 0},
        "transitions": [{"set": {"a": 1}}],
        "invariants": {"bad": {"forbid": {"nope": 1}}},
    }
    with pytest.raises(SpecError) as e:
        protocol_from_spec(spec)
    assert "unknown fields" in str(e.value)


def test_a_condition_with_both_forbid_and_require_is_refused():
    spec = {
        "fields": ["a"],
        "initial": {"a": 0},
        "transitions": [{"set": {"a": 1}}],
        "invariants": {"bad": {"forbid": {"a": 1}, "require": {"a": 0}}},
    }
    with pytest.raises(SpecError):
        protocol_from_spec(spec)


def test_a_bad_incr_amount_is_refused():
    spec = {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {"a": {"incr": "lots"}}}]}
    with pytest.raises(SpecError) as e:
        protocol_from_spec(spec)
    assert "integer" in str(e.value)


def test_no_code_is_executed_from_a_spec():
    """The whole point: a spec is data. Strings that look like code stay strings."""
    spec = {
        "fields": ["a"],
        "initial": {"a": "__import__('os').system('echo pwned')"},
        "transitions": [{"label": "t", "set": {"a": "still just a string"}}],
        "invariants": {"c": {"forbid": {"a": "never"}}},
    }
    res = check_safety(protocol_from_spec(spec))
    assert res["properties"]["c"]["holds"] is True
    assert res["reachable_states"] == 2


def test_validate_spec_returns_none_on_a_good_spec():
    assert validate_spec(MUTEX) is None
