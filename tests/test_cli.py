"""Tests for the command line.

The exit codes are the contract — this is meant to run in CI, so what the shell sees matters more
than what the text says. The one that needs guarding hardest is **3**: an undetermined search must
not exit 0, because a gate that treats "I could not tell" as success is the failure this package
exists to prevent.
"""

from __future__ import annotations

import json

import pytest

from minicheck.cli import EXIT_BAD_SPEC, EXIT_PROVED, EXIT_REFUTED, EXIT_UNDETERMINED, main

SAFE = {
    "fields": ["a", "b", "lock"],
    "initial": {"a": 0, "b": 0, "lock": 0},
    "transitions": [
        {"label": "a_enter", "when": {"a": 0, "lock": 0}, "set": {"a": 1, "lock": 1}},
        {"label": "b_enter", "when": {"b": 0, "lock": 0}, "set": {"b": 1, "lock": 1}},
    ],
    "invariants": {"not_both": {"forbid": {"a": 1, "b": 1}}},
}

BROKEN = {
    **SAFE,
    "transitions": [
        {"label": "a_enter", "when": {"a": 0}, "set": {"a": 1}},
        {"label": "b_enter", "when": {"b": 0}, "set": {"b": 1}},
    ],
}

UNBOUNDED = {
    "fields": ["c"],
    "initial": {"c": 0},
    "transitions": [{"label": "inc", "set": {"c": {"incr": 1}}}],
    "invariants": {"never_neg": {"forbid": {"c": -5}}},
}


def write(tmp_path, spec, name="spec.json"):
    p = tmp_path / name
    p.write_text(json.dumps(spec), encoding="utf-8")
    return str(p)


# ------------------------------------------------------------------------------ the exit contract
def test_a_safe_spec_exits_zero(tmp_path, capsys):
    assert main(["check", write(tmp_path, SAFE)]) == EXIT_PROVED
    assert "PROVED" in capsys.readouterr().out


def test_a_violated_spec_exits_two_and_prints_the_trace(tmp_path, capsys):
    assert main(["check", write(tmp_path, BROKEN)]) == EXIT_REFUTED
    out = capsys.readouterr().out
    assert "REFUTED" in out
    assert "a_enter" in out and "b_enter" in out


def test_an_undetermined_search_exits_three_not_zero(tmp_path, capsys):
    """The load-bearing case. 'I could not tell' must not read as success to a CI gate."""
    assert main(["check", write(tmp_path, UNBOUNDED)]) == EXIT_UNDETERMINED
    out = capsys.readouterr().out
    assert "UNDETERMINED" in out
    assert "not a pass" in out


def test_allow_undetermined_is_an_explicit_opt_in(tmp_path):
    path = write(tmp_path, UNBOUNDED)
    assert main(["check", path]) == EXIT_UNDETERMINED
    assert main(["check", path, "--allow-undetermined"]) == EXIT_PROVED


def test_a_refutation_still_fails_even_with_allow_undetermined(tmp_path):
    """The opt-out must widen only the undetermined case, never mask a real counterexample."""
    assert main(["check", write(tmp_path, BROKEN), "--allow-undetermined"]) == EXIT_REFUTED


@pytest.mark.parametrize(
    "spec",
    [
        {},
        {"fields": []},
        {"fields": ["a"], "initial": {"b": 0}, "transitions": [{"set": {"a": 1}}]},
        {"fields": ["a", "a"], "initial": {"a": 0}, "transitions": [{"set": {"a": 1}}]},
        {"fields": ["a"], "initial": {"a": 0}, "transitions": []},
    ],
)
def test_a_malformed_spec_exits_four(tmp_path, spec):
    assert main(["check", write(tmp_path, spec)]) == EXIT_BAD_SPEC


def test_a_spec_with_nothing_to_check_exits_four(tmp_path, capsys):
    """No invariants and no goal is a user error, not a pass."""
    spec = {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {"a": 1}}]}
    assert main(["check", write(tmp_path, spec)]) == EXIT_BAD_SPEC
    assert "nothing to check" in capsys.readouterr().err


# ------------------------------------------------------------- errors name the fix, not the fault
def test_a_missing_file_says_how_to_make_one(capsys):
    assert main(["check", "/nonexistent/nope.json"]) == EXIT_BAD_SPEC
    err = capsys.readouterr().err
    assert "no such file" in err
    assert "minicheck example" in err


def test_malformed_json_points_at_the_line(tmp_path, capsys):
    p = tmp_path / "bad.json"
    p.write_text('{"fields": ["a",]}', encoding="utf-8")
    assert main(["check", str(p)]) == EXIT_BAD_SPEC
    err = capsys.readouterr().err
    assert "not valid JSON" in err
    assert "line 1" in err
    assert "Trailing commas" in err


def test_a_field_mismatch_lists_what_is_missing(tmp_path, capsys):
    spec = {"fields": ["a", "b"], "initial": {"a": 0}, "transitions": [{"set": {"a": 1}}]}
    assert main(["check", write(tmp_path, spec)]) == EXIT_BAD_SPEC
    err = capsys.readouterr().err
    assert "missing ['b']" in err


# --------------------------------------------------------------------------------- output formats
def test_json_output_is_valid_json_and_carries_the_verdict(tmp_path, capsys):
    main(["check", write(tmp_path, BROKEN), "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert payload["verdict"] == "REFUTED"
    assert payload["exhaustive"] is True
    assert payload["exit_code"] == EXIT_REFUTED
    assert payload["invariants"]["not_both"]["holds"] is False


def test_json_output_on_a_bad_spec_is_still_json(tmp_path, capsys):
    main(["check", write(tmp_path, {}), "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert payload["ok"] is False
    assert payload["verdict"] == "BAD_SPEC"


def test_json_undetermined_carries_the_reason(tmp_path, capsys):
    main(["check", write(tmp_path, UNBOUNDED), "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert payload["verdict"] == "UNDETERMINED"
    assert payload["exhaustive"] is False
    assert "int_bound" in payload["incomplete_reason"]


def test_stdin_is_accepted(tmp_path, capsys, monkeypatch):
    import io

    monkeypatch.setattr("sys.stdin", io.StringIO(json.dumps(SAFE)))
    assert main(["check", "-"]) == EXIT_PROVED
    assert "PROVED" in capsys.readouterr().out


# ------------------------------------------------------------------------------------ subcommands
def test_example_emits_a_spec_that_actually_checks(tmp_path, capsys):
    """The starting point handed to a newcomer must not itself be malformed."""
    assert main(["example"]) == EXIT_PROVED
    spec = json.loads(capsys.readouterr().out)
    assert main(["check", write(tmp_path, spec)]) == EXIT_REFUTED  # the example is the broken mutex


def test_validate_does_not_run_the_search(tmp_path, capsys):
    """validate must accept a spec whose search would not terminate."""
    assert main(["validate", write(tmp_path, UNBOUNDED)]) == EXIT_PROVED
    assert "VALID" in capsys.readouterr().out


def test_validate_rejects_a_malformed_spec(tmp_path):
    assert main(["validate", write(tmp_path, {"fields": []})]) == EXIT_BAD_SPEC


def test_validate_reports_a_trivial_invariant(tmp_path, capsys):
    spec = {
        "fields": ["x"],
        "initial": {"x": 0},
        "transitions": [{"label": "t", "when": {"x": 0}, "set": {"x": 1}}],
        "invariants": {"impossible": {"forbid": {"x": 9999}}},
    }
    main(["validate", write(tmp_path, spec)])
    assert "trivially satisfied" in capsys.readouterr().out


def test_int_bound_flag_changes_the_verdict(tmp_path):
    """A bound wide enough to contain the violation must find it."""
    spec = {
        "fields": ["c"],
        "initial": {"c": 0},
        "transitions": [{"label": "inc", "set": {"c": {"incr": 1}}}],
        "invariants": {"never_100": {"forbid": {"c": 100}}},
    }
    path = write(tmp_path, spec)
    assert main(["check", path]) == EXIT_UNDETERMINED  # default 64 never reaches 100
    assert main(["check", path, "--int-bound", "200"]) == EXIT_REFUTED


def test_max_states_flag_is_honoured(tmp_path, capsys):
    spec = {
        "fields": ["a", "b"],
        "initial": {"a": 0, "b": 0},
        "transitions": [
            {"label": "ia", "set": {"a": {"incr": 1}}},
            {"label": "ib", "set": {"b": {"incr": 1}}},
        ],
        "invariants": {"never": {"forbid": {"a": -1}}},
    }
    assert main(["check", write(tmp_path, spec), "--max-states", "50"]) == EXIT_UNDETERMINED
    assert "exhaustive        NO" in capsys.readouterr().out


def test_liveness_is_checked_when_a_goal_is_present(tmp_path, capsys):
    spec = {
        "fields": ["n"],
        "initial": {"n": 0},
        "transitions": [
            {"label": "goal", "when": {"n": 0}, "set": {"n": 1}},
            {"label": "dead", "when": {"n": 0}, "set": {"n": 2}},
        ],
        "invariants": {"trivial": {"forbid": {"n": 9}}},
        "goal": {"require": {"n": 1}},
    }
    assert main(["check", write(tmp_path, spec)]) == EXIT_REFUTED
    out = capsys.readouterr().out
    assert "liveness" in out
    assert "trap state" in out
