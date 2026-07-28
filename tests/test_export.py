"""Export must produce a model that means the same thing.

The failure mode here is specific and severe: an export that *looks* right but encodes a slightly
different machine hands you a SPIN run that verifies something you did not check. You would then
have two green results and one of them would be about the wrong system.

So the important tests in this file do not inspect the generated text. They **run SPIN on it** and
require the verdict to match minicheck's, on models where the answer is known both ways. Those tests
skip when SPIN is not installed, and CI installs it precisely so they do not skip there.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess

import pytest

from minicheck import check_safety, protocol_from_spec
from minicheck.export import ExportError, to_promela, to_tla

SPIN = shutil.which("spin")
CC = shutil.which("gcc") or shutil.which("cc")
needs_spin = pytest.mark.skipif(not (SPIN and CC), reason="requires spin and a C compiler")

BROKEN = {
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
SAFE = {
    **BROKEN,
    "transitions": [
        {"label": "a_enter", "when": {"a": 0, "lock": 0}, "set": {"a": 1, "lock": 1}},
        {"label": "b_enter", "when": {"b": 0, "lock": 0}, "set": {"b": 1, "lock": 1}},
        {"label": "a_exit", "when": {"a": 1}, "set": {"a": 0, "lock": 0}},
        {"label": "b_exit", "when": {"b": 1}, "set": {"b": 0, "lock": 0}},
    ],
}
COUNTER = {
    "name": "counter",
    "fields": ["n", "done"],
    "initial": {"n": 0, "done": 0},
    "transitions": [
        {"label": "inc", "when": {"done": 0}, "set": {"n": {"incr": 1}}},
        {"label": "stop", "when": {"done": 0}, "set": {"done": 1}},
    ],
    "invariants": {"below_5": {"forbid": {"n": 5}}},
}


def run_spin(pml: str, tmp_path) -> bool:
    """Run SPIN's exhaustive safety check. Returns True if it found NO error."""
    d = tmp_path / "spin"
    d.mkdir(exist_ok=True)
    (d / "m.pml").write_text(pml, encoding="utf-8")
    subprocess.run([SPIN, "-a", "m.pml"], cwd=d, capture_output=True, check=True)
    subprocess.run([CC, "-O1", "-o", "pan", "pan.c"], cwd=d, capture_output=True, check=True)
    out = subprocess.run(["./pan", "-a"], cwd=d, capture_output=True, text=True).stdout
    m = re.search(r"errors:\s*(\d+)", out)
    assert m, f"could not read an error count from SPIN:\n{out}"
    return int(m.group(1)) == 0


def minicheck_holds(spec) -> bool:
    res = check_safety(protocol_from_spec(spec))
    return all(p["holds"] is True for p in res["properties"].values())


# ------------------------------------------------------- the differential that actually matters
@needs_spin
@pytest.mark.parametrize("spec,name", [(BROKEN, "broken"), (SAFE, "safe"), (COUNTER, "counter")])
def test_spin_agrees_with_minicheck(spec, name, tmp_path):
    """An independent industrial model checker must reach the same verdict on the export.

    This is the test that would catch an export encoding a different machine — the one failure
    mode where two green results are worse than one red one.
    """
    ours = minicheck_holds(spec)
    theirs = run_spin(to_promela(spec), tmp_path)
    assert ours == theirs, f"{name}: minicheck says holds={ours}, SPIN says no-errors={theirs}"


@needs_spin
def test_spin_finds_the_same_counterexample_depth(tmp_path):
    """Not just *that* it fails, but that it fails the same distance in."""
    d = tmp_path / "depth"
    d.mkdir()
    (d / "m.pml").write_text(to_promela(BROKEN), encoding="utf-8")
    subprocess.run([SPIN, "-a", "m.pml"], cwd=d, capture_output=True, check=True)
    subprocess.run([CC, "-O1", "-o", "pan", "pan.c"], cwd=d, capture_output=True, check=True)
    out = subprocess.run(["./pan", "-a"], cwd=d, capture_output=True, text=True).stdout
    assert "assertion violated" in out

    res = check_safety(protocol_from_spec(BROKEN))
    ours = len(res["properties"]["not_both"]["counterexample"]) - 1
    assert ours == 2  # a_enter then b_enter
    # SPIN's depth counts its own steps; it must be in the same ballpark, not off by an order.
    m = re.search(r"depth reached (\d+)", out)
    assert m and int(m.group(1)) <= ours + 3


@needs_spin
def test_the_generated_promela_compiles_for_every_shape(tmp_path):
    for i, spec in enumerate((BROKEN, SAFE, COUNTER)):
        d = tmp_path / f"c{i}"
        d.mkdir()
        (d / "m.pml").write_text(to_promela(spec), encoding="utf-8")
        r = subprocess.run([SPIN, "-a", "m.pml"], cwd=d, capture_output=True, text=True)
        assert r.returncode == 0, f"spin -a failed:\n{r.stderr}"


# ------------------------------------------------------------------- structure, without a solver
def test_promela_declares_every_field_and_transition():
    out = to_promela(BROKEN)
    for f in BROKEN["fields"]:
        assert f"int {f} =" in out
    for t in BROKEN["transitions"]:
        assert t["label"] in out
    assert "assert(not_both)" in out


def test_promela_reimposes_the_integer_bound():
    """SPIN must explore the same bounded space, or the two tools answer different questions."""
    out = to_promela(COUNTER, int_bound=16)
    assert "<= 16" in out and ">= -16" in out


def test_tla_has_the_required_module_structure():
    out = to_tla(BROKEN)
    assert out.startswith("---------------------------- MODULE Mutex")
    assert "VARIABLES a, b, lock" in out
    assert "Init ==" in out
    assert "Next ==" in out
    assert "Spec == Init /\\ [][Next]_vars" in out
    assert out.rstrip().endswith("=" * 72)


def test_tla_marks_untouched_variables_unchanged():
    """A TLA+ action that leaves a variable unconstrained is not the same machine."""
    out = to_tla(BROKEN)
    assert "UNCHANGED <<b>>" in out


def test_tla_names_every_action_in_next():
    out = to_tla(BROKEN)
    next_line = next(ln for ln in out.splitlines() if ln.startswith("Next =="))
    for t in BROKEN["transitions"]:
        assert t["label"] in next_line


def test_tla_bounds_the_variables_in_typeok():
    out = to_tla(COUNTER, int_bound=8)
    assert "-8..8" in out


# ------------------------------------------------------------------------------- what it refuses
def test_a_non_integer_field_is_refused_rather_than_mapped():
    """Silently numbering strings would produce counterexamples that do not match yours."""
    spec = {
        "fields": ["s"],
        "initial": {"s": "idle"},
        "transitions": [{"label": "t", "when": {"s": "idle"}, "set": {"s": "busy"}}],
        "invariants": {"i": {"forbid": {"s": "busy"}}},
    }
    with pytest.raises(ExportError, match="non-integer"):
        to_promela(spec)
    with pytest.raises(ExportError, match="non-integer"):
        to_tla(spec)


def test_a_malformed_spec_is_refused_before_export():
    from minicheck import SpecError

    with pytest.raises(SpecError):
        to_promela({"fields": []})


def test_field_names_that_are_not_identifiers_are_sanitised():
    spec = {
        "fields": ["a-b", "9x"],
        "initial": {"a-b": 0, "9x": 0},
        "transitions": [{"label": "t", "when": {"a-b": 0}, "set": {"9x": 1}}],
        "invariants": {"i": {"forbid": {"9x": 5}}},
    }
    out = to_promela(spec)
    assert "int a_b" in out
    assert "int f_9x" in out


@needs_spin
def test_a_sanitised_model_still_compiles(tmp_path):
    spec = {
        "fields": ["a-b", "9x"],
        "initial": {"a-b": 0, "9x": 0},
        "transitions": [{"label": "go", "when": {"a-b": 0}, "set": {"9x": 1}}],
        "invariants": {"i": {"forbid": {"9x": 5}}},
    }
    d = tmp_path / "san"
    d.mkdir()
    (d / "m.pml").write_text(to_promela(spec), encoding="utf-8")
    r = subprocess.run([SPIN, "-a", "m.pml"], cwd=d, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr


def test_spin_availability_is_reported_not_hidden():
    """If these tests skip everywhere, the export is only eyeballed. Make that visible."""
    if not SPIN:
        pytest.skip("spin is not installed here; CI installs it so the differential really runs")
    assert os.path.exists(SPIN)
