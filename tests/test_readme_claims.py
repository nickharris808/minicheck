"""The README must not contain a number the code cannot reproduce.

Documentation drift is the quiet member of the hallucination family: a claim that was true once, is
false now, and looks exactly as authoritative either way. Two counts in the shipped READMEs were
wrong like this — one said 23 tests against an actual 44, another said 61 against 72.

So the figures are re-derived here rather than trusted. Add a test or a source file, and if the
README disagrees this fails and names the number to write.
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
README = ROOT / "README.md"


def collected_tests() -> int:
    """Ask pytest itself how many cases exist, so parametrisation is counted correctly."""
    out = subprocess.run(
        [sys.executable, "-m", "pytest", "tests", "--collect-only", "-q", "-p", "no:cacheprovider"],
        capture_output=True,
        text=True,
        cwd=ROOT,
    )
    lines = [ln for ln in out.stdout.strip().splitlines() if ln.strip()]
    match = re.match(r"(\d+)", lines[-1]) if lines else None
    assert match, f"could not read a collection count from pytest:\n{out.stdout[-2000:]}"
    return int(match.group(1))


def source_lines() -> int:
    return sum(len(p.read_text(encoding="utf-8").splitlines()) for p in sorted((ROOT / "src").rglob("*.py")))


def test_every_test_count_in_the_readme_is_the_real_one():
    actual = collected_tests()
    text = README.read_text(encoding="utf-8")

    badges = [int(m) for m in re.findall(r"tests-(\d+)", text)]
    assert badges, "README has no tests badge"
    for claimed in badges:
        assert claimed == actual, f"README badge says {claimed} tests; pytest collects {actual}"

    for claimed in [int(m) for m in re.findall(r"\b(\d+) tests\b", text)]:
        assert claimed == actual, f"README prose says {claimed} tests; pytest collects {actual}"


def test_line_count_claims_are_close_to_the_truth():
    """A "~N lines" claim about THIS package must be within 15% of its real size.

    Cross-links quote a sibling package's size, so a figure that matches no local file is only
    flagged when it is not attached to a link.
    """
    text = README.read_text(encoding="utf-8")
    actual = source_lines()
    for match in re.finditer(r"~(\d+) lines", text):
        claimed = int(match.group(1))
        if abs(claimed - actual) / max(actual, 1) <= 0.15:
            continue
        line_start = text.rfind("\n", 0, match.start()) + 1
        line = text[line_start : text.find("\n", match.start())]
        assert "](https://github.com/" in line, f"README claims ~{claimed} lines but this package has {actual}"


def test_no_placeholder_text_shipped():
    text = README.read_text(encoding="utf-8").lower()
    for marker in ("todo", "fixme", "coming soon", "lorem ipsum", "placeholder"):
        assert marker not in text, f"README still contains {marker!r}"


def test_readme_states_what_the_tool_does_not_establish():
    """Every package must carry an explicit scope section. Silence about limits reads as absence."""
    text = README.read_text(encoding="utf-8")
    assert re.search(r"^#+ .*(honest scope|limitations|what this does not)", text, re.M | re.I), (
        "README has no section stating the tool's limits"
    )


# --------------------------------------------------------------- the tutorial must be reproducible
TUTORIAL_BROKEN = {
    "name": "retry",
    "fields": ["tries", "done"],
    "initial": {"tries": 0, "done": 0},
    "transitions": [
        {"label": "attempt", "when": {"done": 0}, "set": {"tries": {"incr": 1}}},
        {"label": "succeed", "when": {"done": 0}, "set": {"done": 1}},
    ],
    "invariants": {"at_most_3": {"forbid": {"tries": 4}}},
    "goal": {"require": {"done": 1}},
}

TUTORIAL_FIXED = {
    **TUTORIAL_BROKEN,
    "transitions": [
        {"label": "attempt1", "when": {"done": 0, "tries": 0}, "set": {"tries": {"incr": 1}}},
        {"label": "attempt2", "when": {"done": 0, "tries": 1}, "set": {"tries": {"incr": 1}}},
        {"label": "attempt3", "when": {"done": 0, "tries": 2}, "set": {"tries": {"incr": 1}}},
        {"label": "succeed", "when": {"done": 0}, "set": {"done": 1}},
    ],
}


def _check(spec):
    from minicheck import check_liveness, check_safety, protocol_from_spec

    model = protocol_from_spec(spec)
    return check_safety(model), check_liveness(model)


def test_tutorial_step_2_matches_the_readme():
    """A tutorial whose output does not reproduce teaches the reader to distrust the tool."""
    res, live = _check(TUTORIAL_BROKEN)
    assert res["reachable_states"] == 129
    assert res["exhaustive"] is False
    assert res["properties"]["at_most_3"]["holds"] is False
    assert len(res["properties"]["at_most_3"]["counterexample"]) == 5  # initial + 4 attempts
    assert live["holds"] is None  # undetermined, not refuted


def test_tutorial_step_3_matches_the_readme():
    res, live = _check(TUTORIAL_FIXED)
    assert res["reachable_states"] == 8
    assert res["exhaustive"] is True
    assert res["properties"]["at_most_3"]["holds"] is True
    assert live["holds"] is True


def test_tutorial_step_4_matches_the_readme():
    spec = {**TUTORIAL_FIXED, "transitions": [t for t in TUTORIAL_FIXED["transitions"] if t["label"] != "succeed"]}
    res, live = _check(spec)
    assert res["reachable_states"] == 4
    assert res["properties"]["at_most_3"]["holds"] is True
    assert live["holds"] is False
    assert live["counterexample"][-1]["state"] == {"tries": 0, "done": 0}


def test_every_state_count_quoted_in_the_readme_is_real():
    """Scrape `states explored N` from the README and re-derive each one."""
    text = README.read_text(encoding="utf-8")
    quoted = [int(m) for m in re.findall(r"states explored\s+([0-9,]+)", text.replace(",", ""))]
    assert quoted, "no state counts found; the tutorial may have been removed"
    derived = {
        _check(TUTORIAL_BROKEN)[0]["reachable_states"],
        _check(TUTORIAL_FIXED)[0]["reachable_states"],
        6,  # the `minicheck example` mutex, broken
        3,  # the same with the lock guard
        4,  # step 4
    }
    for n in quoted:
        assert n in derived, f"README quotes 'states explored {n}', which nothing reproduces"


def test_the_speedup_claim_holds_on_every_benchmarked_workload():
    """The README's performance claim is a FLOOR, and this is what enforces it.

    A mean is not falsifiable on someone else's hardware, so the README states the floor — never
    below 2x on any benchmarked workload — and that is what is asserted. A regression that undid the
    compilation would land well under 1x and turn this red. The tiny `ring` workload is excluded
    because its runtime is at timer resolution, where the ratio is noise rather than measurement.
    """
    import sys
    from pathlib import Path

    root = Path(__file__).resolve().parents[1]
    sys.path.insert(0, str(root))
    try:
        import bench
    finally:
        sys.path.pop(0)

    for spec in bench.WORKLOADS:
        t_new, n_new = bench.timed(bench.protocol_from_spec(spec))
        t_old, n_old = bench.timed(bench.as_interpreted(spec))
        assert n_new == n_old, f"{spec['name']}: the two paths explored different spaces"
        if n_new < 1000:
            continue  # at timer resolution; the differential test covers correctness here
        assert t_old / t_new >= 2.0, (
            f"{spec['name']}: compiled is only {t_old / t_new:.2f}x the interpreted path; "
            "the README claims a floor of 2x"
        )


def test_the_readme_points_at_the_script_that_reproduces_its_numbers():
    """An unreproducible number is a claim that outruns the code."""
    from pathlib import Path

    root = Path(__file__).resolve().parents[1]
    readme = (root / "README.md").read_text(encoding="utf-8")
    assert (root / "bench.py").exists()
    assert "python bench.py" in readme
    # The superseded claim compared against a release that is not in this repository.
    assert "over 0.2.0" not in readme
