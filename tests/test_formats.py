"""The output formats must carry the verdict faithfully into every destination.

The risk with a new emitter is not that it crashes — it is that it renders UNDETERMINED as something
a dashboard shows in green. Each format below is checked for the same property: **a verdict that was
not earned must not look like a pass in the destination system.**

The other risk is a diagram that disagrees with the trace it claims to draw, so the graph emitters
are checked against the model they were built from rather than eyeballed.
"""

from __future__ import annotations

import json
import xml.etree.ElementTree as ET

import pytest

from minicheck import (
    RenderTooLarge,
    check_safety,
    protocol_from_spec,
    to_dot,
    to_junit,
    to_mermaid,
    to_sarif,
    to_svg,
)

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
    ],
}
UNBOUNDED = {
    "fields": ["c"],
    "initial": {"c": 0},
    "transitions": [{"label": "inc", "set": {"c": {"incr": 1}}}],
    "invariants": {"never_neg": {"forbid": {"c": -5}}},
}


def run(spec):
    m = protocol_from_spec(spec)
    return m, check_safety(m)


def cex_of(res):
    return next((p["counterexample"] for p in res["properties"].values() if p["holds"] is False), None)


# ------------------------------------------------------------------------------------- SARIF
def test_sarif_is_valid_json_with_the_right_envelope():
    _, res = run(BROKEN)
    d = json.loads(to_sarif(res))
    assert d["version"] == "2.1.0"
    assert d["runs"][0]["tool"]["driver"]["name"] == "minicheck"
    assert d["runs"][0]["tool"]["driver"]["rules"][0]["id"] == "invariant/not_both"


def test_sarif_reports_a_refutation_as_an_error_with_the_trace():
    _, res = run(BROKEN)
    r = json.loads(to_sarif(res))["runs"][0]["results"][0]
    assert r["level"] == "error"
    assert r["kind"] == "fail"
    assert "violated in 2 steps" in r["message"]["text"]
    flow = r["codeFlows"][0]["threadFlows"][0]["locations"]
    assert len(flow) == 3  # initial + 2 steps


def test_sarif_never_marks_an_undetermined_result_as_a_pass():
    """The load-bearing assertion for this format."""
    _, res = run(UNBOUNDED)
    r = json.loads(to_sarif(res))["runs"][0]["results"][0]
    assert r["kind"] != "pass"
    assert r["kind"] == "informational"
    assert r["level"] == "warning"
    assert "not a pass" in r["message"]["text"]
    assert r["properties"]["verdict"] == "UNDETERMINED"
    assert r["properties"]["exhaustive"] is False


def test_sarif_records_a_genuine_pass_as_a_pass():
    _, res = run(SAFE)
    r = json.loads(to_sarif(res))["runs"][0]["results"][0]
    assert r["kind"] == "pass"
    assert r["properties"]["verdict"] == "PROVED"


# ------------------------------------------------------------------------------------- JUnit
def test_junit_parses_and_counts_correctly():
    _, res = run(BROKEN)
    root = ET.fromstring(to_junit(res))
    assert root.tag == "testsuite"
    assert root.get("tests") == "1"
    assert root.get("failures") == "1"
    assert root.find(".//failure") is not None


def test_junit_maps_undetermined_to_error_not_skipped():
    """`<skipped>` renders GREEN in every CI dashboard, which would restore the original defect."""
    _, res = run(UNBOUNDED)
    xml = to_junit(res)
    root = ET.fromstring(xml)
    assert root.get("errors") == "1"
    assert root.get("skipped") == "0"
    assert root.find(".//skipped") is None
    err = root.find(".//error")
    assert err is not None
    assert err.get("type") == "Undetermined"
    assert "not a pass" in err.text


def test_junit_passes_a_proved_invariant_with_no_child_element():
    _, res = run(SAFE)
    root = ET.fromstring(to_junit(res))
    case = root.find(".//testcase")
    assert list(case) == []  # no failure, no error, no skipped == passed
    assert root.get("failures") == "0" and root.get("errors") == "0"


# ------------------------------------------------------------------------------------ Mermaid
def test_mermaid_draws_every_reachable_state_and_highlights_the_trace():
    m, res = run(BROKEN)
    out = to_mermaid(m, cex_of(res), verdict="REFUTED")
    assert out.startswith("stateDiagram-v2")
    assert out.count(" : ") >= res["reachable_states"]  # one label line per state at minimum
    assert "classDef cex" in out
    assert "1. a_enter" in out and "2. b_enter" in out  # steps are numbered, so order is unambiguous


def test_mermaid_step_numbers_match_the_counterexample_exactly():
    m, res = run(BROKEN)
    cex = cex_of(res)
    out = to_mermaid(m, cex)
    for i, step in enumerate(cex[1:], start=1):
        assert f"{i}. {step['label']}" in out


def test_mermaid_without_a_counterexample_still_draws_the_graph():
    m, res = run(SAFE)
    out = to_mermaid(m, None, verdict="PROVED")
    assert "stateDiagram-v2" in out
    assert "classDef cex" not in out  # nothing to highlight


def test_mermaid_refuses_an_illegibly_large_graph():
    """A hairball is not a diagram; refusing is more useful than emitting one."""
    m = protocol_from_spec(
        {
            "fields": [f"f{i}" for i in range(8)],
            "initial": {f"f{i}": 0 for i in range(8)},
            "transitions": [{"label": f"s{i}", "when": {f"f{i}": 0}, "set": {f"f{i}": 1}} for i in range(8)],
            "invariants": {"t": {"forbid": {"f0": 9}}},
        }
    )
    with pytest.raises(RenderTooLarge, match="does not render legibly"):
        to_mermaid(m, None, max_nodes=60)


# ---------------------------------------------------------------------------------------- DOT
def test_dot_is_wellformed_and_highlights_the_path():
    m, res = run(BROKEN)
    out = to_dot(m, cex_of(res), verdict="REFUTED")
    assert out.startswith("digraph counterexample {")
    assert out.rstrip().endswith("}")
    assert out.count("->") >= 4
    assert "#cc0000" in out  # the trace is coloured


def test_dot_node_count_matches_the_reachable_set():
    m, res = run(BROKEN)
    out = to_dot(m, cex_of(res))
    # node lines only — edge lines also start with `s` and carry a label, so exclude them
    nodes = [ln for ln in out.splitlines() if "[label=" in ln and "->" not in ln]
    assert len(nodes) == res["reachable_states"]


# ---------------------------------------------------------------------------------------- SVG
def test_svg_is_wellformed_xml_and_draws_one_box_per_step():
    m, res = run(BROKEN)
    cex = cex_of(res)
    out = to_svg(m, cex, verdict="REFUTED")
    root = ET.fromstring(out)  # raises if malformed
    assert root.tag.endswith("svg")
    rects = [e for e in root.iter() if e.tag.endswith("rect") and e.get("rx") == "6"]
    assert len(rects) == len(cex)


def test_svg_refuses_when_there_is_no_counterexample_to_draw():
    m, _ = run(SAFE)
    with pytest.raises(ValueError, match="needs a counterexample"):
        to_svg(m, None)


def test_svg_escapes_markup_in_state_values():
    """A field value containing < or & must not produce invalid XML."""
    m = protocol_from_spec(
        {
            "fields": ["s"],
            "initial": {"s": "<a & b>"},
            "transitions": [{"label": "t", "when": {"s": "<a & b>"}, "set": {"s": "x"}}],
            "invariants": {"i": {"forbid": {"s": "x"}}},
        }
    )
    res = check_safety(m)
    ET.fromstring(to_svg(m, cex_of(res)))  # must parse


# -------------------------------------------------------------- every format agrees on the verdict
@pytest.mark.parametrize("spec,expected", [(BROKEN, "REFUTED"), (SAFE, "PROVED"), (UNBOUNDED, "UNDETERMINED")])
def test_no_format_disagrees_with_any_other(spec, expected):
    """The whole point of the shared verdict module: one truth, many renderings."""
    m = protocol_from_spec(spec)
    res = check_safety(m)
    sarif = json.loads(to_sarif(res))["runs"][0]["results"][0]
    assert sarif["properties"]["verdict"] == expected

    root = ET.fromstring(to_junit(res))
    junit_verdict = (
        "REFUTED"
        if root.find(".//failure") is not None
        else "UNDETERMINED"
        if root.find(".//error") is not None
        else "PROVED"
    )
    assert junit_verdict == expected
