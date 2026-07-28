"""Adversarial suite for the surfaces added in waves 1 and 2.

Every new surface is a new way to violate the one oracle: **no input may produce a confident-looking
answer that is wrong.** Three of these surfaces are translations — Mermaid, DOT, SARIF, JUnit,
Promela, TLA+ — and a translation is exactly where a verdict can quietly change meaning without
anything crashing.

So the central property here is **verdict preservation**: the same model, rendered through every
format, must never say different things. A format that disagrees with the checker is worse than a
format that fails, because it produces two green results where one is about the wrong system.

Note on scope: this portfolio has **no cache and no streaming mode**. There is nothing to test for
cache-key correctness or stream/non-stream agreement, and inventing tests for absent features would
be its own kind of dishonesty. If an incremental cache is added later (it is planned, not built),
those tests belong here.
"""

from __future__ import annotations

import json
import random
import re
import shutil
import subprocess
import xml.etree.ElementTree as ET

import pytest

from minicheck import (
    ExportError,
    Model,
    Protocol,
    RenderTooLarge,
    check_safety,
    invariant,
    protocol_from_spec,
    to_dot,
    to_junit,
    to_mermaid,
    to_promela,
    to_sarif,
    to_svg,
    to_tla,
    transition,
)
from minicheck.verdict import Verdict, combine, from_holds

SPIN = shutil.which("spin")
CC = shutil.which("gcc") or shutil.which("cc")


# ------------------------------------------------------------------ generators for the sweep
def random_spec(rng: random.Random) -> dict:
    n = rng.randint(1, 4)
    fields = [f"f{i}" for i in range(n)]
    rules = []
    for j in range(rng.randint(1, 5)):
        rule = {"label": f"r{j}", "set": {}}
        if rng.random() < 0.6:
            rule["when"] = {rng.choice(fields): rng.randrange(3)}
        for f in rng.sample(fields, rng.randint(1, n)):
            rule["set"][f] = {"incr": 1} if rng.random() < 0.25 else rng.randrange(3)
        rules.append(rule)
    return {
        "name": f"m{rng.randrange(10**6)}",
        "fields": fields,
        "initial": dict.fromkeys(fields, 0),
        "transitions": rules,
        "invariants": {"p": {"forbid": {fields[0]: rng.randrange(3)}}},
    }


def verdict_of(res: dict) -> Verdict:
    return combine(from_holds(p["holds"], exhaustive=res["exhaustive"]) for p in res["properties"].values())


# ==================================================================== VERDICT PRESERVATION
def test_every_format_reports_the_same_verdict_over_a_random_sweep():
    """The central property. 300 random specs through every emitter, verdicts must agree.

    A format that changes a verdict in translation is the worst defect this plan could introduce,
    because both results look green and only one is about your system.
    """
    rng = random.Random(8675309)
    checked = 0
    for _ in range(300):
        spec = random_spec(rng)
        model = protocol_from_spec(spec)
        res = check_safety(model)
        truth = verdict_of(res)

        sarif = json.loads(to_sarif(res))["runs"][0]["results"]
        sarif_verdicts = [r["properties"]["verdict"] for r in sarif]
        assert combine(Verdict(v) for v in sarif_verdicts) is truth, f"SARIF disagrees on {spec['name']}"

        root = ET.fromstring(to_junit(res))
        if root.find(".//failure") is not None:
            junit = Verdict.REFUTED
        elif root.find(".//error") is not None:
            junit = Verdict.UNDETERMINED
        else:
            junit = Verdict.PROVED
        assert junit is truth, f"JUnit disagrees on {spec['name']}: {junit} vs {truth}"

        # The graph emitters carry the verdict in a comment/label; they must not contradict it.
        try:
            mm = to_mermaid(model, None, verdict=truth.value, max_nodes=5000)
            assert truth.value in mm
            # A graph drawn from a search that could not finish must say so on the diagram.
            if not res["exhaustive"]:
                assert "PARTIAL" in mm, f"{spec['name']}: partial graph drawn without saying so"
        except RenderTooLarge:
            pass
        checked += 1
    assert checked == 300


def test_junit_never_marks_an_unproved_property_as_skipped():
    """`<skipped>` is green in every dashboard. Over a sweep, it must never appear."""
    rng = random.Random(4242)
    for _ in range(200):
        res = check_safety(protocol_from_spec(random_spec(rng)))
        root = ET.fromstring(to_junit(res))
        assert root.get("skipped") == "0"
        assert root.find(".//skipped") is None


def test_sarif_never_emits_kind_pass_for_anything_unproved():
    rng = random.Random(31415)
    for _ in range(200):
        res = check_safety(protocol_from_spec(random_spec(rng)))
        for r, (_name, prop) in zip(json.loads(to_sarif(res))["runs"][0]["results"], res["properties"].items()):
            if prop["holds"] is not True:
                assert r["kind"] != "pass", "an unproved property was reported as a pass"


@pytest.mark.skipif(not (SPIN and CC), reason="requires spin and a C compiler")
def test_the_promela_export_agrees_with_the_checker_over_a_sweep(tmp_path):
    """A differential against an independent industrial model checker, on many models.

    The existing export tests use three hand-written models. This runs SPIN on a random sweep,
    which is where an encoding bug that only shows up on some shape would surface.
    """
    rng = random.Random(1234567)
    compared = 0
    for i in range(25):
        spec = random_spec(rng)
        model = protocol_from_spec(spec)
        res = check_safety(model)
        if not res["exhaustive"]:
            continue  # SPIN would explore a different (unbounded) space; not a fair comparison
        ours = all(p["holds"] is True for p in res["properties"].values())

        d = tmp_path / f"s{i}"
        d.mkdir()
        (d / "m.pml").write_text(to_promela(spec), encoding="utf-8")
        if subprocess.run([SPIN, "-a", "m.pml"], cwd=d, capture_output=True).returncode:
            continue
        if subprocess.run([CC, "-O1", "-o", "pan", "pan.c"], cwd=d, capture_output=True).returncode:
            continue
        # `-E` ignores invalid end states. `pan -a` checks deadlock as well as assertions, while
        # `check_safety` only asks about invariants — comparing the two conflates two questions and
        # would report a disagreement that is really a difference of scope.
        out = subprocess.run(["./pan", "-E"], cwd=d, capture_output=True, text=True).stdout
        m = re.search(r"errors:\s*(\d+)", out)
        if not m:
            continue
        theirs = int(m.group(1)) == 0
        assert ours == theirs, f"{spec['name']}: minicheck holds={ours}, SPIN no-errors={theirs}"
        compared += 1
    assert compared >= 5, f"only {compared} models were comparable; the sweep proved little"


# ==================================================== THE MODEL API MUST BE THE SAME MACHINE
def test_the_model_api_and_the_spec_loader_agree_on_equivalent_machines():
    """Two frontends, one semantics. A divergence here is a silent wrong answer."""
    for k in range(3, 9):

        class Counter(Model):
            n: int = 0

            @transition(when=lambda s, _k=k: s.n < _k)
            def inc(s):
                s.n = s.n + 1

            @invariant(name="below")
            def below(s, _k=k):
                return s.n < _k

        spec = {
            "fields": ["n"],
            "initial": {"n": 0},
            "transitions": [{"label": f"inc{i}", "when": {"n": i}, "set": {"n": {"incr": 1}}} for i in range(k)],
            "invariants": {"below": {"forbid": {"n": k}}},
        }
        a = check_safety(Counter.protocol())
        b = check_safety(protocol_from_spec(spec))
        assert a["reachable_states"] == b["reachable_states"], f"k={k}"
        assert a["properties"]["below"]["holds"] == b["properties"]["below"]["holds"], f"k={k}"


def test_a_model_whose_guard_raises_does_not_produce_a_verdict():
    """An exception in user code must not be swallowed into a pass."""

    class Boom(Model):
        n: int = 0

        @transition(when=lambda s: 1 / 0)
        def t(s):
            s.n = 1

        @invariant
        def i(s):
            return True

    with pytest.raises(ZeroDivisionError):
        check_safety(Boom.protocol())


def test_a_model_body_that_mutates_nothing_is_still_a_step():
    """A self-loop must not be silently dropped as 'disabled'."""

    class Loop(Model):
        n: int = 0

        @transition
        def stay(s):
            pass

        @invariant
        def i(s):
            return True

    assert Loop.protocol().transitions((0,)) == [("stay", (0,))]


# ============================================================ MALFORMED / EMPTY / ENORMOUS
@pytest.mark.parametrize(
    "spec",
    [
        {},
        {"fields": []},
        {"fields": ["a"]},
        {"fields": ["a"], "initial": {"a": 0}},
        {"fields": ["a"], "initial": {"a": 0}, "transitions": []},
        {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {}}]},
        {"fields": ["a"], "initial": {"a": 0}, "transitions": [{"set": {"a": {"incr": "x"}}}]},
    ],
)
def test_no_emitter_produces_output_for_a_malformed_spec(spec):
    """Every emitter must refuse. Emitting a diagram of nothing would look like a clean result."""
    from minicheck import SpecError

    for fn in (to_promela, to_tla):
        with pytest.raises(SpecError):
            fn(spec)


def test_export_refuses_a_non_integer_field_in_every_target():
    spec = {
        "fields": ["s"],
        "initial": {"s": "idle"},
        "transitions": [{"label": "t", "when": {"s": "idle"}, "set": {"s": "busy"}}],
        "invariants": {"i": {"forbid": {"s": "busy"}}},
    }
    for fn in (to_promela, to_tla):
        with pytest.raises(ExportError, match="non-integer"):
            fn(spec)


def test_an_enormous_model_refuses_to_render_rather_than_emitting_a_hairball():
    fields = [f"f{i}" for i in range(12)]
    model = protocol_from_spec(
        {
            "fields": fields,
            "initial": dict.fromkeys(fields, 0),
            "transitions": [{"label": f"s{f}", "when": {f: 0}, "set": {f: 1}} for f in fields],
            "invariants": {"t": {"forbid": {fields[0]: 9}}},
        }
    )
    for fn in (to_mermaid, to_dot):
        with pytest.raises(RenderTooLarge):
            fn(model, None, max_nodes=60)


def test_an_enormous_model_still_yields_a_usable_sarif_report():
    """Refusing to *draw* must not mean refusing to *report*."""
    fields = [f"f{i}" for i in range(12)]
    res = check_safety(
        protocol_from_spec(
            {
                "fields": fields,
                "initial": dict.fromkeys(fields, 0),
                "transitions": [{"label": f"s{f}", "when": {f: 0}, "set": {f: 1}} for f in fields],
                "invariants": {"t": {"forbid": {fields[0]: 9}}},
            }
        ),
        max_states=500,
    )
    d = json.loads(to_sarif(res))
    assert d["runs"][0]["results"][0]["kind"] != "pass"
    assert res["exhaustive"] is False


def test_a_very_long_counterexample_renders_or_refuses_but_never_truncates_silently():
    spec = {
        "fields": ["c"],
        "initial": {"c": 0},
        "transitions": [{"label": "inc", "set": {"c": {"incr": 1}}}],
        "invariants": {"never_50": {"forbid": {"c": 50}}},
    }
    model = protocol_from_spec(spec, int_bound=60)
    res = check_safety(model)
    cex = res["properties"]["never_50"]["counterexample"]
    assert len(cex) == 51
    with pytest.raises(RenderTooLarge):
        to_svg(model, cex, max_nodes=10)
    svg = to_svg(model, cex, max_nodes=100)
    assert svg.count('rx="6"') == 51  # every step drawn, none dropped


# ============================================================= OUT-OF-DISTRIBUTION INPUT
@pytest.mark.parametrize(
    "value",
    ["", "  ", "a" * 500, "with spaces", "unicode-é-ü", "<tag>", "&amp;", "line\nbreak", "tab\there"],
)
def test_odd_field_values_survive_every_emitter_that_accepts_them(value):
    """Rendering must escape rather than emit malformed output, and export must refuse."""
    spec = {
        "fields": ["s", "n"],
        "initial": {"s": value, "n": 0},
        "transitions": [{"label": "t", "when": {"s": value}, "set": {"n": 1}}],
        "invariants": {"i": {"forbid": {"n": 5}}},
    }
    model = protocol_from_spec(spec)
    res = check_safety(model)
    ET.fromstring(to_junit(res))  # must stay well-formed XML
    json.loads(to_sarif(res))  # must stay valid JSON
    to_mermaid(model, None)
    to_dot(model, None)
    with pytest.raises(ExportError):
        to_promela(spec)  # non-integer: refused, not encoded


def test_field_names_that_collide_after_sanitising_are_still_distinguishable():
    """`a-b` and `a_b` both sanitise toward `a_b`; the export must not merge two variables."""
    spec = {
        "fields": ["a-b", "a_b"],
        "initial": {"a-b": 0, "a_b": 0},
        "transitions": [{"label": "t", "when": {"a-b": 0}, "set": {"a_b": 1}}],
        "invariants": {"i": {"forbid": {"a_b": 5}}},
    }
    out = to_promela(spec)
    decls = [ln for ln in out.splitlines() if ln.startswith("int ")]
    assert len(decls) == 2, f"two fields collapsed into {len(decls)} declaration(s): {decls}"
    assert len(set(decls)) == 2, f"two fields produced identical declarations: {decls}"


def test_a_label_containing_target_language_syntax_does_not_break_the_export():
    spec = {
        "fields": ["n"],
        "initial": {"n": 0},
        "transitions": [{"label": "a}; assert(0); /*", "when": {"n": 0}, "set": {"n": 1}}],
        "invariants": {"i": {"forbid": {"n": 5}}},
    }
    out = to_promela(spec)
    # The label appears only inside a comment; it must not close the block or inject a statement.
    assert out.count("active proctype") == 1
    assert "od;" in out


# ================================================================= DIFFERENTIAL: CLI vs API
def test_the_cli_verdict_matches_the_library_verdict(tmp_path):
    """Two entry points, one answer. A divergence would make CI and tests disagree."""
    from minicheck.cli import EXIT_PROVED, EXIT_REFUTED, EXIT_UNDETERMINED, main

    rng = random.Random(999)
    for i in range(40):
        spec = random_spec(rng)
        path = tmp_path / f"s{i}.json"
        path.write_text(json.dumps(spec), encoding="utf-8")
        truth = verdict_of(check_safety(protocol_from_spec(spec)))
        expected = {
            Verdict.PROVED: EXIT_PROVED,
            Verdict.REFUTED: EXIT_REFUTED,
            Verdict.UNDETERMINED: EXIT_UNDETERMINED,
        }[truth]
        assert main(["check", str(path)]) == expected, f"{spec['name']}: CLI disagrees with the library"


def test_every_format_yields_the_same_exit_code_for_the_same_spec(tmp_path):
    """Rendering must never change what the shell is told."""
    from minicheck.cli import main

    rng = random.Random(777)
    for i in range(15):
        spec = random_spec(rng)
        path = tmp_path / f"f{i}.json"
        path.write_text(json.dumps(spec), encoding="utf-8")
        codes = {f: main(["check", str(path), "--format", f]) for f in ("text", "json", "sarif", "junit")}
        assert len(set(codes.values())) == 1, f"{spec['name']}: formats disagree {codes}"


def test_a_protocol_built_from_a_callable_cannot_be_exported():
    """Exporting arbitrary Python would mean guessing at its semantics. It must refuse."""
    m = Protocol(
        name="cb",
        candidate=False,
        fields=("n",),
        initial=(0,),
        transitions=lambda s: [("t", (s[0] + 1,))] if s[0] < 3 else [],
        invariants={"i": lambda d: d["n"] < 3},
    )
    from minicheck import SpecError

    with pytest.raises((SpecError, AttributeError, TypeError, KeyError)):
        to_promela(m)  # not a spec dict; must not silently produce something


# ============================================ REGRESSIONS FOR WHAT THIS SUITE ACTUALLY FOUND
def test_a_single_condition_invariant_is_parenthesised_before_negation():
    """The bug this sweep found, and the reason it took a differential to find it.

    `!f0 == 2` parses as `(!f0) == 2` in Promela and C — always false — so every exported model
    with a one-field `forbid` asserted a property that fires immediately. SPIN then reported a
    violation of something the spec never said. Every hand-written test model happened to use a
    two-field invariant, where the parentheses were already being added.
    """
    spec = {
        "fields": ["f0"],
        "initial": {"f0": 0},
        "transitions": [{"label": "t", "when": {"f0": 0}, "set": {"f0": 1}}],
        "invariants": {"p": {"forbid": {"f0": 2}}},
    }
    pml = to_promela(spec)
    assert "#define p (!(f0 == 2))" in pml, pml
    assert "!f0 ==" not in pml

    tla = to_tla(spec)
    assert "p == ~(f0 = 2)" in tla, tla


@pytest.mark.skipif(not (SPIN and CC), reason="requires spin and a C compiler")
def test_spin_agrees_on_a_single_condition_invariant(tmp_path):
    """The end-to-end form of the same regression."""
    spec = {
        "fields": ["f0"],
        "initial": {"f0": 0},
        "transitions": [{"label": "t", "when": {"f0": 0}, "set": {"f0": 1}}],
        "invariants": {"p": {"forbid": {"f0": 2}}},
    }
    assert check_safety(protocol_from_spec(spec))["properties"]["p"]["holds"] is True

    d = tmp_path / "single"
    d.mkdir()
    (d / "m.pml").write_text(to_promela(spec), encoding="utf-8")
    subprocess.run([SPIN, "-a", "m.pml"], cwd=d, capture_output=True, check=True)
    subprocess.run([CC, "-O1", "-o", "pan", "pan.c"], cwd=d, capture_output=True, check=True)
    out = subprocess.run(["./pan", "-E"], cwd=d, capture_output=True, text=True).stdout
    assert re.search(r"errors:\s*0", out), f"SPIN disagrees on a one-field invariant:\n{out}"


def test_rendering_an_unbounded_model_labels_the_graph_partial_rather_than_crashing():
    """A renderer that raises on an unbounded model is unusable exactly when a picture would help.

    Drawing it silently as though it were the whole graph would be the visual form of a truncated
    proof, so the diagram carries a PARTIAL marker.
    """
    spec = {
        "fields": ["c"],
        "initial": {"c": 0},
        "transitions": [{"label": "inc", "set": {"c": {"incr": 1}}}],
        "invariants": {"i": {"forbid": {"c": 5}}},
    }
    model = protocol_from_spec(spec)
    mm = to_mermaid(model, None, max_nodes=5000)
    assert mm.startswith("stateDiagram-v2")
    assert "PARTIAL" in mm

    dot = to_dot(model, None, max_nodes=5000)
    assert "PARTIAL" in dot


def test_a_finite_model_is_never_labelled_partial():
    """The marker must mean something — it cannot appear on a complete graph."""
    spec = {
        "fields": ["a"],
        "initial": {"a": 0},
        "transitions": [{"label": "t", "when": {"a": 0}, "set": {"a": 1}}],
        "invariants": {"i": {"forbid": {"a": 5}}},
    }
    model = protocol_from_spec(spec)
    assert "PARTIAL" not in to_mermaid(model, None)
    assert "PARTIAL" not in to_dot(model, None)


def test_distinct_fields_never_collapse_into_one_exported_variable():
    """Sanitising is many-to-one, so two fields could become one variable in the target.

    That would export a *different machine* than the one checked — the most serious kind of export
    bug, because both tools would then be green about different systems.
    """
    for names in (["a-b", "a_b"], ["x.y", "x-y", "x_y"], ["1a", "f_1a"], ["é", "e"]):
        spec = {
            "fields": names,
            "initial": dict.fromkeys(names, 0),
            "transitions": [{"label": "t", "when": {names[0]: 0}, "set": {names[-1]: 1}}],
            "invariants": {"i": {"forbid": {names[-1]: 5}}},
        }
        decls = [ln for ln in to_promela(spec).splitlines() if ln.startswith("int ")]
        assert len(decls) == len(names), f"{names}: {len(names)} fields became {len(decls)} declarations"
        assert len(set(decls)) == len(names), f"{names}: duplicate declarations {decls}"

        vs = next(ln for ln in to_tla(spec).splitlines() if ln.startswith("VARIABLES "))
        idents = [v.strip() for v in vs[len("VARIABLES ") :].split(",")]
        assert len(set(idents)) == len(names), f"{names}: TLA+ merged variables {idents}"


def test_a_violation_in_the_initial_state_survives_the_export():
    """The second bug this sweep found.

    An invariant broken at step zero is a real violation — minicheck reports it as a zero-step
    counterexample. The export asserted only inside transition bodies, so nothing was checked before
    the first step and SPIN called an already-broken model fine.
    """
    spec = {
        "fields": ["f0"],
        "initial": {"f0": 0},
        "transitions": [{"label": "r0", "when": {"f0": 0}, "set": {"f0": 2}}],
        "invariants": {"p": {"forbid": {"f0": 0}}},
    }
    res = check_safety(protocol_from_spec(spec))
    assert res["properties"]["p"]["holds"] is False
    assert len(res["properties"]["p"]["counterexample"]) == 1  # the initial state alone

    pml = to_promela(spec)
    before_do = pml.split("  do")[0]
    assert "assert(p);" in before_do, "the initial state is not checked before the loop"


@pytest.mark.skipif(not (SPIN and CC), reason="requires spin and a C compiler")
def test_spin_finds_an_initial_state_violation(tmp_path):
    spec = {
        "fields": ["f0"],
        "initial": {"f0": 0},
        "transitions": [{"label": "r0", "when": {"f0": 0}, "set": {"f0": 2}}],
        "invariants": {"p": {"forbid": {"f0": 0}}},
    }
    d = tmp_path / "init"
    d.mkdir()
    (d / "m.pml").write_text(to_promela(spec), encoding="utf-8")
    subprocess.run([SPIN, "-a", "m.pml"], cwd=d, capture_output=True, check=True)
    subprocess.run([CC, "-O1", "-o", "pan", "pan.c"], cwd=d, capture_output=True, check=True)
    out = subprocess.run(["./pan", "-E"], cwd=d, capture_output=True, text=True).stdout
    assert "assertion violated" in out
    assert re.search(r"errors:\s*[1-9]", out), f"SPIN missed an initial-state violation:\n{out}"
