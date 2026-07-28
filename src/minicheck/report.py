"""Emit results in the formats CI systems already read.

A verdict that only exists in a terminal is a verdict nobody acts on. These two formats put it where
people already look:

``sarif``   SARIF 2.1.0 — GitHub code scanning ingests this and shows a refuted invariant in the
            **Security** tab, with the counterexample as the finding's location and message. Also
            read by GitLab, Azure DevOps, and most static-analysis dashboards.
``junit``   JUnit XML — the lingua franca of CI test reporting. Every CI system on earth renders it.

The mapping of a three-valued verdict onto two-valued formats is the delicate part, and it is
resolved the same way everywhere else in this portfolio: **UNDETERMINED is not a pass.**

* SARIF has a `level` and a `kind`. REFUTED is `level: error, kind: fail`. UNDETERMINED is
  `kind: informational` with `level: warning` — reported, visible, and explicitly *not* `pass`.
* JUnit has pass, `<failure>`, `<error>` and `<skipped>`. REFUTED is `<failure>`. UNDETERMINED is
  `<error>` — **not** `<skipped>`, because a skipped test is green in every dashboard and that would
  quietly restore the exact defect this portfolio exists to prevent.
"""

from __future__ import annotations

import json
import xml.etree.ElementTree as ET
from xml.dom import minidom

from .verdict import Verdict

__all__ = ["to_sarif", "to_junit", "SARIF_VERSION", "SARIF_SCHEMA"]

SARIF_VERSION = "2.1.0"
SARIF_SCHEMA = "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json"

_TOOL_URI = "https://github.com/nickharris808/minicheck"


def _trace_text(counterexample) -> str:
    if not counterexample:
        return ""
    lines = []
    for i, step in enumerate(counterexample):
        label = step["label"] or "(initial)"
        state = ", ".join(f"{k}={v}" for k, v in step["state"].items())
        lines.append(f"  {i}. {label}: {state}")
    return "\n".join(lines)


def _rules(properties: dict) -> list:
    return [
        {
            "id": f"invariant/{name}",
            "name": name,
            "shortDescription": {"text": f"Safety invariant {name!r}"},
            "fullDescription": {
                "text": (
                    "Holds over every reachable state of the model. A failure carries a shortest "
                    "counterexample trace that replays against the model."
                )
            },
            "defaultConfiguration": {"level": "error"},
            "helpUri": _TOOL_URI,
        }
        for name in properties
    ]


def to_sarif(result: dict, *, spec_path: str = "spec.json", version: str = "0.3.0") -> str:
    """SARIF 2.1.0 for GitHub code scanning.

    ``result`` is what `check_safety` returns. Each invariant becomes a rule; each refutation or
    undetermined verdict becomes a result. A proved invariant emits `kind: pass`, so the report
    records what was actually established rather than only what failed.
    """
    props = result.get("properties", {})
    exhaustive = result.get("exhaustive", True)
    results = []

    for name, prop in props.items():
        verdict = (
            Verdict.REFUTED
            if prop["holds"] is False
            else (Verdict.PROVED if prop["holds"] is True else Verdict.UNDETERMINED)
        )
        entry = {
            "ruleId": f"invariant/{name}",
            "message": {"text": ""},
            "locations": [
                {
                    "physicalLocation": {
                        "artifactLocation": {"uri": spec_path},
                        "region": {"startLine": 1},
                    }
                }
            ],
            "properties": {
                "verdict": verdict.value,
                "exhaustive": exhaustive,
                "reachableStates": result.get("reachable_states"),
            },
        }
        if verdict is Verdict.REFUTED:
            steps = len(prop["counterexample"]) - 1
            entry["level"] = "error"
            entry["kind"] = "fail"
            entry["message"]["text"] = (
                f"Invariant {name!r} is violated in {steps} steps.\n{_trace_text(prop['counterexample'])}"
            )
            entry["codeFlows"] = [
                {
                    "threadFlows": [
                        {
                            "locations": [
                                {
                                    "location": {
                                        "message": {
                                            "text": f"{step['label'] or '(initial)'}: "
                                            + ", ".join(f"{k}={v}" for k, v in step["state"].items())
                                        },
                                        "physicalLocation": {
                                            "artifactLocation": {"uri": spec_path},
                                            "region": {"startLine": 1},
                                        },
                                    }
                                }
                                for step in prop["counterexample"]
                            ]
                        }
                    ]
                }
            ]
        elif verdict is Verdict.UNDETERMINED:
            # Visible and explicitly not a pass. `kind: pass` here would be a lie the dashboard
            # would render as green.
            entry["level"] = "warning"
            entry["kind"] = "informational"
            entry["message"]["text"] = (
                f"Invariant {name!r} is UNDETERMINED: the search did not cover the whole state "
                f"space, so nothing was established. This is not a pass. "
                f"{result.get('incomplete_reason', '')}".strip()
            )
        else:
            entry["level"] = "none"
            entry["kind"] = "pass"
            entry["message"]["text"] = (
                f"Invariant {name!r} holds over all {result.get('reachable_states')} reachable states."
            )
        results.append(entry)

    sarif = {
        "$schema": SARIF_SCHEMA,
        "version": SARIF_VERSION,
        "runs": [
            {
                "tool": {
                    "driver": {
                        "name": "minicheck",
                        "version": version,
                        "informationUri": _TOOL_URI,
                        "rules": _rules(props),
                    }
                },
                "results": results,
                "invocations": [
                    {
                        "executionSuccessful": True,
                        "properties": {"exhaustive": exhaustive},
                    }
                ],
            }
        ],
    }
    return json.dumps(sarif, indent=2)


def to_junit(result: dict, *, suite_name: str = "minicheck", spec_path: str = "spec.json") -> str:
    """JUnit XML.

    UNDETERMINED maps to ``<error>``, deliberately not ``<skipped>``. Every CI dashboard renders a
    skipped test as green, so using it here would turn "I could not tell" into a pass — the exact
    failure mode this portfolio is built to avoid.
    """
    props = result.get("properties", {})
    exhaustive = result.get("exhaustive", True)
    n_fail = sum(1 for p in props.values() if p["holds"] is False)
    n_err = sum(1 for p in props.values() if p["holds"] is None)

    suite = ET.Element(
        "testsuite",
        {
            "name": suite_name,
            "tests": str(len(props)),
            "failures": str(n_fail),
            "errors": str(n_err),
            "skipped": "0",
        },
    )
    ET.SubElement(
        suite,
        "properties",
    ).extend(
        [
            ET.Element("property", {"name": "exhaustive", "value": str(exhaustive).lower()}),
            ET.Element("property", {"name": "reachable_states", "value": str(result.get("reachable_states", ""))}),
        ]
    )

    for name, prop in props.items():
        case = ET.SubElement(suite, "testcase", {"classname": f"{suite_name}.{spec_path}", "name": name})
        if prop["holds"] is False:
            steps = len(prop["counterexample"]) - 1
            fail = ET.SubElement(
                case,
                "failure",
                {"type": "InvariantViolated", "message": f"violated in {steps} steps"},
            )
            fail.text = _trace_text(prop["counterexample"])
        elif prop["holds"] is None:
            err = ET.SubElement(
                case,
                "error",
                {"type": "Undetermined", "message": "the search did not cover the whole state space"},
            )
            err.text = (
                f"UNDETERMINED — not a pass. {result.get('incomplete_reason', '')}\n"
                f"No violation was found in the {result.get('reachable_states')} states explored, "
                f"but that is not evidence of absence."
            ).strip()

    raw = ET.tostring(suite, encoding="unicode")
    return minidom.parseString(raw).toprettyxml(indent="  ")
