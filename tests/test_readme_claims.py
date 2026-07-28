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
