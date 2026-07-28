# Contributing to minicheck

Contributions are welcome. Most of this is one rule.

## The rule

**No change may let this tool give a confident answer it has not earned.**

Everything else is negotiable. That is not. A change is unlikely to be accepted if it lets a verdict
be reported from an analysis that did not establish it, maps an undetermined result onto something a
downstream system renders as success, or silently coerces input rather than refusing it.

Unsure whether a change crosses that line? Open an issue first — much easier before the code exists.

## Reporting a false verdict

The most valuable bug report you can send, and it takes priority. **Include the input.**

If this tool told you something was proved and it was not, that is a security-grade defect. Earlier
ones in this portfolio got public advisories; the response is disclosure plus a regression test, not
a quiet patch.

## Setup

```console
git clone https://github.com/nickharris808/minicheck.git
cd minicheck
python -m venv .venv && source .venv/bin/activate
pip install -e ".[test]"
pytest -q
```

Some tests need extra tools and **skip** without them, so a green local run can be less green
than it looks:

- `spin` and a C compiler — the export differential against SPIN. CI installs SPIN, so it runs there
  regardless. Install it if you are touching `export.py`.
- `pip install -e ".[smt]"` for the z3-backed induction tests.

## What a good test looks like

Three kinds, in increasing order of worth:

1. **Unit tests** — they ask whether the code agrees with itself. Necessary, least informative.
2. **Adversarial tests** — malformed, empty, enormous, out-of-distribution input, with one oracle:
   *no input may produce a confident-looking answer that is wrong.*
3. **Differential tests** — the best. Check against an independent implementation of the same
   question.

**Mutation-test your regression test.** Reintroduce the bug and confirm the test goes red. A test
that passes on both the broken and the fixed code is worth nothing.

## Numbers in documentation

`tests/test_readme_claims.py` re-derives every numeric claim in the README. If you change the test
count or add source, it fails until the README matches. That is working as intended — never write a
number the published code cannot reproduce.

## Style

- `ruff check .` and `ruff format --check .` must pass; line length 120.
- Comments explain **why**. The code says what.
- Error messages name the fix, not just the fault.

## Responsible disclosure

Do not add findings or verdicts about **named** third-party products, vendors or protocols. Ship the
checker and the methodology.

## Licence

MIT. By contributing you agree your contribution is licensed the same way.

---

Portfolio-wide guidance: <https://nickharris808.github.io/verification-docs/guides/contributing/>
