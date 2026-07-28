"""The shared three-valued verdict contract.

This module exists so five tools cannot drift apart on what a verdict means. These tests pin the two
properties that matter: an aggregate never rounds *up*, and no combination of inputs produces PROVED
unless every part was proved over a complete search.
"""

from __future__ import annotations

import pytest

from minicheck.verdict import (
    EXIT_ERROR,
    EXIT_PROVED,
    EXIT_REFUTED,
    EXIT_UNDETERMINED,
    Verdict,
    combine,
    exit_code,
    from_holds,
    is_pass,
    to_holds,
)

ALL = [Verdict.PROVED, Verdict.REFUTED, Verdict.UNDETERMINED, Verdict.ERROR]


# ------------------------------------------------------------------------ the mapping from holds
@pytest.mark.parametrize(
    "holds,exhaustive,expected",
    [
        (True, True, Verdict.PROVED),
        (False, True, Verdict.REFUTED),
        (False, False, Verdict.REFUTED),  # a witness stands without exhaustiveness
        (None, True, Verdict.UNDETERMINED),
        (None, False, Verdict.UNDETERMINED),
        (True, False, Verdict.UNDETERMINED),  # the contradiction, downgraded not trusted
    ],
)
def test_from_holds(holds, exhaustive, expected):
    assert from_holds(holds, exhaustive=exhaustive) is expected


def test_a_proof_from_an_incomplete_search_is_downgraded():
    """The single most important line in this module.

    A caller that says "it holds" while also saying "I did not look everywhere" is contradicting
    itself. Trusting the first half is exactly the defect that shipped in 0.1.0.
    """
    assert from_holds(True, exhaustive=False) is Verdict.UNDETERMINED
    assert not is_pass(from_holds(True, exhaustive=False))


@pytest.mark.parametrize("v", ALL)
def test_to_holds_round_trips_the_definite_verdicts(v):
    h = to_holds(v)
    assert h in (True, False, None)
    if v.is_definite:
        assert from_holds(h) is v


# ------------------------------------------------------------------------------- the aggregation
def test_combine_never_rounds_up():
    assert combine([Verdict.PROVED, Verdict.UNDETERMINED]) is Verdict.UNDETERMINED
    assert combine([Verdict.PROVED, Verdict.PROVED]) is Verdict.PROVED
    assert combine([Verdict.UNDETERMINED, Verdict.REFUTED]) is Verdict.REFUTED
    assert combine([Verdict.PROVED, Verdict.REFUTED, Verdict.UNDETERMINED]) is Verdict.REFUTED


def test_a_definite_refutation_dominates_an_undetermined_result():
    """Knowing one thing is broken beats not knowing about another."""
    assert combine([Verdict.REFUTED, Verdict.UNDETERMINED]) is Verdict.REFUTED


def test_error_dominates_everything():
    for v in ALL:
        assert combine([v, Verdict.ERROR]) is Verdict.ERROR


def test_combining_nothing_is_undetermined_not_proved():
    """Vacuous success is the purest form of the defect this module prevents."""
    assert combine([]) is Verdict.UNDETERMINED
    assert not is_pass(combine([]))


@pytest.mark.parametrize("v", ALL)
def test_combining_one_verdict_is_that_verdict(v):
    assert combine([v]) is v


def test_combine_is_order_independent():
    import itertools

    for combo in itertools.permutations([Verdict.PROVED, Verdict.UNDETERMINED, Verdict.REFUTED]):
        assert combine(combo) is Verdict.REFUTED


# ------------------------------------------------------------------------------------ exit codes
def test_exit_codes():
    assert exit_code(Verdict.PROVED) == EXIT_PROVED == 0
    assert exit_code(Verdict.REFUTED) == EXIT_REFUTED == 2
    assert exit_code(Verdict.UNDETERMINED) == EXIT_UNDETERMINED == 3
    assert exit_code(Verdict.ERROR) == EXIT_ERROR == 4


def test_undetermined_is_not_zero_by_default():
    assert exit_code(Verdict.UNDETERMINED) != 0


def test_allow_undetermined_widens_only_the_undetermined_case():
    """A flag meaning "I accept not knowing" must not also mean "I accept known-broken"."""
    assert exit_code(Verdict.UNDETERMINED, allow_undetermined=True) == 0
    assert exit_code(Verdict.REFUTED, allow_undetermined=True) == EXIT_REFUTED
    assert exit_code(Verdict.ERROR, allow_undetermined=True) == EXIT_ERROR


def test_is_pass_is_only_proved():
    assert is_pass(Verdict.PROVED)
    for v in (Verdict.REFUTED, Verdict.UNDETERMINED, Verdict.ERROR):
        assert not is_pass(v)


# --------------------------------------------------------------------------------- serialisation
@pytest.mark.parametrize("v", ALL)
def test_verdicts_serialise_as_their_own_name(v):
    import json

    assert json.dumps({"v": v}) == json.dumps({"v": v.value})
    assert v == v.value  # str enum


@pytest.mark.parametrize("v", ALL)
def test_every_verdict_explains_itself(v):
    assert len(v.explanation) > 30


def test_undetermined_explanation_says_it_is_not_a_pass():
    assert "NOT a pass" in Verdict.UNDETERMINED.explanation
