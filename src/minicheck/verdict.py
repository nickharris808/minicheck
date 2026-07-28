"""The three-valued verdict, defined once.

Every tool in this portfolio answers the same shape of question and must answer it the same way. The
contract:

    PROVED        the whole reachable space was enumerated and the property held everywhere
    REFUTED       a counterexample exists; it is attached and it replays
    UNDETERMINED  the analysis did not finish, so nothing was established
    ERROR         no analysis ran at all

The asymmetry between PROVED and REFUTED is the load-bearing idea. Refuting a safety property needs
ONE witness, so a refutation stays sound even when the search was cut short. Proving one is a claim
about EVERY reachable state, so it may only be issued when the search actually covered every reachable
state. Anything else is UNDETERMINED — which is **never** a pass.

This module exists because that contract was previously re-implemented in five places, and every new
output format is another chance for the five to drift apart. Emitters (JSON, SARIF, JUnit, Mermaid,
DOT) all render `Verdict`, so a change here reaches all of them at once.

>>> combine([Verdict.PROVED, Verdict.UNDETERMINED])
<Verdict.UNDETERMINED: 'UNDETERMINED'>
>>> combine([Verdict.UNDETERMINED, Verdict.REFUTED])
<Verdict.REFUTED: 'REFUTED'>
"""

from __future__ import annotations

from enum import Enum

__all__ = [
    "Verdict",
    "from_holds",
    "to_holds",
    "combine",
    "exit_code",
    "is_pass",
    "EXIT_PROVED",
    "EXIT_REFUTED",
    "EXIT_UNDETERMINED",
    "EXIT_ERROR",
    "SCHEMA_VERSION",
]

#: Bump when the emitted JSON shape changes incompatibly.
SCHEMA_VERSION = "1"

EXIT_PROVED = 0
EXIT_REFUTED = 2
EXIT_UNDETERMINED = 3
EXIT_ERROR = 4


class Verdict(str, Enum):
    """What the analysis established. A `str` enum so it serialises as itself."""

    PROVED = "PROVED"
    REFUTED = "REFUTED"
    UNDETERMINED = "UNDETERMINED"
    ERROR = "ERROR"

    @property
    def is_definite(self) -> bool:
        """True for the two verdicts that actually settle the question."""
        return self in (Verdict.PROVED, Verdict.REFUTED)

    @property
    def explanation(self) -> str:
        return {
            Verdict.PROVED: "every reachable state was enumerated and the property held in all of them",
            Verdict.REFUTED: "a counterexample was found; it starts at the initial state and replays",
            Verdict.UNDETERMINED: (
                "the analysis did not cover the whole state space, so nothing was established. This is NOT a pass"
            ),
            Verdict.ERROR: "no analysis ran, so nothing is known about the input",
        }[self]


def from_holds(holds: bool | None, *, exhaustive: bool = True) -> Verdict:
    """Map a three-valued ``holds`` plus exhaustiveness onto a `Verdict`.

    ``holds=True`` with ``exhaustive=False`` is a contradiction the callers must never produce, so it
    is downgraded here rather than trusted: a proof that did not examine the whole space is not one.
    """
    if holds is False:
        return Verdict.REFUTED  # a witness stands regardless of exhaustiveness
    if holds is None:
        return Verdict.UNDETERMINED
    return Verdict.PROVED if exhaustive else Verdict.UNDETERMINED


def to_holds(verdict: Verdict) -> bool | None:
    """Inverse of `from_holds`, for callers that still speak in ``holds``."""
    return {
        Verdict.PROVED: True,
        Verdict.REFUTED: False,
        Verdict.UNDETERMINED: None,
        Verdict.ERROR: None,
    }[verdict]


def combine(verdicts) -> Verdict:
    """Aggregate several verdicts into one, without ever rounding up.

    Precedence: ERROR > REFUTED > UNDETERMINED > PROVED. A definite refutation dominates an
    undetermined result, an undetermined result is never promoted to PROVED, and the aggregate is
    PROVED only when every part is.
    """
    seen = list(verdicts)
    if not seen:
        # Nothing was checked. Saying PROVED here would be the purest form of the defect this
        # module exists to prevent.
        return Verdict.UNDETERMINED
    if Verdict.ERROR in seen:
        return Verdict.ERROR
    if Verdict.REFUTED in seen:
        return Verdict.REFUTED
    if Verdict.UNDETERMINED in seen:
        return Verdict.UNDETERMINED
    return Verdict.PROVED


def exit_code(verdict: Verdict, *, allow_undetermined: bool = False) -> int:
    """Process exit code. UNDETERMINED is 3, not 0, unless explicitly opted out of.

    ``allow_undetermined`` widens ONLY the undetermined case. A refutation still fails, because a
    flag that says "I accept not knowing" must not also mean "I accept known-broken".
    """
    if verdict is Verdict.UNDETERMINED and allow_undetermined:
        return EXIT_PROVED
    return {
        Verdict.PROVED: EXIT_PROVED,
        Verdict.REFUTED: EXIT_REFUTED,
        Verdict.UNDETERMINED: EXIT_UNDETERMINED,
        Verdict.ERROR: EXIT_ERROR,
    }[verdict]


def is_pass(verdict: Verdict) -> bool:
    """The only verdict that is a pass. Deliberately not `verdict != REFUTED`."""
    return verdict is Verdict.PROVED
