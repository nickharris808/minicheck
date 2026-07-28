"""The Python-native modelling API.

Two things are being tested. First, that it compiles to *exactly* the same machine as the equivalent
hand-written `Protocol` — a nicer front end that quietly changes semantics would be worse than no
front end. Second, that it refuses the mistakes this style makes easy: a typo'd field name, a missing
default, a duplicate transition label.
"""

from __future__ import annotations

import pytest

from minicheck import Protocol, check_liveness, check_safety
from minicheck.model import Model, ModelError, goal, invariant, transition


class Mutex(Model):
    a: int = 0
    b: int = 0
    lock: int = 0

    @transition(when=lambda s: s.a == 0 and s.lock == 0)
    def a_enter(s):
        s.a = 1
        s.lock = 1

    @transition(when=lambda s: s.b == 0 and s.lock == 0)
    def b_enter(s):
        s.b = 1
        s.lock = 1

    @transition(when=lambda s: s.a == 1)
    def a_exit(s):
        s.a = 0
        s.lock = 0

    @transition(when=lambda s: s.b == 1)
    def b_exit(s):
        s.b = 0
        s.lock = 0

    @invariant
    def not_both(s):
        return not (s.a and s.b)


class BrokenMutex(Model):
    a: int = 0
    b: int = 0

    @transition(when=lambda s: s.a == 0)
    def a_enter(s):
        s.a = 1

    @transition(when=lambda s: s.b == 0)
    def b_enter(s):
        s.b = 1

    @invariant
    def not_both(s):
        return not (s.a and s.b)


# ------------------------------------------------------------ it must be the SAME machine
def test_the_model_api_compiles_to_an_equivalent_protocol():
    """Hand-written vs decorated, same reachable set and same verdict."""

    def hand_written():
        def step(s):
            a, b, lock = s
            out = []
            if a == 0 and lock == 0:
                out.append(("a_enter", (1, b, 1)))
            if b == 0 and lock == 0:
                out.append(("b_enter", (a, 1, 1)))
            if a == 1:
                out.append(("a_exit", (0, b, 0)))
            if b == 1:
                out.append(("b_exit", (a, 0, 0)))
            return out

        return Protocol(
            name="mutex",
            candidate=False,
            fields=("a", "b", "lock"),
            initial=(0, 0, 0),
            transitions=step,
            invariants={"not_both": lambda d: not (d["a"] and d["b"])},
        )

    a = check_safety(Mutex.protocol())
    b = check_safety(hand_written())
    assert a["reachable_states"] == b["reachable_states"]
    assert a["properties"]["not_both"]["holds"] == b["properties"]["not_both"]["holds"] is True


def test_a_broken_model_yields_the_same_counterexample_as_the_tuple_form():
    res = check_safety(BrokenMutex.protocol())
    prop = res["properties"]["not_both"]
    assert prop["holds"] is False
    assert [s["label"] for s in prop["counterexample"]] == [None, "a_enter", "b_enter"]


def test_field_order_follows_the_annotation_order():
    """The state tuple is positional, so the declared order is part of the contract."""
    p = Mutex.protocol()
    assert p.fields == ("a", "b", "lock")
    assert p.initial == (0, 0, 0)


def test_the_model_name_defaults_to_the_class_name():
    assert Mutex.protocol().name == "Mutex"
    assert Mutex.protocol(name="custom").name == "custom"


# --------------------------------------------------------------------------------- liveness
def test_a_goal_drives_the_liveness_check():
    class Fork(Model):
        n: int = 0

        @transition(when=lambda s: s.n == 0)
        def to_goal(s):
            s.n = 1

        @transition(when=lambda s: s.n == 0)
        def to_dead(s):
            s.n = 2

        @invariant
        def trivial(s):
            return True

        @goal
        def reached(s):
            return s.n == 1

    res = check_liveness(Fork.protocol())
    assert res["holds"] is False  # state 2 is a trap
    assert res["counterexample"][-1]["state"]["n"] == 2


def test_more_than_one_goal_is_refused():
    with pytest.raises(ModelError, match="at most one"):

        class TwoGoals(Model):
            n: int = 0

            @transition
            def t(s):
                s.n = 1

            @goal
            def g1(s):
                return s.n == 1

            @goal
            def g2(s):
                return s.n == 0


# ------------------------------------------------------------------ what it refuses, and why
def test_a_model_with_no_fields_is_refused():
    with pytest.raises(ModelError, match="declares no fields"):

        class NoFields(Model):
            @transition
            def t(s):
                pass


def test_an_annotated_field_without_a_default_is_refused():
    """Without a default there is no initial state, so there is nothing to search from."""
    with pytest.raises(ModelError, match="no default"):

        class NoDefault(Model):
            n: int

            @transition
            def t(s):
                s.n = 1


def test_a_model_with_no_transitions_is_refused():
    with pytest.raises(ModelError, match="no transitions"):

        class Static(Model):
            n: int = 0

            @invariant
            def i(s):
                return True


def test_duplicate_transition_labels_are_refused():
    """Labels appear in traces; duplicates make a counterexample ambiguous."""
    with pytest.raises(ModelError, match="two transitions labelled"):

        class Dup(Model):
            n: int = 0

            @transition(label="step")
            def one(s):
                s.n = 1

            @transition(label="step")
            def two(s):
                s.n = 2


def test_assigning_an_undeclared_field_raises_rather_than_inventing_state():
    """A typo here would silently create state the checker never explores."""

    class Typo(Model):
        n: int = 0

        @transition
        def t(s):
            s.m = 1  # not a field

        @invariant
        def i(s):
            return True

    with pytest.raises(AttributeError, match="not a declared field"):
        check_safety(Typo.protocol())


def test_reading_an_undeclared_field_names_the_real_fields():
    class Reader(Model):
        n: int = 0

        @transition(when=lambda s: s.nope == 0)
        def t(s):
            s.n = 1

        @invariant
        def i(s):
            return True

    with pytest.raises(AttributeError, match="Declared fields"):
        check_safety(Reader.protocol())


# ------------------------------------------------------------------------- guards and bodies
def test_a_bare_transition_is_always_enabled():
    class Always(Model):
        n: int = 0

        @transition
        def bump(s):
            s.n = 1

        @invariant
        def i(s):
            return s.n < 5

    p = Always.protocol()
    assert p.transitions((0,)) == [("bump", (1,))]
    assert p.transitions((1,)) == [("bump", (1,))]  # a legitimate self-loop, kept


def test_a_self_loop_is_not_mistaken_for_a_disabled_transition():
    """The reason the guard is separate from the body: a no-op body is still a real step."""

    class Loop(Model):
        n: int = 0

        @transition(when=lambda s: s.n == 0)
        def stay(s):
            pass  # deliberately changes nothing

        @invariant
        def i(s):
            return True

    assert Loop.protocol().transitions((0,)) == [("stay", (0,))]


def test_a_custom_label_is_used_in_the_trace():
    class Labelled(Model):
        n: int = 0

        @transition(label="the step")
        def whatever(s):
            s.n = 1

        @invariant
        def never_one(s):
            return s.n != 1

    res = check_safety(Labelled.protocol())
    assert res["properties"]["never_one"]["counterexample"][-1]["label"] == "the step"


def test_a_named_invariant_uses_its_given_name():
    class Named(Model):
        n: int = 0

        @transition
        def t(s):
            s.n = 1

        @invariant(name="my property")
        def whatever(s):
            return s.n != 1

    assert "my property" in check_safety(Named.protocol())["properties"]


def test_to_spec_refuses_rather_than_approximating():
    """A Python guard can express what the JSON format cannot; approximating is worse than refusing."""
    with pytest.raises(ModelError, match="different machine"):
        Mutex.to_spec()


def test_the_state_view_reprs_readably():
    p = Mutex.protocol()
    captured = {}

    class Peek(Model):
        n: int = 0

        @transition(when=lambda s: captured.setdefault("repr", repr(s)) is not None)
        def t(s):
            s.n = 1

        @invariant
        def i(s):
            return True

    Peek.protocol().transitions((0,))
    assert "State(n=0)" in captured["repr"]
    assert p is not None
