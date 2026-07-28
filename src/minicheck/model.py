"""Describe a state machine as a Python class instead of a lambda returning tuples.

The `Protocol` constructor is honest but hostile. This is the shape a newcomer meets first::

    Protocol(
        name="mutex", candidate=False, fields=("a", "b", "lock"), initial=(0, 0, 0),
        transitions=lambda s: (
            [("a_enter", (1, s[1], 1))] * (s[0] == 0 and s[2] == 0)
            + [("b_enter", (s[0], 1, 1))] * (s[1] == 0 and s[2] == 0)
        ),
        invariants={"not_both": lambda d: not (d["a"] and d["b"])},
    )

Positional tuples, index arithmetic, and multiplication-by-boolean as a conditional. It works, and
nobody wants to write it. Here is the same machine::

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

        @invariant
        def not_both(s):
            return not (s.a and s.b)

    check_safety(Mutex.protocol())

**The guard is separate from the body on purpose.** Inferring "enabled" from "the body changed
something" would make a legitimate self-loop indistinguishable from a disabled transition, and would
silently drop it. A bare ``@transition`` is always enabled; ``when=`` narrows it.

Fields are read from class annotations, so their order — and therefore the state tuple — is the
order you wrote them in. This compiles down to exactly the same `Protocol`, so everything that works
on one works on the other.
"""

from __future__ import annotations

from ._core import Protocol

__all__ = ["Model", "transition", "invariant", "goal", "ModelError"]


class ModelError(TypeError):
    """The class is not a well-formed model. The message names what to change."""


class _State:
    """A mutable attribute view over a state tuple, handed to guards and bodies.

    Attribute access rather than indexing is the whole point: `s.lock` instead of `s[2]`.
    Assignment is recorded and the result is converted back to a tuple by the caller.
    """

    __slots__ = ("_fields", "_values")

    def __init__(self, fields: tuple, values: tuple):
        object.__setattr__(self, "_fields", fields)
        object.__setattr__(self, "_values", list(values))

    def __getattr__(self, name):
        fields = object.__getattribute__(self, "_fields")
        if name in fields:
            return object.__getattribute__(self, "_values")[fields.index(name)]
        raise AttributeError(
            f"{name!r} is not a field of this model. Declared fields: {list(fields)}. "
            f"Add it as an annotated class attribute if you meant to introduce it."
        )

    def __setattr__(self, name, value):
        fields = object.__getattribute__(self, "_fields")
        if name not in fields:
            raise AttributeError(
                f"cannot assign to {name!r}: it is not a declared field. Declared fields: "
                f"{list(fields)}. A typo here would silently create state the checker never explores."
            )
        object.__getattribute__(self, "_values")[fields.index(name)] = value

    def _tuple(self) -> tuple:
        return tuple(object.__getattribute__(self, "_values"))

    def __repr__(self) -> str:
        fields = object.__getattribute__(self, "_fields")
        values = object.__getattribute__(self, "_values")
        return "State(" + ", ".join(f"{f}={v!r}" for f, v in zip(fields, values)) + ")"


class _Transition:
    __slots__ = ("fn", "when", "label")

    def __init__(self, fn, when=None, label=None):
        self.fn = fn
        self.when = when
        self.label = label or fn.__name__


class _Invariant:
    __slots__ = ("fn", "name")

    def __init__(self, fn, name=None):
        self.fn = fn
        self.name = name or fn.__name__


class _Goal:
    __slots__ = ("fn",)

    def __init__(self, fn):
        self.fn = fn


def transition(fn=None, *, when=None, label=None):
    """Mark a method as a transition. ``when`` is the guard; without one it is always enabled.

    The body mutates the state view in place::

        @transition(when=lambda s: s.n < 3)
        def inc(s):
            s.n = s.n + 1
    """
    if fn is not None and callable(fn) and when is None and label is None:
        return _Transition(fn)  # bare @transition

    def wrap(f):
        return _Transition(f, when=when, label=label)

    return wrap


def invariant(fn=None, *, name=None):
    """Mark a method as a safety invariant. It returns True when the property holds."""
    if fn is not None and callable(fn) and name is None:
        return _Invariant(fn)

    def wrap(f):
        return _Invariant(f, name=name)

    return wrap


def goal(fn):
    """Mark a method as the liveness goal: the states that must remain reachable."""
    return _Goal(fn)


class _ModelMeta(type):
    """Collect annotated fields, transitions, invariants and the goal at class-creation time."""

    def __new__(mcls, name, bases, ns, **kw):
        cls = super().__new__(mcls, name, bases, ns, **kw)
        if not bases:  # the `Model` base itself
            return cls

        annotations = ns.get("__annotations__", {})
        fields = tuple(f for f in annotations if not f.startswith("_"))
        if not fields:
            raise ModelError(
                f"{name} declares no fields. Add annotated class attributes with defaults, e.g.\n"
                f"    class {name}(Model):\n        n: int = 0"
            )

        initial = []
        for f in fields:
            if f not in ns:
                ann = annotations[f]
                type_name = getattr(ann, "__name__", ann)
                raise ModelError(
                    f"{name}.{f} is annotated but has no default, so the initial state is "
                    f"undefined. Write `{f}: {type_name} = <value>`."
                )
            initial.append(ns[f])

        transitions = [v for v in ns.values() if isinstance(v, _Transition)]
        invariants = [v for v in ns.values() if isinstance(v, _Invariant)]
        goals = [v for v in ns.values() if isinstance(v, _Goal)]

        if not transitions:
            raise ModelError(
                f"{name} declares no transitions, so nothing can ever happen. Add one:\n"
                f"    @transition\n    def step(s): ..."
            )
        if len(goals) > 1:
            raise ModelError(f"{name} declares {len(goals)} goals; a model has at most one.")

        seen = set()
        for t in transitions:
            if t.label in seen:
                raise ModelError(
                    f"{name} has two transitions labelled {t.label!r}. Labels appear in "
                    f"counterexample traces, so duplicates make a trace ambiguous."
                )
            seen.add(t.label)

        cls._fields = fields
        cls._initial = tuple(initial)
        cls._transitions = transitions
        cls._invariants = invariants
        cls._goal = goals[0] if goals else None
        return cls


class Model(metaclass=_ModelMeta):
    """Base class for a declaratively-described state machine.

    Subclass it, annotate fields with defaults, and decorate methods. `protocol()` compiles the
    result into the same `Protocol` the rest of the library takes.
    """

    @classmethod
    def protocol(cls, *, name: str | None = None, candidate: bool = False) -> Protocol:
        """Compile to a `Protocol`.

        The guards and bodies are closed over once here; the returned transition function does no
        introspection per state.
        """
        fields = cls._fields
        specs = [(t.label, t.when, t.fn) for t in cls._transitions]

        def transitions(state):
            out = []
            for label, when, body in specs:
                view = _State(fields, state)
                if when is not None and not when(view):
                    continue
                body(view)
                out.append((label, view._tuple()))
            return out

        def as_pred(fn):
            return lambda d: fn(_State(fields, tuple(d[f] for f in fields)))

        return Protocol(
            name=name or cls.__name__,
            candidate=candidate,
            fields=fields,
            initial=cls._initial,
            transitions=transitions,
            invariants={inv.name: as_pred(inv.fn) for inv in cls._invariants},
            goal=as_pred(cls._goal.fn) if cls._goal else None,
        )

    @classmethod
    def to_spec(cls) -> dict:
        """The declarative JSON spec, where the model is simple enough to express as one.

        Raises `ModelError` when it is not. A Python guard can compute anything; the JSON format
        only holds equality tests and literal assignments. Emitting an approximation would produce a
        spec that checks a *different machine* than the class does — so this refuses instead.

        Use `protocol()` for the general case; use this when you want a portable artifact.
        """
        raise ModelError(
            "to_spec() is not implemented, and deliberately so: a Python guard can express "
            "conditions the JSON spec format cannot, and silently approximating one as the other "
            "would emit a spec for a different machine than this class describes. Use "
            "`YourModel.protocol()` and check that, or write the spec by hand if you need the "
            "portable form."
        )
