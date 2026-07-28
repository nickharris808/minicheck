# Contributing to minicheck

A small, readable, dependency-free engine is the point of this package. That shapes what changes are easy to
accept.

## Ground rules

1. **No dependencies.** Standard library only. A pull request that adds a runtime dependency will be
   declined regardless of merit — depend on `minicheck` from your own package instead.
2. **z3 stays optional and lazy.** The BFS engine must keep working with no third-party package
   installed. There is a test that enforces this by reading the module-level imports.
3. **Counterexamples stay shortest.** The search is breadth-first for that reason. A change that makes
   it depth-first, or that returns the first violation found by a non-BFS route, changes a documented
   guarantee.

## Getting set up

```
python -m venv .venv && . .venv/bin/activate
pip install -e ".[test]"
pytest
```

## Pull requests

- Add a test that fails before your change and passes after. Tests live in `tests/`.
- Keep the public API in `__all__` explicit; anything not listed there is internal.
- If you change the shape of a returned dict, say so loudly — callers index these keys directly.
- `check_liveness` is AG-EF (every reachable state can still reach a goal), not plain reachability.
  Please do not "simplify" it into the weaker check.
- Sign-off by [DCO](https://developercertificate.org/) (`git commit -s`). There is no CLA.

## Reporting a wrong answer

A missed counterexample — `holds: True` for a model that can actually violate the invariant — is the
most serious possible bug here. If you find one, please include the `Protocol` definition in full, so
it can go straight into the test suite.
