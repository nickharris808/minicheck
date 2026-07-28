# Security advisory — false "proved safe" verdict via `int_bound` (minicheck 0.1.0)

**Severity:** high for anyone relying on a verdict. **Fixed in:** 0.2.0. **Found by:** the maintainer,
during a hardening audit. **Exploitation:** none known; the package had negligible adoption.

## Summary

`protocol_from_spec` applied `int_bound` (default 64) as a **clamp**. An integer field driven past
the bound saturated at it instead of continuing, so states beyond the bound were never generated —
and `check_safety` reported the invariant as **holding**, with no warning that the search had been
truncated.

A verifier reporting a proof it did not perform is worse than no verifier, because it displaces the
scrutiny a user would otherwise apply.

## Reproducer (0.1.0)

```python
from minicheck import protocol_from_spec, check_safety

spec = {
    "fields": ["c"],
    "initial": {"c": 0},
    "transitions": [{"label": "inc", "set": {"c": {"incr": 1}}}],
    "invariants": {"never_100": {"forbid": {"c": 100}}},
}
check_safety(protocol_from_spec(spec))
# 0.1.0 -> {'reachable_states': 65, ...}  never_100: {'holds': True}
```

The counter increments without limit and genuinely reaches 100. `holds: True` is false.

## Reach

The defect was reachable from every surface that accepted a declarative spec: the library, the
`minicheck-mcp` MCP server (agent-facing), and the public Hugging Face Space.

## Fix

1. Integers are no longer clamped. A transition leaving the bound raises `IntBoundExceeded`.
2. `check_safety` is now three-valued. A search that stops early returns `holds: None` with
   `exhaustive: False` and an `incomplete_reason`, never `True`.
3. A counterexample found before the search stopped is still returned — refutation needs one witness,
   so it stays sound under a partial sweep. Only `holds: True` requires exhaustiveness.
4. `spec_warnings` reports conditions that are trivially satisfied because they name a value the
   bounded space cannot represent.

## Action required

Upgrade, then re-run any spec whose verdict you relied on. Treat a `holds: None` as a result you do
not yet have — raise `int_bound`, or add a `when` guard that bounds the growing field.
