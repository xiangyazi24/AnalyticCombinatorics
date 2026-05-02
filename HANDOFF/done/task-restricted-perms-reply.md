Done.

Created `AnalyticCombinatorics/PartA/Ch2/RestrictedPerms.lean`.

Contents:
- `boundedCyclePermCount (m n : ℕ) : ℕ`, using the distinguished-cycle recurrence.
- `noFixedNo2Count : ℕ → ℕ`, excluding 1-cycles and 2-cycles.
- `zigzagTriangle` and `zigzagCount : ℕ → ℕ`, using the Entringer triangle.
- Native-decide sanity checks for the requested small values, plus checked instances of the tangent/secant convolution recurrence for `2 ≤ n ≤ 7`.

Verification:

```text
lake build AnalyticCombinatorics.PartA.Ch2.RestrictedPerms
```

passed.
