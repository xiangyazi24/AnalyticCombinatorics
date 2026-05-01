Done.

Appended the explicit derangement EGF intermediate identity to
`AnalyticCombinatorics/Examples/Derangements.lean`:

```lean
example :
    (1 - PowerSeries.X) * derangementClass.egf =
      PowerSeries.evalNegHom (PowerSeries.exp ℚ) := by
  exact one_sub_X_mul_derangementClass_egf
```

Mathlib's workable `exp(-X)` form here is
`PowerSeries.evalNegHom (PowerSeries.exp ℚ)`.

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Derangements.lean`
- `lake build`
- no `sorry`/`admit` in `AnalyticCombinatorics/Examples/Derangements.lean`
