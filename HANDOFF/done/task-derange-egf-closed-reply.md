Done.

Appended to `AnalyticCombinatorics/Examples/Derangements.lean`:

- `derangementClass_egf_mul_one_sub_X_eq_exp_neg`
  - right-multiplied closed form: `D(X) * (1 - X) = exp(-X)`
  - uses Mathlib's existing spelling `PowerSeries.evalNegHom (PowerSeries.exp ℚ)` for `exp(-X)`
- `derangementClass_egf_mul_exp_mul_one_sub_X`
  - combined identity: `D(X) * exp(X) * (1 - X) = 1`

Verification:

- `lake env lean AnalyticCombinatorics/Examples/Derangements.lean`
- `lake build`

Both passed. No new `sorry`s or axioms.
