Done.

Added `coeff_exp_pow_eq_pow_div_factorial` in
`AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean`, immediately after the
existing square case.

Proof uses Mathlib's `PowerSeries.exp_pow_eq_rescale_exp`:
`(exp ℚ)^k = rescale (k : ℚ) (exp ℚ)`, then simplifies coefficients with
`coeff_rescale` and `coeff_exp`.

Verification:
- `lake env lean AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean`
- `lake build`

No new `sorry`s.
