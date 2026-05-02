# Surjections via EGF — reply

Created `AnalyticCombinatorics/PartA/Ch2/Surjections.lean` and added it to the top-level `AnalyticCombinatorics.lean` imports.

Proved:

- `surjCount` by the requested inclusion-exclusion formula over `ℤ`.
- `surjCount_zero_right`: `surjCount n 0 = if n = 0 then 1 else 0`.
- `surjCount_zero_left`: `surjCount 0 k = if k = 0 then 1 else 0`.
- `surjCount_self`: `surjCount n n = n.factorial` (stronger than the requested `n ≥ 1` form).
- Stirling bridge:
  `surjCount_eq_factorial_mul_stirlingSecond (n k) :
    surjCount n k = ((k.factorial * Nat.stirlingSecond n k : ℕ) : ℤ)`.
- Concrete sanity values:
  - `surjCount 1 1 = 1`
  - `surjCount 2 1 = 1`
  - `surjCount 2 2 = 2`
  - `surjCount 3 2 = 6`
  - `surjCount 3 3 = 6`
  - `surjCount 4 2 = 14`
  - `surjCount 4 3 = 36`
- `surjCount_matches_example : surjCount 4 3 = 36`.
- EGF coefficient identity:
  `surjCount_egf_coeff (n k) :
    (surjCount n k : ℚ) / n.factorial =
      coeff n (((PowerSeries.exp ℚ) - 1) ^ k)`.
- `fubiniNumber` as `∑ k ∈ range (n + 1), surjCount n k`.
- Fubini sanity values `1, 1, 3, 13, 75` for `n = 0..4`.

Verification:

- `lake build AnalyticCombinatorics.PartA.Ch2.Surjections` passed before the final Stirling bridge was added.
- The final Stirling bridge proof was checked separately with `lake env lean --stdin` before patching it into the file.
- A subsequent `lake build AnalyticCombinatorics.PartA.Ch2.Surjections` retry hit a local `.lake`/Mathlib dependency rebuild problem (`Mathlib/Data/Prod/Basic.olean` missing) and then stalled in dependency rebuilding, with no Lean error from `Surjections.lean`.
