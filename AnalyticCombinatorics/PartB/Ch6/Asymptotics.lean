/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Standard scales and finite transfer checks.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartB.Ch6.TransferTheorems

set_option linter.style.nativeDecide false

open PowerSeries CombinatorialClass TransferTheorems

/-! ## Standard function scale -/

/-- Coefficients of the algebraic standard scale `(1 - z)^{-α}`,
represented by the rising factorial `(α)_n / n!`. -/
def standardScaleCoeff (α : ℚ) (n : ℕ) : ℚ :=
  (∏ k ∈ Finset.range n, (α + (k : ℚ))) / (n.factorial : ℚ)

/-- Integer-parameter sanity checks for `(1 - z)^{-1}`. -/
theorem standardScaleCoeff_one_samples :
    standardScaleCoeff 1 0 = 1 ∧
    standardScaleCoeff 1 1 = 1 ∧
    standardScaleCoeff 1 2 = 1 ∧
    standardScaleCoeff 1 3 = 1 ∧
    standardScaleCoeff 1 4 = 1 ∧
    standardScaleCoeff 1 5 = 1 := by
  sorry

/-- Integer-parameter sanity checks for `(1 - z)^{-2}`. -/
theorem standardScaleCoeff_two_samples :
    standardScaleCoeff 2 0 = 1 ∧
    standardScaleCoeff 2 1 = 2 ∧
    standardScaleCoeff 2 2 = 3 ∧
    standardScaleCoeff 2 3 = 4 ∧
    standardScaleCoeff 2 4 = 5 ∧
    standardScaleCoeff 2 5 = 6 := by
  sorry

/-- Integer-parameter sanity checks for `(1 - z)^{-3}`. -/
theorem standardScaleCoeff_three_samples :
    standardScaleCoeff 3 0 = 1 ∧
    standardScaleCoeff 3 1 = 3 ∧
    standardScaleCoeff 3 2 = 6 ∧
    standardScaleCoeff 3 3 = 10 ∧
    standardScaleCoeff 3 4 = 15 ∧
    standardScaleCoeff 3 5 = 21 := by
  sorry

/-! ## Geometric scale -/

/-- Coefficient sequence of `1 / (1 - ρz)`. -/
def geomCoeff (ρ : ℕ) (n : ℕ) : ℕ := ρ ^ n

private def geomSeriesQ (ρ : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((geomCoeff ρ n : ℕ) : ℚ)

private theorem geomSeriesQ_mul_one_sub (ρ : ℕ) :
    geomSeriesQ ρ * (1 - C (ρ : ℚ) * X) = 1 := by
  ext n
  rw [mul_sub, mul_one]
  cases n with
  | zero =>
      simp [geomSeriesQ, geomCoeff]
  | succ n =>
      rw [← mul_assoc]
      simp only [map_sub, coeff_succ_mul_X, coeff_one, Nat.succ_ne_zero,
        ↓reduceIte]
      rw [coeff_mul_C]
      simp [geomSeriesQ, geomCoeff, pow_succ]

/-- In `ℚ[[X]]`, the coefficient of `X^n` in `(1 - ρX)^{-1}` is `ρ^n`. -/
theorem geomCoeff_powerSeries (ρ n : ℕ) :
    coeff n (((1 - C (ρ : ℚ) * X : PowerSeries ℚ)⁻¹)) = (geomCoeff ρ n : ℚ) := by
  have hconst : PowerSeries.constantCoeff (1 - C (ρ : ℚ) * X : PowerSeries ℚ) ≠ 0 := by
    simp
  have hseries :
      ((1 - C (ρ : ℚ) * X : PowerSeries ℚ)⁻¹) = geomSeriesQ ρ := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one hconst]
    exact geomSeriesQ_mul_one_sub ρ
  rw [hseries]
  simp [geomSeriesQ, geomCoeff]

/-! ## Catalan asymptotic statements and finite checks -/

/-- Statement form of the Catalan exponential asymptotic order. -/
def catalanAsymptotics : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N < n →
    ((4 : ℚ) - ε) ^ n < (binaryTreeClass.count n : ℚ) ∧
      (binaryTreeClass.count n : ℚ) < ((4 : ℚ) + ε) ^ n

/-- The Catalan ratios `C_{n+1}/C_n`, for `n = 5, ..., 10`, lie between `3` and `5`. -/
theorem catalan_ratio_between_three_and_five_5_10 :
    3 * binaryTreeClass.count 5 < binaryTreeClass.count 6 ∧
    binaryTreeClass.count 6 < 5 * binaryTreeClass.count 5 ∧
    3 * binaryTreeClass.count 6 < binaryTreeClass.count 7 ∧
    binaryTreeClass.count 7 < 5 * binaryTreeClass.count 6 ∧
    3 * binaryTreeClass.count 7 < binaryTreeClass.count 8 ∧
    binaryTreeClass.count 8 < 5 * binaryTreeClass.count 7 ∧
    3 * binaryTreeClass.count 8 < binaryTreeClass.count 9 ∧
    binaryTreeClass.count 9 < 5 * binaryTreeClass.count 8 ∧
    3 * binaryTreeClass.count 9 < binaryTreeClass.count 10 ∧
    binaryTreeClass.count 10 < 5 * binaryTreeClass.count 9 ∧
    3 * binaryTreeClass.count 10 < binaryTreeClass.count 11 ∧
    binaryTreeClass.count 11 < 5 * binaryTreeClass.count 10 := by
  repeat rw [catalan_formula]
  sorry

/-- `C_n < 4^n` for `n = 1, ..., 15`. -/
theorem catalan_below_four_pow_1_15 :
    binaryTreeClass.count 1 < 4 ^ 1 ∧
    binaryTreeClass.count 2 < 4 ^ 2 ∧
    binaryTreeClass.count 3 < 4 ^ 3 ∧
    binaryTreeClass.count 4 < 4 ^ 4 ∧
    binaryTreeClass.count 5 < 4 ^ 5 ∧
    binaryTreeClass.count 6 < 4 ^ 6 ∧
    binaryTreeClass.count 7 < 4 ^ 7 ∧
    binaryTreeClass.count 8 < 4 ^ 8 ∧
    binaryTreeClass.count 9 < 4 ^ 9 ∧
    binaryTreeClass.count 10 < 4 ^ 10 ∧
    binaryTreeClass.count 11 < 4 ^ 11 ∧
    binaryTreeClass.count 12 < 4 ^ 12 ∧
    binaryTreeClass.count 13 < 4 ^ 13 ∧
    binaryTreeClass.count 14 < 4 ^ 14 ∧
    binaryTreeClass.count 15 < 4 ^ 15 := by
  repeat rw [catalan_formula]
  sorry

/-- The requested lower check `3^n < C_n` over `n = 5, ..., 15` is false already at `n = 5`. -/
theorem catalan_three_pow_lower_fails_at_5 :
    ¬ 3 ^ 5 < binaryTreeClass.count 5 := by
  sorry

/-! ## Exponential order predicate -/

/-- A sequence has exponential order `ρ` if it is eventually squeezed between
`(ρ - ε)^n` and `(ρ + ε)^n` for every positive rational `ε`. -/
def IsExponentialOrder (f : ℕ → ℕ) (ρ : ℕ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N < n →
    ((ρ : ℚ) - ε) ^ n < (f n : ℚ) ∧ (f n : ℚ) < ((ρ : ℚ) + ε) ^ n

/-- Statement form of Catalan exponential order. -/
def catalanIsExponentialOrderFour : Prop :=
  IsExponentialOrder binaryTreeClass.count 4
