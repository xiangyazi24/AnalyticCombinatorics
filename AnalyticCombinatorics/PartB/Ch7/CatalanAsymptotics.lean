/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Precise Catalan asymptotics, finite coefficient checks.

  The analytic statement `C_n ~ 4^n / (sqrt pi * n^(3/2))` is not proved here.
  This file records executable finite checks around the coefficient sequences
  and their expected exponential growth constants.
-/
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartA.Ch1.SchroederTheory
import AnalyticCombinatorics.PartB.Ch6.TransferTheorems

set_option linter.style.nativeDecide false

open TransferTheorems

open CombinatorialClass

/-! ## Catalan ratios -/

/-- The scaled Catalan ratio `C_n (n+1) / 4^n`, written in the requested form. -/
noncomputable def catalanRatio (n : ℕ) : ℚ :=
  ((binaryTreeClass.count n : ℚ) * (n + 1) * 4) / ((4 : ℚ) ^ (n + 1))

set_option linter.flexible false in
/-- Integer cross-multiplied monotonicity check for `catalanRatio`,
for `n = 1, ..., 12`. -/
theorem catalanRatio_cross_decreasing_1_12 :
    ∀ n ∈ Finset.Icc 1 12,
      binaryTreeClass.count (n + 1) * (n + 2) * 4 ^ n ≤
        binaryTreeClass.count n * (n + 1) * 4 ^ (n + 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> simp [TransferTheorems.catalan_formula] <;> native_decide

/-! ## Motzkin growth checks -/

/-- `M_n < 3^n` for `n = 1, ..., 12`. -/
theorem motzkinNumber_lt_three_pow_1_12 :
    ∀ n ∈ Finset.Icc 1 12, motzkinNumber n < 3 ^ n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

/-- The requested lower range `2^n < M_n` starting at `n = 4` is false. -/
theorem two_pow_lt_motzkinNumber_fails_at_4 :
    ¬ 2 ^ 4 < motzkinNumber 4 := by
  native_decide

/-- `2^n < M_n` for `n = 8, ..., 12`, where this lower check is true. -/
theorem two_pow_lt_motzkinNumber_8_12 :
    ∀ n ∈ Finset.Icc 8 12, 2 ^ n < motzkinNumber n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

/-- Statement form of the Motzkin exponential growth prediction. -/
def ch7_motzkinGrowthRateIsThree : Prop :=
  exponentialGrowthRate motzkinNumber = 3

/-! ## Schroeder growth checks -/

/-- `S_n < 6^n` for the large Schroeder numbers, `n = 1, ..., 8`. -/
theorem schroederCount_lt_six_pow_1_8 :
    ∀ n ∈ Finset.Icc 1 8, schroederCount n < 6 ^ n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide

/-- The requested lower range `5^n < S_n` starting at `n = 2` is false. -/
theorem five_pow_lt_schroederCount_fails_at_2 :
    ¬ 5 ^ 2 < schroederCount 2 := by
  native_decide

/-- Statement form of the large-Schroeder exponential growth prediction. -/
noncomputable def schroederGrowthRate : ℝ :=
  3 + 2 * Real.sqrt 2

/-- Statement form: large Schroeder numbers have growth rate `3 + 2 sqrt 2`. -/
def ch7_schroederGrowthRateIsThreePlusTwoSqrtTwo : Prop :=
  exponentialGrowthRate schroederCount = schroederGrowthRate

/-! ## Transfer-theorem coefficient checks -/

set_option linter.flexible false in
/-- The Catalan/tree identity behind the central binomial coefficient,
checked for `n = 0, ..., 12`. -/
theorem binaryTreeClass_count_mul_succ_eq_centralBinom_0_12 :
    ∀ n ∈ Finset.Icc 0 12,
      binaryTreeClass.count n * (n + 1) = (2 * n).choose n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> simp [TransferTheorems.catalan_formula] <;> native_decide

/-- Finite check of `(2n choose n)/(n+1) ≤ 4^n/(n+1)` for `n = 0, ..., 15`. -/
theorem centralBinom_div_succ_le_four_pow_div_succ_0_15 :
    ∀ n ∈ Finset.Icc 0 15,
      (2 * n).choose n / (n + 1) ≤ 4 ^ n / (n + 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  interval_cases n <;> native_decide
