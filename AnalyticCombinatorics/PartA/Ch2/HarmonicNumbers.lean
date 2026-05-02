import Mathlib.Tactic

open Finset

set_option linter.style.nativeDecide false

/-- Rational harmonic numbers `H_n = 1 + 1/2 + ... + 1/n`. -/
def harmonicNumber : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonicNumber n + 1 / (n + 1 : ℚ)

theorem harmonicNumber_one : harmonicNumber 1 = 1 := by
  native_decide

theorem harmonicNumber_two : harmonicNumber 2 = 3 / 2 := by
  native_decide

theorem harmonicNumber_three : harmonicNumber 3 = 11 / 6 := by
  native_decide

theorem harmonicNumber_four : harmonicNumber 4 = 25 / 12 := by
  native_decide

theorem harmonicNumber_five : harmonicNumber 5 = 137 / 60 := by
  native_decide

theorem harmonicNumber_six : harmonicNumber 6 = 49 / 20 := by
  native_decide

/-- Total number of cycles over all permutations of `n` labelled elements,
computed as `∑_{k=1}^n n! / k`. -/
def totalCyclesCount (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, n.factorial / (k + 1)

theorem totalCyclesCount_one :
    (totalCyclesCount 1 : ℚ) = (1).factorial * harmonicNumber 1 := by
  native_decide

theorem totalCyclesCount_two :
    (totalCyclesCount 2 : ℚ) = (2).factorial * harmonicNumber 2 := by
  native_decide

theorem totalCyclesCount_three :
    (totalCyclesCount 3 : ℚ) = (3).factorial * harmonicNumber 3 := by
  native_decide

theorem totalCyclesCount_four :
    (totalCyclesCount 4 : ℚ) = (4).factorial * harmonicNumber 4 := by
  native_decide

theorem totalCyclesCount_five :
    (totalCyclesCount 5 : ℚ) = (5).factorial * harmonicNumber 5 := by
  native_decide

theorem totalCyclesCount_six :
    (totalCyclesCount 6 : ℚ) = (6).factorial * harmonicNumber 6 := by
  native_decide

/-- Unsigned Stirling numbers of the first kind, counting permutations of `n`
labelled elements with exactly `k` cycles. -/
def unsignedStirling1 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * unsignedStirling1 n (k + 1) + unsignedStirling1 n k

theorem unsignedStirling1_zero_zero : unsignedStirling1 0 0 = 1 := by
  native_decide

theorem unsignedStirling1_zero_succ (k : ℕ) : unsignedStirling1 0 (k + 1) = 0 := by
  rfl

theorem unsignedStirling1_succ_zero (n : ℕ) : unsignedStirling1 (n + 1) 0 = 0 := by
  rfl

theorem unsignedStirling1_succ_succ (n k : ℕ) :
    unsignedStirling1 (n + 1) (k + 1) =
      n * unsignedStirling1 n (k + 1) + unsignedStirling1 n k := by
  rfl

theorem unsignedStirling1_three_one : unsignedStirling1 3 1 = 2 := by
  native_decide

theorem unsignedStirling1_three_two : unsignedStirling1 3 2 = 3 := by
  native_decide

theorem unsignedStirling1_three_three : unsignedStirling1 3 3 = 1 := by
  native_decide

theorem unsignedStirling1_four_one : unsignedStirling1 4 1 = 6 := by
  native_decide

theorem unsignedStirling1_four_two : unsignedStirling1 4 2 = 11 := by
  native_decide

theorem unsignedStirling1_four_three : unsignedStirling1 4 3 = 6 := by
  native_decide

theorem unsignedStirling1_four_four : unsignedStirling1 4 4 = 1 := by
  native_decide

theorem unsignedStirling1_row_sum_zero :
    ∑ k ∈ Finset.range (0 + 1), unsignedStirling1 0 k = (0).factorial := by
  native_decide

theorem unsignedStirling1_row_sum_one :
    ∑ k ∈ Finset.range (1 + 1), unsignedStirling1 1 k = (1).factorial := by
  native_decide

theorem unsignedStirling1_row_sum_two :
    ∑ k ∈ Finset.range (2 + 1), unsignedStirling1 2 k = (2).factorial := by
  native_decide

theorem unsignedStirling1_row_sum_three :
    ∑ k ∈ Finset.range (3 + 1), unsignedStirling1 3 k = (3).factorial := by
  native_decide

theorem unsignedStirling1_row_sum_four :
    ∑ k ∈ Finset.range (4 + 1), unsignedStirling1 4 k = (4).factorial := by
  native_decide

theorem unsignedStirling1_row_sum_five :
    ∑ k ∈ Finset.range (5 + 1), unsignedStirling1 5 k = (5).factorial := by
  native_decide

theorem unsignedStirling1_row_sum_six :
    ∑ k ∈ Finset.range (6 + 1), unsignedStirling1 6 k = (6).factorial := by
  native_decide
