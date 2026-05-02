import Mathlib.Tactic

open Finset

set_option linter.style.nativeDecide false

/-- Bell numbers, defined by the standard binomial recurrence. -/
def bellCount : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k ∈ (Finset.range (n + 1)).attach, Nat.choose n k.val * bellCount k.val
termination_by n => n
decreasing_by
  exact Nat.lt_succ_iff.mp (Nat.succ_lt_succ (Finset.mem_range.mp k.2))

/-- Standalone form of the Bell-number recurrence. -/
theorem bellCount_rec (n : ℕ) :
    bellCount (n + 1) =
      ∑ k ∈ Finset.range (n + 1), Nat.choose n k * bellCount k := by
  rw [bellCount]
  exact Finset.sum_attach (Finset.range (n + 1)) fun k => Nat.choose n k * bellCount k

theorem bellCount_zero : bellCount 0 = 1 := by
  native_decide

theorem bellCount_one : bellCount 1 = 1 := by
  native_decide

theorem bellCount_two : bellCount 2 = 2 := by
  native_decide

theorem bellCount_three : bellCount 3 = 5 := by
  native_decide

theorem bellCount_four : bellCount 4 = 15 := by
  native_decide

theorem bellCount_five : bellCount 5 = 52 := by
  native_decide

theorem bellCount_six : bellCount 6 = 203 := by
  native_decide

/-- Stirling numbers of the second kind, by their standard recurrence. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)

theorem bellCount_eq_sum_stirling2_zero :
    bellCount 0 = ∑ k ∈ Finset.range (0 + 1), stirling2 0 k := by
  native_decide

theorem bellCount_eq_sum_stirling2_one :
    bellCount 1 = ∑ k ∈ Finset.range (1 + 1), stirling2 1 k := by
  native_decide

theorem bellCount_eq_sum_stirling2_two :
    bellCount 2 = ∑ k ∈ Finset.range (2 + 1), stirling2 2 k := by
  native_decide

theorem bellCount_eq_sum_stirling2_three :
    bellCount 3 = ∑ k ∈ Finset.range (3 + 1), stirling2 3 k := by
  native_decide

theorem bellCount_eq_sum_stirling2_four :
    bellCount 4 = ∑ k ∈ Finset.range (4 + 1), stirling2 4 k := by
  native_decide

theorem bellCount_eq_sum_stirling2_five :
    bellCount 5 = ∑ k ∈ Finset.range (5 + 1), stirling2 5 k := by
  native_decide

theorem bellCount_eq_sum_stirling2_six :
    bellCount 6 = ∑ k ∈ Finset.range (6 + 1), stirling2 6 k := by
  native_decide

/-- Checked instances, for `n = 0, ..., 6`, of `B_n = ∑_k S(n,k)`. -/
theorem bellCount_eq_sum_stirling2_upto_six (n : ℕ) (hn : n ≤ 6) :
    bellCount n = ∑ k ∈ Finset.range (n + 1), stirling2 n k := by
  interval_cases n <;> native_decide
