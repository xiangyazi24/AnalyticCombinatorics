import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch2.Derangements

open Finset

set_option linter.style.nativeDecide false

/-- Unsigned Stirling numbers of the first kind:
permutations of `n` labelled elements with exactly `k` cycles. -/
def cycleTypeCount : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * cycleTypeCount n (k + 1) + cycleTypeCount n k

theorem cycleTypeCount_zero_zero : cycleTypeCount 0 0 = 1 := by
  native_decide

theorem cycleTypeCount_zero_succ (k : ℕ) : cycleTypeCount 0 (k + 1) = 0 := by
  rfl

theorem cycleTypeCount_succ_zero (n : ℕ) : cycleTypeCount (n + 1) 0 = 0 := by
  rfl

/-- The standard Stirling-first recurrence, with the cycle count written as a successor. -/
theorem cycleTypeCount_succ_succ (n k : ℕ) :
    cycleTypeCount (n + 1) (k + 1) =
      n * cycleTypeCount n (k + 1) + cycleTypeCount n k := by
  rfl

/-- The standard Stirling-first recurrence, for nonzero cycle count. -/
theorem cycleTypeCount_succ_left (n k : ℕ) (hk : k ≠ 0) :
    cycleTypeCount (n + 1) k =
      n * cycleTypeCount n k + cycleTypeCount n (k - 1) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hk)
  rfl

theorem cycleTypeCount_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → cycleTypeCount n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => by rfl
  | n + 1, k + 1, hk => by
      rw [cycleTypeCount_succ_succ,
        cycleTypeCount_eq_zero_of_lt (Nat.lt_of_succ_lt_succ hk),
        cycleTypeCount_eq_zero_of_lt (Nat.lt_of_succ_lt hk), mul_zero]

theorem cycleTypeCount_self (n : ℕ) : cycleTypeCount n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [cycleTypeCount_succ_succ, ih,
        cycleTypeCount_eq_zero_of_lt (Nat.lt_succ_self n), mul_zero]

theorem cycleTypeCount_three_one : cycleTypeCount 3 1 = 2 := by native_decide
theorem cycleTypeCount_three_two : cycleTypeCount 3 2 = 3 := by native_decide
theorem cycleTypeCount_three_three : cycleTypeCount 3 3 = 1 := by native_decide

theorem cycleTypeCount_four_one : cycleTypeCount 4 1 = 6 := by native_decide
theorem cycleTypeCount_four_two : cycleTypeCount 4 2 = 11 := by native_decide
theorem cycleTypeCount_four_three : cycleTypeCount 4 3 = 6 := by native_decide
theorem cycleTypeCount_four_four : cycleTypeCount 4 4 = 1 := by native_decide

private lemma cycleTypeCount_shifted_row_sum (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range (n + 1), cycleTypeCount n (k + 1)) =
      ∑ k ∈ Finset.range (n + 1), cycleTypeCount n k := by
  cases n with
  | zero => omega
  | succ n =>
      calc
        (∑ k ∈ Finset.range (n + 1 + 1), cycleTypeCount (n + 1) (k + 1))
            = ∑ k ∈ Finset.range (n + 1), cycleTypeCount (n + 1) (k + 1) := by
              rw [Finset.sum_range_succ]
              rw [cycleTypeCount_eq_zero_of_lt (Nat.lt_succ_self (n + 1))]
              simp
        _ = cycleTypeCount (n + 1) 0 +
              ∑ k ∈ Finset.range (n + 1), cycleTypeCount (n + 1) (k + 1) := by
              rw [cycleTypeCount_succ_zero n]
              simp
        _ = (∑ k ∈ Finset.range (n + 1), cycleTypeCount (n + 1) (k + 1)) +
              cycleTypeCount (n + 1) 0 := by
              rw [Nat.add_comm]
        _ = ∑ k ∈ Finset.range (n + 1 + 1), cycleTypeCount (n + 1) k := by
              exact (Finset.sum_range_succ'
                (fun k => cycleTypeCount (n + 1) k) (n + 1)).symm

/-- Row sums of unsigned Stirling numbers of the first kind give `n!`. -/
theorem stirling1_row_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), cycleTypeCount n k = n.factorial := by
  induction n with
  | zero =>
      native_decide
  | succ n ih =>
      cases n with
      | zero =>
          native_decide
      | succ n =>
          calc
            (∑ k ∈ Finset.range (n + 1 + 1 + 1), cycleTypeCount (n + 1 + 1) k)
                = ∑ k ∈ Finset.range (n + 1 + 1),
                    cycleTypeCount (n + 1 + 1) (k + 1) := by
                  rw [Finset.sum_range_succ']
                  rw [cycleTypeCount_succ_zero (n + 1)]
                  simp
            _ = ∑ k ∈ Finset.range (n + 1 + 1),
                    ((n + 1) * cycleTypeCount (n + 1) (k + 1) +
                      cycleTypeCount (n + 1) k) := by
                  apply Finset.sum_congr rfl
                  intro k _hk
                  rw [cycleTypeCount_succ_succ]
            _ = (n + 1) * (∑ k ∈ Finset.range (n + 1 + 1),
                    cycleTypeCount (n + 1) (k + 1)) +
                  ∑ k ∈ Finset.range (n + 1 + 1), cycleTypeCount (n + 1) k := by
                  rw [Finset.sum_add_distrib, Finset.mul_sum]
            _ = (n + 1) * (∑ k ∈ Finset.range (n + 1 + 1),
                    cycleTypeCount (n + 1) k) +
                  ∑ k ∈ Finset.range (n + 1 + 1), cycleTypeCount (n + 1) k := by
                  rw [cycleTypeCount_shifted_row_sum (n + 1) (Nat.succ_pos n)]
            _ = (n + 1 + 1) * (n + 1).factorial := by
                  rw [ih]
                  ring_nf
            _ = (n + 1 + 1).factorial := by
                  exact (Nat.factorial_succ (n + 1)).symm

theorem cycleTypeCount_row_sum_one :
    ∑ k ∈ Finset.range (1 + 1), cycleTypeCount 1 k = (1).factorial := by native_decide
theorem cycleTypeCount_row_sum_two :
    ∑ k ∈ Finset.range (2 + 1), cycleTypeCount 2 k = (2).factorial := by native_decide
theorem cycleTypeCount_row_sum_three :
    ∑ k ∈ Finset.range (3 + 1), cycleTypeCount 3 k = (3).factorial := by native_decide
theorem cycleTypeCount_row_sum_four :
    ∑ k ∈ Finset.range (4 + 1), cycleTypeCount 4 k = (4).factorial := by native_decide
theorem cycleTypeCount_row_sum_five :
    ∑ k ∈ Finset.range (5 + 1), cycleTypeCount 5 k = (5).factorial := by native_decide
theorem cycleTypeCount_row_sum_six :
    ∑ k ∈ Finset.range (6 + 1), cycleTypeCount 6 k = (6).factorial := by native_decide

/-- Checked instances of `stirling1_row_sum`, for `n = 0, ..., 8`. -/
theorem stirling1_row_sum_checked (n : ℕ) (hn : n ≤ 8) :
    ∑ k ∈ Finset.range (n + 1), cycleTypeCount n k = n.factorial := by
  interval_cases n <;> native_decide

/-- Inclusion-exclusion count of permutations with no fixed points. -/
def fixedPointZeroPermCount (n : ℕ) : ℕ :=
  Int.toNat
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ j * (n.choose j : ℤ) * ((n - j).factorial : ℤ))

/-- Checked instances, for `n = 0, ..., 6`, of derangements as permutations
with zero fixed points. -/
theorem derangeCount_eq_fixed_point_zero (n : ℕ) (hn : n ≤ 6) :
    derangeCount n = fixedPointZeroPermCount n := by
  interval_cases n <;> native_decide
