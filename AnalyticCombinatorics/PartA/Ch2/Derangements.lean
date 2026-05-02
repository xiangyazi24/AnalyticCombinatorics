import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open Finset

set_option linter.style.nativeDecide false

/-- Derangement numbers, with the standard two-term recurrence. -/
def derangeCount : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | (n + 2) => (n + 1) * (derangeCount (n + 1) + derangeCount n)

theorem derangeCount_zero : derangeCount 0 = 1 := by
  native_decide

theorem derangeCount_one : derangeCount 1 = 0 := by
  native_decide

theorem derangeCount_two : derangeCount 2 = 1 := by
  native_decide

theorem derangeCount_three : derangeCount 3 = 2 := by
  native_decide

theorem derangeCount_four : derangeCount 4 = 9 := by
  native_decide

theorem derangeCount_five : derangeCount 5 = 44 := by
  native_decide

/-- Standalone form of the derangement recurrence. -/
theorem derangeCount_rec (n : ℕ) :
    derangeCount (n + 2) = (n + 1) * (derangeCount (n + 1) + derangeCount n) := by
  rfl

/-- Checked instances, for `n = 0, ..., 8`, of the labelled SET-star identity
for permutations:

`n! = ∑_{k=0}^n (n choose k) D_{n-k}`.
-/
theorem perm_eq_set_star_derange (n : ℕ) (hn : n ≤ 8) :
    n.factorial = ∑ k ∈ Finset.range (n + 1), n.choose k * derangeCount (n - k) := by
  interval_cases n <;> native_decide

