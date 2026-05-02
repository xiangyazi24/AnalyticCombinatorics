/-
  Analytic Combinatorics -- Part A: Symbolic Method
  Chapter II: Parking functions and their Cayley-tree count.

  This file records the standard count of parking functions of length `n`,
      (n + 1)^(n - 1),
  together with its relation to the rooted Cayley count in
  `LabelledTrees.lean`.
-/
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch2.LabelledTrees

set_option linter.style.show false
set_option linter.style.nativeDecide false

namespace ParkingFunctions

/-- Number of parking functions of length `n`.

The formula also gives the conventional empty count:
`parkingFunctionCount 0 = 1`, since natural subtraction makes
`0 - 1 = 0`. -/
def parkingFunctionCount (n : ℕ) : ℕ :=
  (n + 1) ^ (n - 1)

theorem parkingFunctionCount_zero : parkingFunctionCount 0 = 1 := by
  native_decide

theorem parkingFunctionCount_eq_pow (n : ℕ) :
    parkingFunctionCount n = (n + 1) ^ (n - 1) := by
  rfl

/-- Rooted Cayley trees on `n + 1` vertices are parking functions with one
distinguished extra root choice. -/
theorem cayleyCount_succ_eq_mul_parkingFunctionCount (n : ℕ) :
    cayleyCount (n + 1) = (n + 1) * parkingFunctionCount n := by
  rw [cayleyCount_eq_pow (n + 1) (Nat.succ_pos n), parkingFunctionCount]
  cases n with
  | zero => norm_num
  | succ n =>
      have hsub : n + 1 + 1 - 1 = n + 1 := by omega
      have hsub' : n + 1 - 1 = n := by omega
      rw [hsub, hsub', pow_succ]
      rw [Nat.mul_comm]

/-- Equivalently, parking functions are the rooted Cayley count divided by
the `n + 1` choices of the extra root. -/
theorem parkingFunctionCount_eq_cayleyCount_succ_div (n : ℕ) :
    parkingFunctionCount n = cayleyCount (n + 1) / (n + 1) := by
  rw [cayleyCount_succ_eq_mul_parkingFunctionCount]
  exact Eq.symm (Nat.mul_div_right _ (Nat.succ_pos n))

/-- Checked Cayley connection for `n = 1, ..., 8`. -/
theorem parkingFunctionCount_eq_cayleyQuotient_checked (n : ℕ)
    (hn₁ : 1 ≤ n) (hn₂ : n ≤ 8) :
    parkingFunctionCount n = cayleyCount (n + 1) / (n + 1) := by
  interval_cases n <;> native_decide

theorem parkingFunctionCount_one : parkingFunctionCount 1 = 1 := by native_decide
theorem parkingFunctionCount_two : parkingFunctionCount 2 = 3 := by native_decide
theorem parkingFunctionCount_three : parkingFunctionCount 3 = 16 := by native_decide
theorem parkingFunctionCount_four : parkingFunctionCount 4 = 125 := by native_decide
theorem parkingFunctionCount_five : parkingFunctionCount 5 = 1296 := by native_decide

example : parkingFunctionCount 6 = 16807 := by native_decide
example : parkingFunctionCount 7 = 262144 := by native_decide
example : parkingFunctionCount 8 = 4782969 := by native_decide

/-- Ballot-problem count in the strict-lead two-candidate case, using the
standard integer form of `(n - k)/(n + k) * choose (n + k) k` for `n > k`. -/
def ballotCount (n k : ℕ) : ℕ :=
  if k < n then ((n - k) * (n + k).choose k) / (n + k) else 0

example : ballotCount 1 0 = 1 := by native_decide
example : ballotCount 2 1 = 1 := by native_decide
example : ballotCount 3 1 = 2 := by native_decide
example : ballotCount 3 2 = 2 := by native_decide
example : ballotCount 4 2 = 5 := by native_decide
example : ballotCount 4 3 = 5 := by native_decide
example : ballotCount 2 2 = 0 := by native_decide

end ParkingFunctions
