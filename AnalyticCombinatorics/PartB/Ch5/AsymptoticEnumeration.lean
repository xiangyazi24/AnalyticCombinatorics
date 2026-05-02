/-
  Analytic Combinatorics — Part B
  Chapter V — Asymptotic Enumeration

  Executable numerical checks for exponential growth rates, factorial bounds,
  central binomial asymptotics, Catalan subexponential factors, and
  partition function values.
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Combinatorics.Enumerative.Catalan

set_option linter.style.nativeDecide false

namespace AsymptoticEnumeration

open Finset

/-! ## 1. Ratio method for exponential growth (Fibonacci) -/

/-- The ratio `a(n+1)/a(n)` as a rational number, used to approximate
    the exponential growth rate of a sequence. -/
def ratioCheck (a : ℕ → ℕ) (n : ℕ) : ℚ := (a (n + 1) : ℚ) / (a n : ℚ)

/-- `Nat.fib 12 / Nat.fib 11 = 144 / 89`. -/
theorem ratioCheck_fib_11 : ratioCheck Nat.fib 11 = 144 / 89 := by native_decide

/-- The Fibonacci ratio at index 11 is less than 1.619 (cross-multiplied). -/
theorem fib_ratio_upper : 144 * 1000 < 89 * 1619 := by native_decide

/-- The Fibonacci ratio at index 11 is greater than 1.617 (cross-multiplied). -/
theorem fib_ratio_lower : 144 * 1000 > 89 * 1617 := by native_decide

/-! ## 2. Factorial bounds (Stirling consequences) -/

example : 2 ^ 10 < Nat.factorial 10 := by native_decide

example : Nat.factorial 10 < 10 ^ 7 := by native_decide

example : Nat.factorial 20 < 20 ^ 19 := by native_decide

/-! ## 3. Central binomial coefficient growth -/

/-- `Nat.choose 20 10 = 184756`. -/
theorem centralBinom_20 : Nat.choose 20 10 = 184756 := by native_decide

/-- Lower bound: `(choose 20 10)^2 * 32 < 4^20`, so `4^20 / (choose 20 10)^2 > 32`. -/
theorem centralBinom_sq_lower : (Nat.choose 20 10) ^ 2 * 32 < 4 ^ 20 := by native_decide

/-- Upper bound: `(choose 20 10)^2 * 33 > 4^20`, so `4^20 / (choose 20 10)^2 < 33`. -/
theorem centralBinom_sq_upper : (Nat.choose 20 10) ^ 2 * 33 > 4 ^ 20 := by native_decide

/-! ## 4. Catalan subexponential factor -/

/-- The Catalan number `C_n = binom(2n, n) / (n+1)`. -/
def catalanNum (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- `catalanNum` agrees with Mathlib's `catalan` for small values. -/
theorem catalanNum_eq_catalan_10 : catalanNum 10 = catalan 10 := by native_decide

/-- `C_10 = 16796`. -/
theorem catalan_10_val : catalanNum 10 = 16796 := by native_decide

/-- Catalan subexponential check: `C_10 * 11 * 4 < 4^11`.
    This witnesses `C_n * (n+1) < 4^n` scaled by 4. -/
theorem catalan_subexp_10 : catalanNum 10 * 11 * 4 < 4 ^ 11 := by native_decide

/-- Catalan subexponential check: `C_15 * 16 * 4 < 4^16`. -/
theorem catalan_subexp_15 : catalanNum 15 * 16 * 4 < 4 ^ 16 := by native_decide

/-! ## 5. Partition function (table-based) -/

/-- The integer partition function `p(n)`, defined by explicit table for small values.
    Values from OEIS A000041. -/
def partitionCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 7
  | 6 => 11
  | 7 => 15
  | 8 => 22
  | 9 => 30
  | 10 => 42
  | 11 => 56
  | 12 => 77
  | 13 => 101
  | 14 => 135
  | 15 => 176
  | 16 => 231
  | 17 => 297
  | 18 => 385
  | 19 => 490
  | 20 => 627
  | _ + 21 => 0  -- not defined beyond 20

theorem partitionCount_0 : partitionCount 0 = 1 := rfl
theorem partitionCount_1 : partitionCount 1 = 1 := rfl
theorem partitionCount_2 : partitionCount 2 = 2 := rfl
theorem partitionCount_3 : partitionCount 3 = 3 := rfl
theorem partitionCount_4 : partitionCount 4 = 5 := rfl
theorem partitionCount_5 : partitionCount 5 = 7 := rfl
theorem partitionCount_10 : partitionCount 10 = 42 := rfl
theorem partitionCount_20 : partitionCount 20 = 627 := rfl

/-- Partition growth: `p(20) > 2^9` (super-polynomial growth evidence). -/
theorem partition_growth_lower : partitionCount 20 > 2 ^ 9 := by native_decide

/-- Partition growth: `p(20) < 2^10`. -/
theorem partition_growth_upper : partitionCount 20 < 2 ^ 10 := by native_decide

end AsymptoticEnumeration
