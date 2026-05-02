/-
  Analytic Combinatorics — Part B
  Chapter IX — Depoissonization: combinatorial identities and finite checks.

  This module formalizes basic combinatorial quantities relevant to
  depoissonization arguments in Chapter IX: partial sums of the exponential
  series, the birthday problem (no-collision probability), Stirling numbers
  of the second kind, Bell numbers, and expected empty bins in hashing.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset

namespace Depoissonization

/-! ## Partial sums of the exponential series -/

/-- Partial sum of the exponential series: ∑_{k=0}^{n} 1/k! -/
def expPartialSum (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), 1 / (Nat.factorial k : ℚ)

theorem expPartialSum_zero : expPartialSum 0 = 1 := by native_decide

theorem expPartialSum_one : expPartialSum 1 = 2 := by native_decide

theorem expPartialSum_two : expPartialSum 2 = 5 / 2 := by native_decide

theorem expPartialSum_three : expPartialSum 3 = 8 / 3 := by native_decide

theorem expPartialSum_four : expPartialSum 4 = 65 / 24 := by native_decide

theorem expPartialSum_five : expPartialSum 5 = 163 / 60 := by native_decide

/-! ## Birthday problem (no-collision probability) -/

/-- Probability that k items placed in n bins have no collisions. -/
def birthdayNoColl (n k : ℕ) : ℚ :=
  if k = 0 then 1
  else if k > n then 0
  else ∏ i ∈ Finset.range k, ((n - i : ℤ) : ℚ) / (n : ℚ)

theorem birthdayNoColl_4_2 : birthdayNoColl 4 2 = 3 / 4 := by native_decide

theorem birthdayNoColl_4_3 : birthdayNoColl 4 3 = 3 / 8 := by native_decide

theorem birthdayNoColl_6_3 : birthdayNoColl 6 3 = 5 / 9 := by native_decide

/-! ## Stirling numbers of the second kind -/

/-- Stirling number of the second kind S(n, k). -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

theorem stirling2_3_2 : stirling2 3 2 = 3 := by native_decide

theorem stirling2_4_2 : stirling2 4 2 = 7 := by native_decide

theorem stirling2_5_2 : stirling2 5 2 = 15 := by native_decide

theorem stirling2_5_3 : stirling2 5 3 = 25 := by native_decide

theorem stirling2_5_4 : stirling2 5 4 = 10 := by native_decide

theorem stirling2_5_5 : stirling2 5 5 = 1 := by native_decide

/-! ## Bell numbers -/

/-- Bell number B(n), the total number of set partitions of an n-element set. -/
def bellFromStirling (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), stirling2 n k

theorem bellFromStirling_zero : bellFromStirling 0 = 1 := by native_decide

theorem bellFromStirling_one : bellFromStirling 1 = 1 := by native_decide

theorem bellFromStirling_two : bellFromStirling 2 = 2 := by native_decide

theorem bellFromStirling_three : bellFromStirling 3 = 5 := by native_decide

theorem bellFromStirling_four : bellFromStirling 4 = 15 := by native_decide

theorem bellFromStirling_five : bellFromStirling 5 = 52 := by native_decide

/-! ## Expected empty bins (hashing model) -/

/-- Numerator of the expected number of empty bins: m * (m-1)^n. -/
def expectedEmptyNumer (m n : ℕ) : ℕ := m * (m - 1) ^ n

/-- Denominator of the expected number of empty bins: m^n. -/
def expectedEmptyDenom (m n : ℕ) : ℕ := m ^ n

theorem expectedEmptyNumer_10_5 : expectedEmptyNumer 10 5 = 590490 := by native_decide

theorem expectedEmptyDenom_10_5 : expectedEmptyDenom 10 5 = 100000 := by native_decide

end Depoissonization
