import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass

open Finset PowerSeries CombinatorialClass

/-- Inclusion-exclusion count of surjections from an `n`-set onto a `k`-set. -/
def surjCount (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (-1) ^ j * (k.choose j : ℤ) * ((k - j : ℤ) ^ n)

theorem surjCount_zero_right (n : ℕ) :
    surjCount n 0 = if n = 0 then 1 else 0 := by
  cases n <;> simp [surjCount]

theorem surjCount_zero_left (k : ℕ) :
    surjCount 0 k = if k = 0 then 1 else 0 := by
  rw [surjCount]
  simp only [pow_zero, mul_one]
  exact Int.alternating_sum_range_choose

example : surjCount 1 1 = 1 := by native_decide
example : surjCount 2 1 = 1 := by native_decide
example : surjCount 2 2 = 2 := by native_decide
example : surjCount 3 2 = 6 := by native_decide
example : surjCount 3 3 = 6 := by native_decide
example : surjCount 4 2 = 14 := by native_decide
example : surjCount 4 3 = 36 := by native_decide

theorem surjCount_matches_example : surjCount 4 3 = 36 := by native_decide

/-- Ordered Bell / Fubini number: total ordered set partitions of an `n`-set. -/
def fubiniNumber (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), surjCount n k

example : fubiniNumber 0 = 1 := by native_decide
example : fubiniNumber 1 = 1 := by native_decide
example : fubiniNumber 2 = 3 := by native_decide
example : fubiniNumber 3 = 13 := by native_decide
example : fubiniNumber 4 = 75 := by native_decide

