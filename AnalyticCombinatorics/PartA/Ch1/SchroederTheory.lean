/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I: Large Schroeder numbers.

  The ordinary generating function `S(z)` for the large Schroeder numbers
  satisfies

      S(z) = 1 + z * S(z) + z * S(z)^2.

  This file records the corresponding coefficient recursion and the first
  values.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

open Finset PowerSeries

set_option linter.style.nativeDecide false
set_option linter.style.show false

/-- Large Schroeder numbers, starting `1, 2, 6, 22, 90, ...`. -/
def schroederCount : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      schroederCount n +
        ∑ i : (Finset.range (n + 1) : Set ℕ),
          schroederCount i.1 * schroederCount (n - i.1)
termination_by n => n
decreasing_by
  all_goals simp_wf
  all_goals
    try
      have hi := Finset.mem_range.mp (show i.1 ∈ Finset.range (n + 1) from i.2)
    omega

/-- The defining coefficient recursion for the large Schroeder numbers. -/
theorem schroederCount_succ (n : ℕ) :
    schroederCount (n + 1) =
      schroederCount n +
        ∑ i ∈ Finset.range (n + 1), schroederCount i * schroederCount (n - i) := by
  rw [schroederCount]
  congr 1
  exact Finset.sum_coe_sort (s := Finset.range (n + 1))
    (f := fun i : ℕ => schroederCount i * schroederCount (n - i))

/-! ## Sanity checks -/

theorem schroederCount_zero : schroederCount 0 = 1 := by native_decide
theorem schroederCount_one : schroederCount 1 = 2 := by native_decide
theorem schroederCount_two : schroederCount 2 = 6 := by native_decide
theorem schroederCount_three : schroederCount 3 = 22 := by native_decide
theorem schroederCount_four : schroederCount 4 = 90 := by native_decide

/-- OGF for the large Schroeder numbers. -/
noncomputable def schroederOGF : PowerSeries ℕ := fun s => schroederCount (s ())

theorem coeff_schroederOGF (n : ℕ) : coeff n schroederOGF = schroederCount n := by
  change schroederCount ((Finsupp.single () n) ()) = schroederCount n
  simp [Finsupp.single_eq_same]

/-- The quadratic OGF equation `S = 1 + z*S + z*S^2`. -/
theorem schroederOGF_eq :
    schroederOGF = 1 + PowerSeries.X * schroederOGF + PowerSeries.X * schroederOGF ^ 2 := by
  ext n
  cases n with
  | zero =>
      rw [coeff_schroederOGF, schroederCount_zero]
      simp
  | succ n =>
      have hX : coeff (n + 1) (PowerSeries.X * schroederOGF) = schroederCount n := by
        rw [PowerSeries.coeff_succ_X_mul, coeff_schroederOGF]
      have hX2 : coeff (n + 1) (PowerSeries.X * schroederOGF ^ 2) =
          ∑ i ∈ Finset.range (n + 1), schroederCount i * schroederCount (n - i) := by
        rw [PowerSeries.coeff_succ_X_mul, pow_two, coeff_mul]
        simp only [coeff_schroederOGF]
        exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => schroederCount i * schroederCount j) n
      rw [coeff_schroederOGF, schroederCount_succ n]
      simp [map_add, hX, hX2]
