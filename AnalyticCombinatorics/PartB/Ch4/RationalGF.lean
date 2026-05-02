/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Rational Generating Functions

  Lightweight coefficient checks for rational generating functions.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open PowerSeries

/-! ## Geometric series coefficients -/

/-- The explicitly constructed geometric series has coefficient `a^n`. -/
theorem geom_coeff (a : ℕ) (n : ℕ) :
    coeff n (PowerSeries.mk (fun n : ℕ => a ^ n) : PowerSeries ℕ) = a ^ n := by
  simp [PowerSeries.coeff_mk]

/-! ## Linear recurrences -/

/-- A sequence satisfies a homogeneous linear recurrence with the given coefficient list.

For `coeffs = [c₀, ..., cₖ₋₁]`, this says
`seq n = c₀ seq (n-1) + ... + cₖ₋₁ seq (n-k)` for all `n ≥ k`.
-/
def isLinearRecurrence (seq : ℕ → ℕ) (coeffs : List ℕ) : Prop :=
    ∀ n ≥ coeffs.length,
      seq n = ∑ i ∈ Finset.range coeffs.length,
        coeffs[i]! * seq (n - 1 - i)

/-- Boolean finite recurrence check used for executable sanity tests. -/
def linearRecurrenceCheckUpTo (N : ℕ) (seq : ℕ → ℕ) (coeffs : List ℕ) : Bool :=
    (List.range (N + 1)).all fun n =>
      if n < coeffs.length then
        true
      else
        seq n == ∑ i ∈ Finset.range coeffs.length,
          coeffs[i]! * seq (n - 1 - i)

/-- Finite version used for executable sanity checks. -/
def satisfiesLinearRecurrenceUpTo (N : ℕ) (seq : ℕ → ℕ) (coeffs : List ℕ) : Prop :=
    linearRecurrenceCheckUpTo N seq coeffs = true

/-- Fibonacci satisfies `Fₙ = Fₙ₋₁ + Fₙ₋₂` through `n = 20`, checked by computation. -/
theorem fibonacci_linear_recurrence_upto_20 :
    satisfiesLinearRecurrenceUpTo 20 Nat.fib [1, 1] := by
  change linearRecurrenceCheckUpTo 20 Nat.fib [1, 1] = true
  native_decide

/-! ## Small growth-bound checks -/

/-- A finite executable exponential growth bound. -/
def growthBoundCheckUpTo (N : ℕ) (seq : ℕ → ℕ) (C r : ℕ) : Bool :=
    (List.range (N + 1)).all fun n => seq n ≤ C * r ^ n

/-- A finite executable exponential growth bound. -/
def hasGrowthBoundUpTo (N : ℕ) (seq : ℕ → ℕ) (C r : ℕ) : Prop :=
    growthBoundCheckUpTo N seq C r = true

/-- The geometric sequence `3^n` is bounded by itself through `n = 20`. -/
theorem geometric_growth_bound_upto_20 :
    hasGrowthBoundUpTo 20 (fun n : ℕ => 3 ^ n) 1 3 := by
  change growthBoundCheckUpTo 20 (fun n : ℕ => 3 ^ n) 1 3 = true
  native_decide

/-- Fibonacci is below `2^n` through `n = 20`. -/
theorem fibonacci_growth_bound_upto_20 :
    hasGrowthBoundUpTo 20 Nat.fib 1 2 := by
  change growthBoundCheckUpTo 20 Nat.fib 1 2 = true
  native_decide
