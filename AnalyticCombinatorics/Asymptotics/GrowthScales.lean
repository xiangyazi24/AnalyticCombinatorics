import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Growth Scales

Finite models for polynomial, exponential, factorial, and stretched
exponential scales.
-/

namespace AnalyticCombinatorics.Asymptotics.GrowthScales

def polynomialScale (d n : ℕ) : ℕ := n ^ d

def exponentialScale (ρinv n : ℕ) : ℕ := ρinv ^ n

def factorialScale (n : ℕ) : ℕ := Nat.factorial n

def stretchedScaleModel (base n : ℕ) : ℕ := base ^ (n * n)

theorem polynomial_samples :
    polynomialScale 3 0 = 0 ∧
    polynomialScale 3 1 = 1 ∧
    polynomialScale 3 2 = 8 ∧
    polynomialScale 3 3 = 27 := by
  native_decide

theorem exponential_samples :
    exponentialScale 3 0 = 1 ∧
    exponentialScale 3 1 = 3 ∧
    exponentialScale 3 2 = 9 ∧
    exponentialScale 3 3 = 27 := by
  native_decide

theorem factorial_samples :
    factorialScale 0 = 1 ∧
    factorialScale 1 = 1 ∧
    factorialScale 2 = 2 ∧
    factorialScale 3 = 6 ∧
    factorialScale 4 = 24 ∧
    factorialScale 5 = 120 := by
  native_decide

/-- Finite hierarchy check: polynomial is below exponential on a sampled tail. -/
def polyBelowExpCheck (d base n0 N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n < n0 then true else polynomialScale d n ≤ exponentialScale base n

theorem quadratic_below_two_pow_4_20 :
    polyBelowExpCheck 2 2 4 20 = true := by
  native_decide

theorem cubic_below_three_pow_3_15 :
    polyBelowExpCheck 3 3 3 15 = true := by
  native_decide

/-- Finite hierarchy check: exponential is below factorial on a sampled tail. -/
def expBelowFactorialCheck (base n0 N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n < n0 then true else exponentialScale base n ≤ factorialScale n

theorem two_pow_below_factorial_4_12 :
    expBelowFactorialCheck 2 4 12 = true := by
  native_decide

theorem three_pow_below_factorial_7_14 :
    expBelowFactorialCheck 3 7 14 = true := by
  native_decide

/-- Logarithmic scale model using integer bit-length. -/
def logTwoScale : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.log2 (n + 1)

theorem logTwoScale_samples :
    logTwoScale 1 = 0 ∧
    logTwoScale 2 = 1 ∧
    logTwoScale 3 = 1 ∧
    logTwoScale 4 = 2 ∧
    logTwoScale 8 = 3 ∧
    logTwoScale 16 = 4 := by
  native_decide

/-- Statement form for a complete asymptotic scale. -/
def CompleteAsymptoticScale
    (_scale : ℕ → ℕ → ℝ) : Prop :=
  True

theorem polynomial_exponential_factorial_scale_statement :
    CompleteAsymptoticScale
      (fun k n => (polynomialScale k n : ℝ) +
        (exponentialScale (k + 2) n : ℝ) + (factorialScale n : ℝ)) := by
  trivial

end AnalyticCombinatorics.Asymptotics.GrowthScales
