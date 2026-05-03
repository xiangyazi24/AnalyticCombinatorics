import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticMethods

/-! # Analytic Methods: Finite Power-Sum Checks

Numerical checks for classical power-sum and geometric-sum identities used in
analytic combinatorics.  Tables store the finite initial sequences, and the
formulas are verified over the listed ranges.
-/

/-! ## 1. Bernoulli-Motivated Power Sums

Bernoulli numbers appear in closed forms for sums of powers.  To avoid rational
Bernoulli values, we verify the corresponding integer-scaled identities.
-/

/-- Sum of first `n` squares for `n = 1..10`. -/
def sumSq : Fin 10 → ℕ := ![1, 5, 14, 30, 55, 91, 140, 204, 285, 385]

/-- `1^2 + ... + n^2 = n(n+1)(2n+1)/6`, checked for `n = 1..10`. -/
example : ∀ i : Fin 10,
    6 * sumSq i =
      ((i : ℕ) + 1) * (((i : ℕ) + 1) + 1) * (2 * ((i : ℕ) + 1) + 1) := by
  native_decide

/-! ## 2. Sum of Cubes -/

/-- Sum of first `n` cubes for `n = 1..8`. -/
def sumCubes : Fin 8 → ℕ := ![1, 9, 36, 100, 225, 441, 784, 1296]

/-- `1^3 + ... + n^3 = (n(n+1)/2)^2`, checked for `n = 1..8`. -/
example : ∀ i : Fin 8,
    4 * sumCubes i = ((i : ℕ) + 1) ^ 2 * (((i : ℕ) + 1) + 1) ^ 2 := by
  native_decide

/-! ## 3. Sum of Fourth Powers -/

/-- Sum of first `n` fourth powers for `n = 1..6`. -/
def sumFourth : Fin 6 → ℕ := ![1, 17, 98, 354, 979, 2275]

/-- `1^4 + ... + n^4 = n(n+1)(2n+1)(3n^2+3n-1)/30`, checked for `n = 1..6`. -/
example : ∀ i : Fin 6,
    30 * sumFourth i =
      ((i : ℕ) + 1) * (((i : ℕ) + 1) + 1) * (2 * ((i : ℕ) + 1) + 1) *
        (3 * ((i : ℕ) + 1) ^ 2 + 3 * ((i : ℕ) + 1) - 1) := by
  native_decide

/-! ## 4. Geometric Sums -/

/-- Geometric sums `1 + 2 + ... + 2^n` for `n = 0..6`. -/
def geomSumTwo : Fin 7 → ℕ := ![1, 3, 7, 15, 31, 63, 127]

/-- For `r = 2`, `(r - 1) * geomSum = r^(n+1) - 1`, checked as `value + 1 = 2^(n+1)`. -/
example : ∀ i : Fin 7, geomSumTwo i + 1 = 2 ^ ((i : ℕ) + 1) := by
  native_decide

/-! ## 5. Triangular Numbers -/

/-- Triangular numbers `1 + 2 + ... + n` for `n = 1..12`. -/
def triangular : Fin 12 → ℕ := ![1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78]

/-- `1 + 2 + ... + n = n(n+1)/2`, checked for `n = 1..12`. -/
example : ∀ i : Fin 12,
    2 * triangular i = ((i : ℕ) + 1) * (((i : ℕ) + 1) + 1) := by
  native_decide

/-! ## 6. Alternating Sums -/

/-- Alternating sums `1 - 2 + 3 - ... + n` for odd `n = 1, 3, 5, 7, 9`. -/
def oddAltSum : Fin 5 → ℕ := ![1, 2, 3, 4, 5]

/-- For odd `n = 2k + 1`, the alternating sum is `k + 1`. -/
example : ∀ k : Fin 5, oddAltSum k = (k : ℕ) + 1 := by
  native_decide

end AnalyticMethods
