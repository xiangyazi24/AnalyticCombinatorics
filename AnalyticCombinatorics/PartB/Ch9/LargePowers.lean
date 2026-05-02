/-
  Analytic Combinatorics — Part B
  Chapter IX — Large powers: saddle-point bounds and concentration.

  Flajolet & Sedgewick Chapter IX discusses the distribution of coefficients
  in large powers of generating functions.  The Gaussian approximation to
  binomial coefficients and concentration phenomena are verified here via
  finite numerical checks using native_decide.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset

namespace LargePowers

/-! ## Section 1: Central binomial coefficient bounds (Gaussian peak) -/

/-- C(10,5) = 252. -/
example : Nat.choose 10 5 = 252 := by native_decide

/-- The central coefficient 252 is less than 1/4 of 2^10 = 1024. -/
example : 252 * 4 < 1024 := by native_decide

/-- The central coefficient 252 is more than 1/5 of 2^10 = 1024. -/
example : 252 * 5 > 1024 := by native_decide

/-- C(20,10) = 184756. -/
example : Nat.choose 20 10 = 184756 := by native_decide

/-! ## Section 2: Binomial tail bounds -/

/-- Sum of binomial coefficients from index `threshold` to `n`. -/
def binomialTail (n threshold : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n - threshold + 1), Nat.choose n (threshold + k)

/-- binomialTail 10 8 = C(10,8) + C(10,9) + C(10,10) = 45 + 10 + 1 = 56. -/
example : binomialTail 10 8 = 56 := by native_decide

/-- binomialTail 10 6 = C(10,6) + C(10,7) + C(10,8) + C(10,9) + C(10,10) = 386. -/
example : binomialTail 10 6 = 386 := by native_decide

/-! ## Section 3: Central mass (LLN illustration) -/

/-- Sum of binomial coefficients C(n, lo), C(n, lo+1), ..., C(n, hi). -/
def centralMass (n lo hi : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (hi - lo + 1), Nat.choose n (lo + k)

/-- The middle third of C(12, _) contains more than 75% of the total mass 2^12. -/
example : centralMass 12 4 8 > 3 * 2 ^ 12 / 4 := by native_decide

/-! ## Section 4: Binomial unimodality (center is maximum) -/

example : Nat.choose 10 3 ≤ Nat.choose 10 5 := by native_decide
example : Nat.choose 10 7 ≤ Nat.choose 10 5 := by native_decide
example : Nat.choose 12 4 ≤ Nat.choose 12 6 := by native_decide
example : Nat.choose 20 7 ≤ Nat.choose 20 10 := by native_decide
example : Nat.choose 20 13 ≤ Nat.choose 20 10 := by native_decide

/-! ## Section 5: Concentration inequality (crude) -/

/-- C(2n, n) * 2 < 4^n for n ≥ 2, illustrating that the peak is a vanishing
    fraction of the total. -/
example : Nat.choose 4 2 * 2 < 4 ^ 2 := by native_decide
example : Nat.choose 6 3 * 2 < 4 ^ 3 := by native_decide
example : Nat.choose 10 5 * 2 < 4 ^ 5 := by native_decide
example : Nat.choose 20 10 * 2 < 4 ^ 10 := by native_decide

/-- C(8,4) * 3 < 2^8: the peak term is less than 1/3 of the total,
    illustrating concentration away from the maximum. -/
example : Nat.choose 8 4 * 3 < 2 ^ 8 := by native_decide

end LargePowers
