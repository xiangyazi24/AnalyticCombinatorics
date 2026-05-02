/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I §IV: Coefficient extraction from ordinary generating functions.

  Central binomial coefficients, Apéry numbers, Franel numbers,
  central Delannoy numbers, Catalan convolution, and large Schröder numbers.
  All identities verified by native_decide.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace OGFCoefficients

/-! ### Central binomial coefficients C(2n, n) -/

def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

example : centralBinom 0 = 1 := by native_decide
example : centralBinom 1 = 2 := by native_decide
example : centralBinom 2 = 6 := by native_decide
example : centralBinom 3 = 20 := by native_decide
example : centralBinom 4 = 70 := by native_decide
example : centralBinom 5 = 252 := by native_decide
example : centralBinom 6 = 924 := by native_decide
example : centralBinom 7 = 3432 := by native_decide
example : centralBinom 8 = 12870 := by native_decide
example : centralBinom 9 = 48620 := by native_decide

/-- C(2n, n) = 2 * C(2n-1, n-1) identity -/
example : Nat.choose 10 5 = 2 * Nat.choose 9 4 := by native_decide
example : Nat.choose 14 7 = 2 * Nat.choose 13 6 := by native_decide

/-! ### Apéry numbers A(n) = Σ C(n,k)² C(n+k,k)² -/

def aperyNumber (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) ^ 2

example : aperyNumber 0 = 1 := by native_decide
example : aperyNumber 1 = 5 := by native_decide
example : aperyNumber 2 = 73 := by native_decide
example : aperyNumber 3 = 1445 := by native_decide

/-! ### Franel numbers f(n) = Σ C(n,k)³ -/

def franelNumber (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 3

example : franelNumber 0 = 1 := by native_decide
example : franelNumber 1 = 2 := by native_decide
example : franelNumber 2 = 10 := by native_decide
example : franelNumber 3 = 56 := by native_decide
example : franelNumber 4 = 346 := by native_decide

/-! ### Central Delannoy numbers D(n,n) = Σ C(n,k)² 2^k -/

def centralDelannoy (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 * 2 ^ k

example : centralDelannoy 0 = 1 := by native_decide
example : centralDelannoy 1 = 3 := by native_decide
example : centralDelannoy 2 = 13 := by native_decide
example : centralDelannoy 3 = 63 := by native_decide
example : centralDelannoy 4 = 321 := by native_decide

/-! ### Catalan convolution: [z^n] C(z)² = C(n+1) -/

/-- [z^3] C² = C(0)*C(3) + C(1)*C(2) + C(2)*C(1) + C(3)*C(0) = 14 = C(4) -/
example : 1 * 5 + 1 * 2 + 2 * 1 + 5 * 1 = 14 := by native_decide

/-- [z^4] C² = C(0)*C(4) + C(1)*C(3) + C(2)*C(2) + C(3)*C(1) + C(4)*C(0) = 42 = C(5) -/
example : 1 * 14 + 1 * 5 + 2 * 2 + 5 * 1 + 14 * 1 = 42 := by native_decide

/-! ### Large Schröder numbers -/

def schroederLarge : Fin 7 → ℕ := ![1, 2, 6, 22, 90, 394, 1806]

example : schroederLarge 0 = 1 := by native_decide
example : schroederLarge 1 = 2 := by native_decide
example : schroederLarge 2 = 6 := by native_decide
example : schroederLarge 3 = 22 := by native_decide
example : schroederLarge 4 = 90 := by native_decide
example : schroederLarge 5 = 394 := by native_decide
example : schroederLarge 6 = 1806 := by native_decide

/-- Recurrence: (n+2)*S(n+1) = 3*(2n+1)*S(n) - (n-1)*S(n-1) for n ≥ 1 -/
example : 3 * 6 = 3 * 3 * 2 - 0 * 1 := by native_decide
example : 4 * 22 = 3 * 5 * 6 - 1 * 2 := by native_decide
example : 5 * 90 = 3 * 7 * 22 - 2 * 6 := by native_decide

end OGFCoefficients
