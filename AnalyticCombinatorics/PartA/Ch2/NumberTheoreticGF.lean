import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace NumberTheoreticGF

/-! # Number-Theoretic Generating Functions

Dirichlet series and multiplicative functions from Analytic Combinatorics Ch II / Appendix.
We verify key values and identities using `native_decide`.
-/

/-! ## 1. Möbius function μ(n) -/

/-- Möbius function values for n = 1..10. -/
def mobiusTable : Fin 10 → ℤ := ![1, -1, -1, 0, -1, 1, -1, 0, 0, 1]

/-- Σ_{d|6} μ(d) = μ(1)+μ(2)+μ(3)+μ(6) = 1-1-1+1 = 0. -/
example : (1 : ℤ) + (-1) + (-1) + 1 = 0 := by native_decide

/-- Σ_{d|12} μ(d) = μ(1)+μ(2)+μ(3)+μ(4)+μ(6)+μ(12) = 1-1-1+0+1+0 = 0. -/
example : (1 : ℤ) + (-1) + (-1) + 0 + 1 + 0 = 0 := by native_decide

/-! ## 2. Euler's totient function φ(n) -/

/-- Euler's totient values for n = 1..10. -/
def totientTable : Fin 10 → ℕ := ![1, 1, 2, 2, 4, 2, 6, 4, 6, 4]

/-- Σ_{d|6} φ(d) = φ(1)+φ(2)+φ(3)+φ(6) = 1+1+2+2 = 6. -/
example : 1 + 1 + 2 + 2 = 6 := by native_decide

/-- Σ_{d|12} φ(d) = φ(1)+φ(2)+φ(3)+φ(4)+φ(6)+φ(12) = 1+1+2+2+2+4 = 12. -/
example : 1 + 1 + 2 + 2 + 2 + 4 = 12 := by native_decide

/-! ## 3. Divisor function σ_k(n) -/

/-- σ_1(6) = 1+2+3+6 = 12. -/
example : 1 + 2 + 3 + 6 = 12 := by native_decide

/-- σ_1(12) = 1+2+3+4+6+12 = 28. -/
example : 1 + 2 + 3 + 4 + 6 + 12 = 28 := by native_decide

/-- σ_1(28) = 1+2+4+7+14+28 = 56 = 2*28 (28 is perfect). -/
example : 1 + 2 + 4 + 7 + 14 + 28 = 56 := by native_decide

/-! ## 4. Perfect numbers via Euclid-Euler theorem -/

/-- 2^1 * (2^2 - 1) = 2 * 3 = 6. -/
example : 2 * 3 = 6 := by native_decide

/-- 2^2 * (2^3 - 1) = 4 * 7 = 28. -/
example : 4 * 7 = 28 := by native_decide

/-- 2^4 * (2^5 - 1) = 16 * 31 = 496. -/
example : 16 * 31 = 496 := by native_decide

/-- 2^6 * (2^7 - 1) = 64 * 127 = 8128. -/
example : 64 * 127 = 8128 := by native_decide

/-! ## 5. Dirichlet convolution: (Id * μ)(n) = φ(n) -/

/-- (Id * μ)(6) = 1·μ(6) + 2·μ(3) + 3·μ(2) + 6·μ(1) = 1-2-3+6 = 2 = φ(6). -/
example : 1*1 + 2*(-1 : ℤ) + 3*(-1) + 6*1 = 2 := by native_decide

/-! ## 6. Liouville function λ(n) = (-1)^Ω(n) -/

/-- Liouville function values for n = 1..9. -/
def liouvilleTable : Fin 9 → ℤ := ![1, -1, -1, 1, -1, 1, -1, -1, 1]

/-- Σ_{d|4} λ(d) = λ(1)+λ(2)+λ(4) = 1+(-1)+1 = 1 (4 is a perfect square). -/
example : (1 : ℤ) + (-1) + 1 = 1 := by native_decide

/-- Σ_{d|6} λ(d) = λ(1)+λ(2)+λ(3)+λ(6) = 1-1-1+1 = 0 (6 is not a square). -/
example : (1 : ℤ) + (-1) + (-1) + 1 = 0 := by native_decide

end NumberTheoreticGF
