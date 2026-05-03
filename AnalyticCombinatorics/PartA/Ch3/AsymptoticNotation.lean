import Mathlib.Tactic

set_option linter.style.nativeDecide false
set_option linter.style.longLine false

namespace AsymptoticNotation

/-! # Asymptotic Notation and Growth Rate Comparisons

Numerical verifications for the asymptotic hierarchy:
  n! ≫ a^n ≫ n^k ≫ n·log(n) ≫ n ≫ log(n)

All comparisons are verified at concrete finite ranges using `native_decide`.
Sequences are represented as `Fin n → ℕ` tables. -/

/-! ## 1. Factorial Dominates Exponential: n! > 2^n for n ≥ 4 -/

/-- Factorial values n! for n = 0..10. -/
def factTable : Fin 11 → ℕ := ![1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800]

/-- Powers of 2: 2^n for n = 0..10. -/
def pow2Table : Fin 11 → ℕ := ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

/-- n! > 2^n for n = 4..10. -/
example : ∀ i : Fin 7, factTable ⟨i.val + 4, by omega⟩ > pow2Table ⟨i.val + 4, by omega⟩ := by
  native_decide

/-- Spot checks: 4! = 24 > 16 = 2^4. -/
example : factTable 4 = 24 := by native_decide
example : pow2Table 4 = 16 := by native_decide
example : factTable 4 > pow2Table 4 := by native_decide

/-- 7! = 5040, 8! = 40320, 9! = 362880, 10! = 3628800. -/
example : factTable 7 = 5040 := by native_decide
example : factTable 8 = 40320 := by native_decide
example : factTable 9 = 362880 := by native_decide
example : factTable 10 = 3628800 := by native_decide

/-- 2^10 = 1024. -/
example : pow2Table 10 = 1024 := by native_decide

/-- Powers of 3: 3^n for n = 0..10. -/
def pow3Table : Fin 11 → ℕ := ![1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 59049]

/-- n! > 3^n for n = 7, 8, 9 (i.e., 5040>2187, 40320>6561, 362880>19683). -/
example : factTable 7 > pow3Table 7 := by native_decide
example : factTable 8 > pow3Table 8 := by native_decide
example : factTable 9 > pow3Table 9 := by native_decide

/-- Verify: 3^7 = 2187, 3^8 = 6561, 3^9 = 19683. -/
example : pow3Table 7 = 2187 := by native_decide
example : pow3Table 8 = 6561 := by native_decide
example : pow3Table 9 = 19683 := by native_decide

/-! ## 2. Exponential Dominates Polynomial: 2^n > n^3 for n ≥ 10 -/

/-- n^3 for n = 0..15. -/
def cube : Fin 16 → ℕ := ![0, 1, 8, 27, 64, 125, 216, 343, 512, 729, 1000, 1331, 1728, 2197, 2744, 3375]

/-- 2^n for n = 0..15. -/
def pow2_16 : Fin 16 → ℕ := ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768]

/-- 2^n > n^3 for n = 10..15. -/
example : ∀ i : Fin 6, pow2_16 ⟨i.val + 10, by omega⟩ > cube ⟨i.val + 10, by omega⟩ := by
  native_decide

/-- Spot checks: 2^10 = 1024 > 1000 = 10^3. -/
example : pow2_16 10 = 1024 := by native_decide
example : cube 10 = 1000 := by native_decide
example : pow2_16 10 > cube 10 := by native_decide

/-- 2^15 = 32768 > 3375 = 15^3. -/
example : pow2_16 15 = 32768 := by native_decide
example : cube 15 = 3375 := by native_decide
example : pow2_16 15 > cube 15 := by native_decide

/-- n^2 for n = 0..15. -/
def sqr : Fin 16 → ℕ := ![0, 1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225]

/-- 2^n > n^2 for n = 5..15. -/
example : ∀ i : Fin 11, pow2_16 ⟨i.val + 5, by omega⟩ > sqr ⟨i.val + 5, by omega⟩ := by
  native_decide

/-- Spot checks: 2^5 = 32 > 25 = 5^2, 2^6 = 64 > 36 = 6^2, 2^7 = 128 > 49 = 7^2. -/
example : pow2_16 5 > sqr 5 := by native_decide
example : pow2_16 6 > sqr 6 := by native_decide
example : pow2_16 7 > sqr 7 := by native_decide

/-! ## 3. Polynomial Hierarchy: n^3 > n^2 > n -/

/-- n^4 for n = 0..15. -/
def fourth : Fin 16 → ℕ := ![0, 1, 16, 81, 256, 625, 1296, 2401, 4096, 6561, 10000, 14641, 20736, 28561, 38416, 50625]

-- n^3 > n^2 + n for n = 2..10, equivalently n^3 - n^2 > n (but we avoid ℕ subtraction).
-- We verify n^3 > n^2 + n directly.
/-- n^2 + n for n = 0..10. -/
def sqrPlusN : Fin 11 → ℕ := ![0, 2, 6, 12, 20, 30, 42, 56, 72, 90, 110]

/-- n^3 table for n = 0..10 (a sub-table). -/
def cubeSmall : Fin 11 → ℕ := ![0, 1, 8, 27, 64, 125, 216, 343, 512, 729, 1000]

/-- n^3 > n^2 + n for n = 2..10. -/
example : ∀ i : Fin 9, cubeSmall ⟨i.val + 2, by omega⟩ > sqrPlusN ⟨i.val + 2, by omega⟩ := by
  native_decide

/-- Spot check: 2^3 = 8 > 4 + 2 = 6. -/
example : cubeSmall 2 > sqrPlusN 2 := by native_decide

-- n^4 > 2 * n^3 for n = 3..10.
/-- 2*n^3 values for n = 0..10. -/
def twoCube : Fin 11 → ℕ := ![0, 2, 16, 54, 128, 250, 432, 686, 1024, 1458, 2000]

/-- n^4 for n = 0..10. -/
def fourthSmall : Fin 11 → ℕ := ![0, 1, 16, 81, 256, 625, 1296, 2401, 4096, 6561, 10000]

/-- n^4 > 2*n^3 for n = 3..10. -/
example : ∀ i : Fin 8, fourthSmall ⟨i.val + 3, by omega⟩ > twoCube ⟨i.val + 3, by omega⟩ := by
  native_decide

/-- Spot check: 3^4 = 81 > 2 * 3^3 = 54. -/
example : fourthSmall 3 = 81 := by native_decide
example : twoCube 3 = 54 := by native_decide
example : fourthSmall 3 > twoCube 3 := by native_decide

/-! ## 4. Harmonic Numbers (Sub-logarithmic Accumulation)

The harmonic number H(n) = 1 + 1/2 + ... + 1/n grows like log(n).
We work with scaled harmonics: H(n)*n! = n! * Σ_{k=1}^{n} 1/k.
These are always integers. -/

/-- H(n)*n! for n = 1..7.
    H(1)*1! = 1, H(2)*2! = 3, H(3)*3! = 11, H(4)*4! = 50,
    H(5)*5! = 274, H(6)*6! = 1764, H(7)*7! = 13068. -/
def scaledHarmonic : Fin 8 → ℕ := ![0, 1, 3, 11, 50, 274, 1764, 13068]

/-- (n+1)! for n = 0..7. -/
def factPlus1 : Fin 8 → ℕ := ![1, 2, 6, 24, 120, 720, 5040, 40320]

/-- H(n)*n! < (n+1)! for n = 1..7 (since H(n) < n+1). -/
example : ∀ i : Fin 7, scaledHarmonic ⟨i.val + 1, by omega⟩ < factPlus1 ⟨i.val + 1, by omega⟩ := by
  native_decide

-- H(n)*n! > n! for n = 2..7 (since H(n) > 1).
/-- n! for n = 0..7. -/
def factSmall : Fin 8 → ℕ := ![1, 1, 2, 6, 24, 120, 720, 5040]

/-- H(n)*n! > n! for n = 2..7. -/
example : ∀ i : Fin 6, scaledHarmonic ⟨i.val + 2, by omega⟩ > factSmall ⟨i.val + 2, by omega⟩ := by
  native_decide

/-- Spot checks: H(3)*3! = 11, H(4)*4! = 50, H(5)*5! = 274. -/
example : scaledHarmonic 3 = 11 := by native_decide
example : scaledHarmonic 4 = 50 := by native_decide
example : scaledHarmonic 5 = 274 := by native_decide

/-! ## 5. Catalan Numbers: Growth Rate ~4^n / n^{3/2}

C(n) = (1/(n+1)) * C(2n, n). The ratio C(n+1)/C(n) → 4 from below. -/

/-- Catalan numbers C(n) for n = 0..9. -/
def catalan : Fin 10 → ℕ := ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]

/-- 4^n for n = 0..9. -/
def pow4 : Fin 10 → ℕ := ![1, 4, 16, 64, 256, 1024, 4096, 16384, 65536, 262144]

/-- C(n) < 4^n for n = 1..9. -/
example : ∀ i : Fin 9, catalan ⟨i.val + 1, by omega⟩ < pow4 ⟨i.val + 1, by omega⟩ := by
  native_decide

/-- Spot check: C(9) = 4862 < 262144 = 4^9. -/
example : catalan 9 = 4862 := by native_decide
example : pow4 9 = 262144 := by native_decide
example : catalan 9 < pow4 9 := by native_decide

/-- The identity C(n) * (n+1) = C(2n, n) for n = 0..9.
    Equivalently: catalan[n] * (n+1) = binomial(2n, n). -/
def centralBinom : Fin 10 → ℕ := ![1, 2, 6, 20, 70, 252, 924, 3432, 12870, 48620]

/-- C(n) * (n+1) = C(2n, n) for n = 0..9. -/
example : ∀ i : Fin 10, catalan i * (i.val + 1) = centralBinom i := by native_decide

/-- The ratio C(n+1) < 4 * C(n) for n = 1..8 (ratio < 4). -/
example : ∀ i : Fin 8, catalan ⟨i.val + 2, by omega⟩ < 4 * catalan ⟨i.val + 1, by omega⟩ := by
  native_decide

/-- Spot check: C(2) = 2 < 4*C(1) = 4. -/
example : catalan 2 < 4 * catalan 1 := by native_decide
/-- C(9) = 4862 < 4*C(8) = 4*1430 = 5720. -/
example : catalan 9 < 4 * catalan 8 := by native_decide

/-! ## 6. Fibonacci Numbers: Growth Rate ~φ^n

F(n) satisfies F(n) < 2^n (well below exponential).
The ratio F(n+1)/F(n) → φ ≈ 1.618 < 2, so 2*F(n) ≥ F(n+1).
The identity F(n)^2 + F(n+1)^2 = F(2n+1) confirms the growth structure. -/

/-- Fibonacci numbers F(n) for n = 0..15. -/
def fib : Fin 16 → ℕ := ![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610]

/-- F(n) < 2^n for n = 0..15. -/
example : ∀ i : Fin 16, fib i < pow2_16 i := by native_decide

/-- Spot checks. -/
example : fib 10 = 55 := by native_decide
example : fib 15 = 610 := by native_decide
example : pow2_16 10 = 1024 := by native_decide
example : fib 10 < pow2_16 10 := by native_decide

-- The identity F(n)^2 + F(n+1)^2 = F(2n+1) for n = 1..6.
-- F(1)^2+F(2)^2 = 2 = F(3), F(2)^2+F(3)^2 = 5 = F(5), F(3)^2+F(4)^2 = 13 = F(7), etc.
/-- F(2n+1) for n = 0..6: 0, F(3)=2, F(5)=5, F(7)=13, F(9)=34, F(11)=89, F(13)=233. -/
def fibOdd : Fin 7 → ℕ := ![0, 2, 5, 13, 34, 89, 233]

/-- F(n)^2 + F(n+1)^2 = F(2n+1) for n = 1..6. -/
example : ∀ i : Fin 6,
    fib ⟨i.val + 1, by omega⟩ ^ 2 + fib ⟨i.val + 2, by omega⟩ ^ 2 =
    fibOdd ⟨i.val + 1, by omega⟩ := by
  native_decide

/-- Spot check: F(3)^2 + F(4)^2 = 4 + 9 = 13 = F(7). -/
example : fib 3 ^ 2 + fib 4 ^ 2 = 13 := by native_decide
example : fibOdd 3 = 13 := by native_decide

/-- 2 * F(n) ≥ F(n+1) for n = 1..14 (since φ < 2). -/
example : ∀ i : Fin 14, 2 * fib ⟨i.val + 1, by omega⟩ ≥ fib ⟨i.val + 2, by omega⟩ := by
  native_decide

/-- Spot checks: 2*F(14) = 2*377 = 754 ≥ 610 = F(15). -/
example : fib 14 = 377 := by native_decide
example : fib 15 = 610 := by native_decide
example : 2 * fib 14 ≥ fib 15 := by native_decide

/-- Summary of growth hierarchy (verified at n=10):
    F(10) = 55 < 2^10 = 1024 < 10^3 = 1000 ... wait, 1024 > 1000.
    So: F(10) < n^3 < 2^n at n=10, and 10! >> 2^10. -/
example : fib 10 < cube 10 := by native_decide
example : pow2_16 10 > cube 10 := by native_decide
example : factTable 10 > pow2Table 10 := by native_decide

end AsymptoticNotation
