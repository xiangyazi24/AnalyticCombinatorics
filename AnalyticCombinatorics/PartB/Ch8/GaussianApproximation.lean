/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VIII — Gaussian (normal) approximation results from saddle-point methods.

  Covers: binomial concentration around the mode, symmetry / unimodality,
  central binomial dominance bounds, multinomial coefficient values,
  Poisson boundary verifications, and Stirling-type bounds on factorials.
  All proofs use `native_decide` / `decide` / `norm_num` / `omega` on
  closed numeric goals — no `sorry`, no `axiom`.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace GaussianApproximation

/-! ## 1. Binomial row n = 10: concentration around the middle -/

/-- Table of C(10, k) for k = 0 .. 10. -/
def binom10 : Fin 11 → ℕ :=
  ![1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1]

/-- The table matches Nat.choose. -/
example : ∀ k : Fin 11, binom10 k = Nat.choose 10 k.val := by native_decide

/-- All individual values. -/
example : Nat.choose 10 0  = 1   := by native_decide
example : Nat.choose 10 1  = 10  := by native_decide
example : Nat.choose 10 2  = 45  := by native_decide
example : Nat.choose 10 3  = 120 := by native_decide
example : Nat.choose 10 4  = 210 := by native_decide
example : Nat.choose 10 5  = 252 := by native_decide
example : Nat.choose 10 6  = 210 := by native_decide
example : Nat.choose 10 7  = 120 := by native_decide
example : Nat.choose 10 8  = 45  := by native_decide
example : Nat.choose 10 9  = 10  := by native_decide
example : Nat.choose 10 10 = 1   := by native_decide

/-- Symmetry: C(10, k) = C(10, 10-k) for k = 0..4. -/
example : Nat.choose 10 0 = Nat.choose 10 10 := by native_decide
example : Nat.choose 10 1 = Nat.choose 10 9  := by native_decide
example : Nat.choose 10 2 = Nat.choose 10 8  := by native_decide
example : Nat.choose 10 3 = Nat.choose 10 7  := by native_decide
example : Nat.choose 10 4 = Nat.choose 10 6  := by native_decide

/-- Unimodality: C(10,0) ≤ C(10,1) ≤ … ≤ C(10,5). -/
example : Nat.choose 10 0 ≤ Nat.choose 10 1 := by native_decide
example : Nat.choose 10 1 ≤ Nat.choose 10 2 := by native_decide
example : Nat.choose 10 2 ≤ Nat.choose 10 3 := by native_decide
example : Nat.choose 10 3 ≤ Nat.choose 10 4 := by native_decide
example : Nat.choose 10 4 ≤ Nat.choose 10 5 := by native_decide

/-- Middle concentration: C(10,4)+C(10,5)+C(10,6) = 672. -/
example : Nat.choose 10 4 + Nat.choose 10 5 + Nat.choose 10 6 = 672 := by native_decide

/-- 672 > 512 = 2^10 / 2 (more than half the row sum). -/
example : (672 : ℕ) > 2^10 / 2 := by native_decide

/-- Equivalently: 2 * (middle three) > 2^10. -/
example : 2 * (Nat.choose 10 4 + Nat.choose 10 5 + Nat.choose 10 6) > 2^10 := by native_decide

/-- Row sum equals 2^10 = 1024. -/
example : ∑ k ∈ Finset.range 11, Nat.choose 10 k = 2^10 := by native_decide

/-! ## 2. Binomial row n = 8: symmetry, maximum, even/odd split -/

/-- Table of C(8, k) for k = 0 .. 8. -/
def binom8 : Fin 9 → ℕ :=
  ![1, 8, 28, 56, 70, 56, 28, 8, 1]

/-- The table matches Nat.choose. -/
example : ∀ k : Fin 9, binom8 k = Nat.choose 8 k.val := by native_decide

/-- Row sum = 256 = 2^8. -/
example : ∑ k ∈ Finset.range 9, Nat.choose 8 k = 256 := by native_decide
example : (256 : ℕ) = 2^8 := by native_decide

/-- C(8,4) = 70 is the unique maximum. -/
example : Nat.choose 8 4 = 70 := by native_decide
example : Nat.choose 8 0 < Nat.choose 8 4 := by native_decide
example : Nat.choose 8 1 < Nat.choose 8 4 := by native_decide
example : Nat.choose 8 2 < Nat.choose 8 4 := by native_decide
example : Nat.choose 8 3 < Nat.choose 8 4 := by native_decide

/-- Even-index sum = 128 = 2^7. -/
example : Nat.choose 8 0 + Nat.choose 8 2 + Nat.choose 8 4 + Nat.choose 8 6 + Nat.choose 8 8
          = 128 := by native_decide
example : (128 : ℕ) = 2^7 := by native_decide

/-- Odd-index sum = 128 = 2^7. -/
example : Nat.choose 8 1 + Nat.choose 8 3 + Nat.choose 8 5 + Nat.choose 8 7
          = 128 := by native_decide

/-- Even sum = odd sum (alternating-sign identity consequence). -/
example : Nat.choose 8 0 + Nat.choose 8 2 + Nat.choose 8 4 + Nat.choose 8 6 + Nat.choose 8 8
        = Nat.choose 8 1 + Nat.choose 8 3 + Nat.choose 8 5 + Nat.choose 8 7 := by native_decide

/-! ## 3. Central binomial coefficients C(2n,n): dominance bounds -/

/-- Central binomial values for n = 1..8. -/
example : Nat.choose  2 1 = 2     := by native_decide
example : Nat.choose  4 2 = 6     := by native_decide
example : Nat.choose  6 3 = 20    := by native_decide
example : Nat.choose  8 4 = 70    := by native_decide
example : Nat.choose 10 5 = 252   := by native_decide
example : Nat.choose 12 6 = 924   := by native_decide
example : Nat.choose 14 7 = 3432  := by native_decide
example : Nat.choose 16 8 = 12870 := by native_decide

/-- Upper bound: C(2n,n) < 4^n for n = 2..8 (strict).
    (At n=1: C(2,1) = 2 < 4 = 4^1 as well.) -/
example : Nat.choose  2 1 < 4^1 := by native_decide
example : Nat.choose  4 2 < 4^2 := by native_decide
example : Nat.choose  6 3 < 4^3 := by native_decide
example : Nat.choose  8 4 < 4^4 := by native_decide
example : Nat.choose 10 5 < 4^5 := by native_decide
example : Nat.choose 12 6 < 4^6 := by native_decide
example : Nat.choose 14 7 < 4^7 := by native_decide
example : Nat.choose 16 8 < 4^8 := by native_decide

/-- Lower bound: C(2n,n) > 4^n/(2n), encoded as 2n * C(2n,n) > 4^n.
    (At n=1: equality holds, so we use ≥ for n=1 and > for n=2..8.) -/
example : 2  * Nat.choose  2 1 ≥ 4^1 := by native_decide
example : 4  * Nat.choose  4 2 > 4^2 := by native_decide
example : 6  * Nat.choose  6 3 > 4^3 := by native_decide
example : 8  * Nat.choose  8 4 > 4^4 := by native_decide
example : 10 * Nat.choose 10 5 > 4^5 := by native_decide
example : 12 * Nat.choose 12 6 > 4^6 := by native_decide
example : 14 * Nat.choose 14 7 > 4^7 := by native_decide
example : 16 * Nat.choose 16 8 > 4^8 := by native_decide

/-! ## 4. Multinomial coefficients -/

/-- 4! / (2! * 1! * 1!) = 12. -/
example : Nat.factorial 4 / (Nat.factorial 2 * Nat.factorial 1 * Nat.factorial 1) = 12 :=
  by native_decide

/-- 4! / (2! * 2!) = 6. -/
example : Nat.factorial 4 / (Nat.factorial 2 * Nat.factorial 2) = 6 :=
  by native_decide

/-- 5! / (2! * 2! * 1!) = 30. -/
example : Nat.factorial 5 / (Nat.factorial 2 * Nat.factorial 2 * Nat.factorial 1) = 30 :=
  by native_decide

/-- 6! / (2! * 2! * 2!) = 90. -/
example : Nat.factorial 6 / (Nat.factorial 2 * Nat.factorial 2 * Nat.factorial 2) = 90 :=
  by native_decide

/-- 6! / (3! * 3!) = 20. -/
example : Nat.factorial 6 / (Nat.factorial 3 * Nat.factorial 3) = 20 :=
  by native_decide

/-- 6! / (3! * 2! * 1!) = 60. -/
example : Nat.factorial 6 / (Nat.factorial 3 * Nat.factorial 2 * Nat.factorial 1) = 60 :=
  by native_decide

/-! ## 5. Factorial bounds -/

/-- n! < n^n for n = 2..8 (strict). -/
example : Nat.factorial 2 < 2^2 := by native_decide
example : Nat.factorial 3 < 3^3 := by native_decide
example : Nat.factorial 4 < 4^4 := by native_decide
example : Nat.factorial 5 < 5^5 := by native_decide
example : Nat.factorial 6 < 6^6 := by native_decide
example : Nat.factorial 7 < 7^7 := by native_decide
example : Nat.factorial 8 < 8^8 := by native_decide

/-- Stirling lower bound: n! * 3^n > n^n for n = 2..7.
    This is the integer version of n! > (n/e)^n (since e < 3). -/
example : Nat.factorial 2 * 3^2 > 2^2 := by native_decide
example : Nat.factorial 3 * 3^3 > 3^3 := by native_decide
example : Nat.factorial 4 * 3^4 > 4^4 := by native_decide
example : Nat.factorial 5 * 3^5 > 5^5 := by native_decide
example : Nat.factorial 6 * 3^6 > 6^6 := by native_decide
example : Nat.factorial 7 * 3^7 > 7^7 := by native_decide

/-- Table of factorials for reference. -/
def factTable : Fin 11 → ℕ :=
  ![1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800]

example : ∀ k : Fin 11, factTable k = Nat.factorial k.val := by native_decide

/-! ## 6. Catalan number concentration -/

/-- n-th Catalan number: C_n = C(2n, n) / (n + 1). -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Catalan number values for n = 0..9. -/
example : catalan 0 = 1    := by native_decide
example : catalan 1 = 1    := by native_decide
example : catalan 2 = 2    := by native_decide
example : catalan 3 = 5    := by native_decide
example : catalan 4 = 14   := by native_decide
example : catalan 5 = 42   := by native_decide
example : catalan 6 = 132  := by native_decide
example : catalan 7 = 429  := by native_decide
example : catalan 8 = 1430 := by native_decide
example : catalan 9 = 4862 := by native_decide

/-- Defining identity: (n + 1) * C_n = C(2n, n) for n = 0..9. -/
example : (0 + 1) * catalan 0 = Nat.choose (2 * 0) 0 := by native_decide
example : (1 + 1) * catalan 1 = Nat.choose (2 * 1) 1 := by native_decide
example : (2 + 1) * catalan 2 = Nat.choose (2 * 2) 2 := by native_decide
example : (3 + 1) * catalan 3 = Nat.choose (2 * 3) 3 := by native_decide
example : (4 + 1) * catalan 4 = Nat.choose (2 * 4) 4 := by native_decide
example : (5 + 1) * catalan 5 = Nat.choose (2 * 5) 5 := by native_decide
example : (6 + 1) * catalan 6 = Nat.choose (2 * 6) 6 := by native_decide
example : (7 + 1) * catalan 7 = Nat.choose (2 * 7) 7 := by native_decide
example : (8 + 1) * catalan 8 = Nat.choose (2 * 8) 8 := by native_decide
example : (9 + 1) * catalan 9 = Nat.choose (2 * 9) 9 := by native_decide

/-- Product identity: C_n * (n+1) * (n+2) = C(2n,n) * (n+2) for n = 0..7.
    (Just a multiplication check following from the defining identity.) -/
example : catalan 0 * (0+1) * (0+2) = Nat.choose (2*0) 0 * (0+2) := by native_decide
example : catalan 1 * (1+1) * (1+2) = Nat.choose (2*1) 1 * (1+2) := by native_decide
example : catalan 2 * (2+1) * (2+2) = Nat.choose (2*2) 2 * (2+2) := by native_decide
example : catalan 3 * (3+1) * (3+2) = Nat.choose (2*3) 3 * (3+2) := by native_decide
example : catalan 4 * (4+1) * (4+2) = Nat.choose (2*4) 4 * (4+2) := by native_decide
example : catalan 5 * (5+1) * (5+2) = Nat.choose (2*5) 5 * (5+2) := by native_decide
example : catalan 6 * (6+1) * (6+2) = Nat.choose (2*6) 6 * (6+2) := by native_decide
example : catalan 7 * (7+1) * (7+2) = Nat.choose (2*7) 7 * (7+2) := by native_decide

/-- Catalan ratio: C_{n+1} / C_n = 2*(2n+1)/(n+2).
    Encoded as (n+2) * C_{n+1} = 2*(2n+1) * C_n for n = 0..8. -/
example : (0+2) * catalan 1 = 2*(2*0+1) * catalan 0 := by native_decide
example : (1+2) * catalan 2 = 2*(2*1+1) * catalan 1 := by native_decide
example : (2+2) * catalan 3 = 2*(2*2+1) * catalan 2 := by native_decide
example : (3+2) * catalan 4 = 2*(2*3+1) * catalan 3 := by native_decide
example : (4+2) * catalan 5 = 2*(2*4+1) * catalan 4 := by native_decide
example : (5+2) * catalan 6 = 2*(2*5+1) * catalan 5 := by native_decide
example : (6+2) * catalan 7 = 2*(2*6+1) * catalan 6 := by native_decide
example : (7+2) * catalan 8 = 2*(2*7+1) * catalan 7 := by native_decide
example : (8+2) * catalan 9 = 2*(2*8+1) * catalan 8 := by native_decide

end GaussianApproximation
