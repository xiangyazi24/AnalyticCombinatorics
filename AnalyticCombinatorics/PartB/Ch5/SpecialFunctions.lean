/-
  Analytic Combinatorics — Part B
  Chapter V — Special Functions

  Executable numerical checks for Bernoulli numbers, Gamma/factorial values,
  Catalan recurrences, Pochhammer symbols (rising/falling factorials),
  and binomial transforms.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace SpecialFunctions

open Finset

/-! ## 1. Bernoulli numbers -/

/-- Table of Bernoulli numbers B_0 through B_6 as rationals. -/
def bernoulliTable : Fin 7 → ℚ := ![1, -1/2, 1/6, 0, -1/30, 0, 1/42]

/-- B_0 = 1. -/
example : bernoulliTable 0 = 1 := by native_decide

/-- B_1 = -1/2. -/
example : bernoulliTable 1 = -1/2 := by native_decide

/-- B_2 = 1/6. -/
example : bernoulliTable 2 = 1/6 := by native_decide

/-- B_3 = 0 (odd Bernoulli number). -/
example : bernoulliTable 3 = 0 := by native_decide

/-- B_4 = -1/30. -/
example : bernoulliTable 4 = -1/30 := by native_decide

/-- B_5 = 0 (odd Bernoulli number). -/
example : bernoulliTable 5 = 0 := by native_decide

/-- B_6 = 1/42. -/
example : bernoulliTable 6 = 1/42 := by native_decide

/-- Bernoulli vanishing: B_3 and B_5 are both 0 (odd indices ≥ 3). -/
example : bernoulliTable 3 = 0 ∧ bernoulliTable 5 = 0 := by native_decide

/-- Sum formula verification for n=1:
    C(2,0)*B_0 + C(2,1)*B_1 = 1*1 + 2*(-1/2) = 0. -/
example : (1 : ℚ) + 2 * (-1/2) = 0 := by native_decide

/-- Sum formula verification for n=2:
    C(3,0)*B_0 + C(3,1)*B_1 + C(3,2)*B_2 = 1 + 3*(-1/2) + 3*(1/6) = 0. -/
example : (1 : ℚ) + 3 * (-1/2) + 3 * (1/6) = 0 := by native_decide

/-- Sum formula verification for n=3:
    C(4,0)*1 + C(4,1)*(-1/2) + C(4,2)*(1/6) + C(4,3)*0 = 1 - 2 + 1 + 0 = 0. -/
example : (1 : ℚ) + 4 * (-1/2) + 6 * (1/6) + 4 * 0 = 0 := by native_decide

/-- Sum formula verification for n=4:
    C(5,0)*1 + C(5,1)*(-1/2) + C(5,2)*(1/6) + C(5,3)*0 + C(5,4)*(-1/30) = 0. -/
example : (1 : ℚ) + 5 * (-1/2) + 10 * (1/6) + 10 * 0 + 5 * (-1/30) = 0 := by native_decide

/-! ## 2. Gamma function at integers (via factorials) -/

/-- Γ(1) = 0! = 1. -/
example : Nat.factorial 0 = 1 := by native_decide

/-- Γ(2) = 1! = 1. -/
example : Nat.factorial 1 = 1 := by native_decide

/-- Γ(3) = 2! = 2. -/
example : Nat.factorial 2 = 2 := by native_decide

/-- Γ(4) = 3! = 6. -/
example : Nat.factorial 3 = 6 := by native_decide

/-- Γ(5) = 4! = 24. -/
example : Nat.factorial 4 = 24 := by native_decide

/-- 10! = 3628800. -/
example : Nat.factorial 10 = 3628800 := by native_decide

/-- Duplication formula witness: (5!)² * 252 = 10!.
    Equivalently: 1/C(10,5) = (5!)²/10!. -/
example : (Nat.factorial 5) ^ 2 * 252 = Nat.factorial 10 := by native_decide

/-- Central binomial coefficient C(10,5) = 252. -/
example : Nat.choose 10 5 = 252 := by native_decide

/-- Double factorial relation: 12! / 6!² = C(12,6) = 924. -/
example : Nat.choose 12 6 = 924 := by native_decide

/-- Factorial ratio: 7!/5! = 42. -/
example : Nat.factorial 7 / Nat.factorial 5 = 42 := by native_decide

/-! ## 3. Catalan number generating function recurrence -/

/-- Catalan number by formula: C_n = C(2n,n)/(n+1). -/
def catalanNum (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Catalan recurrence: (n+2)*C(n+1) = (4n+2)*C(n).
    Verify for n=0: 2*C(1) = 2*C(0), i.e. 2*1 = 2*1. -/
example : 2 * 1 = 2 * 1 := by native_decide

/-- Catalan recurrence for n=1: 3*C(2) = 6*C(1), i.e. 3*2 = 6*1. -/
example : 3 * 2 = 6 * 1 := by native_decide

/-- Catalan recurrence for n=2: 4*C(3) = 10*C(2), i.e. 4*5 = 10*2. -/
example : 4 * 5 = 10 * 2 := by native_decide

/-- Catalan recurrence for n=3: 5*C(4) = 14*C(3), i.e. 5*14 = 14*5. -/
example : 5 * 14 = 14 * 5 := by native_decide

/-- Catalan recurrence for n=4: 6*C(5) = 18*C(4), i.e. 6*42 = 18*14. -/
example : 6 * 42 = 18 * 14 := by native_decide

/-- Catalan recurrence for n=5: 7*C(6) = 22*C(5), i.e. 7*132 = 22*42. -/
example : 7 * 132 = 22 * 42 := by native_decide

/-- Catalan recurrence for n=6: 8*C(7) = 26*C(6), i.e. 8*429 = 26*132. -/
example : 8 * 429 = 26 * 132 := by native_decide

/-- Catalan recurrence for n=7: 9*C(8) = 30*C(7), i.e. 9*1430 = 30*429. -/
example : 9 * 1430 = 30 * 429 := by native_decide

/-- Catalan recurrence for n=8: 10*C(9) = 34*C(8), i.e. 10*4862 = 34*1430. -/
example : 10 * 4862 = 34 * 1430 := by native_decide

/-- Verify catalanNum formula for first several values. -/
example : catalanNum 0 = 1 := by native_decide
example : catalanNum 1 = 1 := by native_decide
example : catalanNum 2 = 2 := by native_decide
example : catalanNum 3 = 5 := by native_decide
example : catalanNum 4 = 14 := by native_decide
example : catalanNum 5 = 42 := by native_decide

/-! ## 4. Pochhammer symbol (rising factorial) -/

/-- Rising factorial: (x)_n = x(x+1)···(x+n-1). -/
def risingFactorial (x n : ℕ) : ℕ := ∏ i ∈ Finset.range n, (x + i)

/-- (1)_5 = 1*2*3*4*5 = 5! = 120. -/
example : risingFactorial 1 5 = Nat.factorial 5 := by native_decide

/-- (2)_3 = 2*3*4 = 24. -/
example : risingFactorial 2 3 = 24 := by native_decide

/-- (3)_4 = 3*4*5*6 = 360. -/
example : risingFactorial 3 4 = 360 := by native_decide

/-- (1)_n = n! for small values. -/
example : risingFactorial 1 0 = Nat.factorial 0 := by native_decide
example : risingFactorial 1 1 = Nat.factorial 1 := by native_decide
example : risingFactorial 1 2 = Nat.factorial 2 := by native_decide
example : risingFactorial 1 3 = Nat.factorial 3 := by native_decide
example : risingFactorial 1 4 = Nat.factorial 4 := by native_decide
example : risingFactorial 1 6 = Nat.factorial 6 := by native_decide

/-- (5)_3 = 5*6*7 = 210. -/
example : risingFactorial 5 3 = 210 := by native_decide

/-- (x)_1 = x for small x. -/
example : risingFactorial 7 1 = 7 := by native_decide

/-! ## 5. Falling factorial -/

/-- Falling factorial: x^{(n)} = x(x-1)···(x-n+1).
    In ℕ, this is 0 when n > x due to subtraction truncation. -/
def fallingFactorial (x n : ℕ) : ℕ := ∏ i ∈ Finset.range n, (x - i)

/-- 5^{(3)} = 5*4*3 = 60. -/
example : fallingFactorial 5 3 = 60 := by native_decide

/-- 10^{(4)} = 10*9*8*7 = 5040. -/
example : fallingFactorial 10 4 = 5040 := by native_decide

/-- n^{(n)} = n! (verified for n=6). -/
example : fallingFactorial 6 6 = Nat.factorial 6 := by native_decide

/-- Vanishing: 3^{(4)} = 3*2*1*0 = 0 (since n > x). -/
example : fallingFactorial 3 4 = 0 := by native_decide

/-- n^{(n)} = n! (verified for n=5). -/
example : fallingFactorial 5 5 = Nat.factorial 5 := by native_decide

/-- Falling factorial equals binomial coefficient times n!:
    x^{(n)} = C(x,n) * n!. Verified for x=7, n=3: 7*6*5 = C(7,3)*6 = 35*6 = 210. -/
example : fallingFactorial 7 3 = Nat.choose 7 3 * Nat.factorial 3 := by native_decide

/-- Verified for x=10, n=4: 10*9*8*7 = C(10,4)*4! = 210*24 = 5040. -/
example : fallingFactorial 10 4 = Nat.choose 10 4 * Nat.factorial 4 := by native_decide

/-! ## 6. Binomial transform -/

/-- Binomial transform: if a_n = 1 for all n, then b_n = 2^n.
    Verify sum of C(n,k) for k=0..n equals 2^n. -/
example : Nat.choose 4 0 + Nat.choose 4 1 + Nat.choose 4 2 +
          Nat.choose 4 3 + Nat.choose 4 4 = 2 ^ 4 := by native_decide

example : Nat.choose 6 0 + Nat.choose 6 1 + Nat.choose 6 2 +
          Nat.choose 6 3 + Nat.choose 6 4 + Nat.choose 6 5 +
          Nat.choose 6 6 = 2 ^ 6 := by native_decide

/-- Binomial transform of a_k = k: b_n = Σ C(n,k)*k = n*2^{n-1}.
    Verify for n=4: Σ C(4,k)*k = 0+4+12+12+4 = 32 = 4*8. -/
example : 0 + 4 + 12 + 12 + 4 = 32 := by native_decide

/-- Verify for n=5: Σ C(5,k)*k = 0+5+20+30+20+5 = 80 = 5*16. -/
example : 0 + 5 + 20 + 30 + 20 + 5 = 80 := by native_decide

/-- Explicit check: C(4,0)*0 + C(4,1)*1 + C(4,2)*2 + C(4,3)*3 + C(4,4)*4 = 32. -/
example : Nat.choose 4 0 * 0 + Nat.choose 4 1 * 1 + Nat.choose 4 2 * 2 +
          Nat.choose 4 3 * 3 + Nat.choose 4 4 * 4 = 32 := by native_decide

/-- Explicit check: C(5,0)*0 + C(5,1)*1 + ... + C(5,5)*5 = 80. -/
example : Nat.choose 5 0 * 0 + Nat.choose 5 1 * 1 + Nat.choose 5 2 * 2 +
          Nat.choose 5 3 * 3 + Nat.choose 5 4 * 4 + Nat.choose 5 5 * 5 = 80 := by native_decide

/-- Binomial transform of a_k = k²: b_n = Σ C(n,k)*k² = n*(n+1)*2^{n-2}.
    Verify for n=4: 4*5*4 = 80. -/
example : Nat.choose 4 0 * 0 + Nat.choose 4 1 * 1 + Nat.choose 4 2 * 4 +
          Nat.choose 4 3 * 9 + Nat.choose 4 4 * 16 = 80 := by native_decide

/-- Inverse binomial transform: if b_n = 2^n then a_n = Σ (-1)^{n-k} C(n,k) 2^k.
    For n=3: -C(3,0)*1 + C(3,1)*2 - C(3,2)*4 + C(3,3)*8 = -1+6-12+8 = 1.
    We verify in ℤ. -/
example : -(1 : ℤ) + 6 - 12 + 8 = 1 := by native_decide

/-- Inverse binomial transform for n=4:
    C(4,0)*1 - C(4,1)*2 + C(4,2)*4 - C(4,3)*8 + C(4,4)*16 = 1-8+24-32+16 = 1. -/
example : (1 : ℤ) - 8 + 24 - 32 + 16 = 1 := by native_decide

end SpecialFunctions
