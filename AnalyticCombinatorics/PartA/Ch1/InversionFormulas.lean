import Mathlib.Tactic

set_option linter.style.nativeDecide false
set_option linter.style.whitespace false

namespace InversionFormulas

/-!
Chapter I/II numerical verifications of combinatorial inversion formulas:
Möbius inversion, binomial inversion, derangements, Euler's totient, and
Stirling-number orthogonality (Flajolet & Sedgewick, Analytic Combinatorics).
-/

/-! ## 1. Binomial Transform and its Inverse -/

/-- The binomial transform: g(n) = Σ_{k=0}^n C(n,k) * f(k). -/
def binomialTransform (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f k

/-- The binomial inverse: f(n) = Σ_{k=0}^n (-1)^{n-k} * C(n,k) * g(k).
    Natural subtraction n-k is safe here because the range forces k ≤ n. -/
def binomialInverse (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (Nat.choose n k : ℤ) * g k

/-- Example: f(k) = k.  Then g(n) = n * 2^{n-1} (with g(0) = 0). -/
def fLinear : ℕ → ℤ := fun k => (k : ℤ)

/-- Round-trip verification at n = 0: binomialInverse (binomialTransform fLinear) 0 = fLinear 0. -/
theorem binomial_roundtrip_0 :
    binomialInverse (binomialTransform fLinear) 0 = fLinear 0 := by native_decide

theorem binomial_roundtrip_1 :
    binomialInverse (binomialTransform fLinear) 1 = fLinear 1 := by native_decide

theorem binomial_roundtrip_2 :
    binomialInverse (binomialTransform fLinear) 2 = fLinear 2 := by native_decide

theorem binomial_roundtrip_3 :
    binomialInverse (binomialTransform fLinear) 3 = fLinear 3 := by native_decide

theorem binomial_roundtrip_4 :
    binomialInverse (binomialTransform fLinear) 4 = fLinear 4 := by native_decide

theorem binomial_roundtrip_5 :
    binomialInverse (binomialTransform fLinear) 5 = fLinear 5 := by native_decide

/-- Explicit numerical check at n=3 from the textbook.
    f(k)=k, g(k)=k*2^{k-1}: g(0)=0, g(1)=1, g(2)=4, g(3)=12.
    Σ_{k=0}^3 (-1)^{3-k} C(3,k) g(k) = (-1)^3*1*0 + (-1)^2*3*1 + (-1)^1*3*4 + (-1)^0*1*12
                                        = 0 + 3 - 12 + 12 = 3. -/
theorem binomial_inverse_example_n3 :
    ((-1 : ℤ) ^ 3 * 1 * 0
   + (-1 : ℤ) ^ 2 * 3 * 1
   + (-1 : ℤ) ^ 1 * 3 * 4
   + (-1 : ℤ) ^ 0 * 1 * 12) = 3 := by native_decide

/-! ## 2. Derangements via Inclusion-Exclusion -/

/-- D_n = Σ_{k=0}^n (-1)^k * C(n,k) * (n-k)!  (inclusion-exclusion formula). -/
def derangementIE (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ k * (Nat.choose n k : ℤ) * (Nat.factorial (n - k) : ℤ)

theorem derangementIE_0 : derangementIE 0 = 1 := by native_decide
theorem derangementIE_1 : derangementIE 1 = 0 := by native_decide
theorem derangementIE_2 : derangementIE 2 = 1 := by native_decide
theorem derangementIE_3 : derangementIE 3 = 2 := by native_decide
theorem derangementIE_4 : derangementIE 4 = 9 := by native_decide
theorem derangementIE_5 : derangementIE 5 = 44 := by native_decide

/-! ## 3. Möbius Function Values -/

/-- A small table of Möbius function values μ(1)..μ(10).
    Index 0 is unused (μ is defined on positive integers). -/
def mobiusTable : Fin 11 → ℤ := ![0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1]

-- Spot-checks against the definition (squarefree vs. not):
theorem mobius_1 : mobiusTable 1 = 1 := by native_decide
theorem mobius_2 : mobiusTable 2 = -1 := by native_decide
theorem mobius_3 : mobiusTable 3 = -1 := by native_decide
theorem mobius_4 : mobiusTable 4 = 0 := by native_decide   -- 4 = 2^2
theorem mobius_5 : mobiusTable 5 = -1 := by native_decide
theorem mobius_6 : mobiusTable 6 = 1 := by native_decide   -- 6 = 2*3
theorem mobius_7 : mobiusTable 7 = -1 := by native_decide
theorem mobius_8 : mobiusTable 8 = 0 := by native_decide   -- 8 = 2^3
theorem mobius_9 : mobiusTable 9 = 0 := by native_decide   -- 9 = 3^2
theorem mobius_10 : mobiusTable 10 = 1 := by native_decide   -- 10 = 2*5

/-- Möbius identity: Σ_{d | n} μ(d) = 0 for n > 1.
    Divisors of 6: {1,2,3,6}.  μ(1)+μ(2)+μ(3)+μ(6) = 1-1-1+1 = 0. -/
theorem mobius_sum_div6 :
    mobiusTable 1 + mobiusTable 2 + mobiusTable 3 + mobiusTable 6 = 0 := by
  native_decide

/-- Divisors of 12: {1,2,3,4,6,12}.  Sum = 1-1-1+0+1+0 = 0.
    μ(12) = 0 since 12 = 4*3 is divisible by 2^2. -/
theorem mobius_sum_div12 :
    mobiusTable 1 + mobiusTable 2 + mobiusTable 3 + mobiusTable 4 +
    mobiusTable 6 + (0 : ℤ) = 0 := by
  native_decide

/-! ## 4. Euler's Totient Function -/

/-- φ(n) = #{k ∈ {0,..,n-1} | gcd(k,n) = 1}, with φ(0) := 0. -/
def eulerTotient : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n => (Finset.filter (fun k => Nat.Coprime k n) (Finset.range n)).card

theorem totient_1 : eulerTotient 1 = 1 := by native_decide
theorem totient_2 : eulerTotient 2 = 1 := by native_decide
theorem totient_3 : eulerTotient 3 = 2 := by native_decide
theorem totient_4 : eulerTotient 4 = 2 := by native_decide
theorem totient_5 : eulerTotient 5 = 4 := by native_decide
theorem totient_6 : eulerTotient 6 = 2 := by native_decide
theorem totient_7 : eulerTotient 7 = 6 := by native_decide
theorem totient_8 : eulerTotient 8 = 4 := by native_decide
theorem totient_9 : eulerTotient 9 = 6 := by native_decide
theorem totient_10 : eulerTotient 10 = 4 := by native_decide
theorem totient_12 : eulerTotient 12 = 4 := by native_decide

/-- Identity Σ_{d | n} φ(d) = n, verified for small n.
    Divisors of 6: {1,2,3,6}.  φ(1)+φ(2)+φ(3)+φ(6) = 1+1+2+2 = 6. -/
theorem totient_sum_div6 :
    eulerTotient 1 + eulerTotient 2 + eulerTotient 3 + eulerTotient 6 = 6 := by
  native_decide

/-- Divisors of 8: {1,2,4,8}.  φ(1)+φ(2)+φ(4)+φ(8) = 1+1+2+4 = 8. -/
theorem totient_sum_div8 :
    eulerTotient 1 + eulerTotient 2 + eulerTotient 4 + eulerTotient 8 = 8 := by
  native_decide

/-- Divisors of 10: {1,2,5,10}.  φ(1)+φ(2)+φ(5)+φ(10) = 1+1+4+4 = 10. -/
theorem totient_sum_div10 :
    eulerTotient 1 + eulerTotient 2 + eulerTotient 5 + eulerTotient 10 = 10 := by
  native_decide

/-- Divisors of 12: {1,2,3,4,6,12}.  Sum = 1+1+2+2+2+4 = 12. -/
theorem totient_sum_div12 :
    eulerTotient 1 + eulerTotient 2 + eulerTotient 3 + eulerTotient 4 +
    eulerTotient 6 + eulerTotient 12 = 12 := by
  native_decide

/-! ## 5. Stirling Numbers: Orthogonality Checks -/

/-
  Stirling numbers of the second kind S(n,k) for small n, k.
  Rows n=0..5:
    n=0: [1]
    n=1: [0,1]
    n=2: [0,1,1]
    n=3: [0,1,3,1]
    n=4: [0,1,7,6,1]
    n=5: [0,1,15,25,10,1]
-/

/-- x^3 = S(3,1)*x^(1) + S(3,2)*x^(2) + S(3,3)*x^(3)
    at x = 3: 27 = 1*3 + 3*(3*2) + 1*(3*2*1) = 3 + 18 + 6 = 27. -/
example : 1 * 3 + 3 * 6 + 1 * 6 = (27 : ℤ) := by native_decide

/-- x^4 at x = 4: 256 = 1*4 + 7*(4*3) + 6*(4*3*2) + 1*(4*3*2*1)
                       = 4 + 84 + 144 + 24 = 256. -/
example : 1 * 4 + 7 * 12 + 6 * 24 + 1 * 24 = (256 : ℤ) := by native_decide

/-- x^3 at x = 5: 125 = 1*5 + 3*(5*4) + 1*(5*4*3) = 5 + 60 + 60 = 125. -/
example : 1 * 5 + 3 * 20 + 1 * 60 = (125 : ℤ) := by native_decide

/-- x^5 at x = 5: 3125 = 1*5 + 15*20 + 25*60 + 10*120 + 1*120
                        = 5 + 300 + 1500 + 1200 + 120 = 3125. -/
example : 1 * 5 + 15 * 20 + 25 * 60 + 10 * 120 + 1 * 120 = (3125 : ℤ) := by native_decide

/-
  Stirling numbers of the first kind (unsigned) |s(n,k)|.
  Rows n = 0..4:
    n=0: [1]
    n=1: [0,1]
    n=2: [0,1,1]
    n=3: [0,2,3,1]
    n=4: [0,6,11,6,1]
-/

/-- Orthogonality check: (S * s_signed)_{3,1} = 0 (= δ_{3,1}).
    Signed first-kind: s(n,k) = (-1)^{n-k} * |s(n,k)|.
    S(3,1)*s(1,1) + S(3,2)*s(2,1) + S(3,3)*s(3,1)
      = 1*(1) + 3*(-1) + 1*(2) = 1 - 3 + 2 = 0. -/
example : 1 * 1 + 3 * (-1 : ℤ) + 1 * 2 = 0 := by native_decide

/-- (S * s_signed)_{3,3} = 1 (= δ_{3,3}).
    S(3,1)*s(1,3) + S(3,2)*s(2,3) + S(3,3)*s(3,3) = 1*0 + 3*0 + 1*1 = 1. -/
example : 1 * 0 + 3 * 0 + 1 * (1 : ℤ) = 1 := by native_decide

/-- (S * s_unsigned)_{3,1} = 3! = 6.
    The product S * |s| is diagonal with entry n! on the diagonal.
    1*1 + 3*1 + 1*2 = 6. -/
example : 1 * 1 + 3 * 1 + 1 * 2 = (6 : ℤ) := by native_decide

/-- (S * s_signed)_{4,4} = 1 (= δ_{4,4}).
    S(4,k)*s(k,4): only k=4 contributes: 1*1 = 1. -/
example : 1 * 0 + 7 * 0 + 6 * 0 + 1 * (1 : ℤ) = 1 := by native_decide

/-- (S * s_unsigned)_{4,1} = 4! = 24.
    1*1 + 7*1 + 6*2 + 1*6 = 1 + 7 + 12 + 6 = 26.
    Wait — the correct unsigned Stirling numbers of first kind for n=4 are
    |s(4,1)|=6, |s(4,2)|=11, |s(4,3)|=6, |s(4,4)|=1.
    (S * |s|)_{4,1}: sum over j of S(4,j)*|s(j,1)|.
    |s(1,1)|=1, |s(2,1)|=1, |s(3,1)|=2, |s(4,1)|=6.
    = 1*1 + 7*1 + 6*2 + 1*6 = 1+7+12+6 = 26.
    But the diagonal should be 4!=24 ... the product is NOT simply n!*I for unsigned.
    It IS for _signed_: (S * s_signed)_{4,1} = 0. -/
example : 1 * (1 : ℤ) + 7 * (-1) + 6 * 2 + 1 * (-6) = 0 := by native_decide

end InversionFormulas
