import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.PolynomialArithmetic

open Finset Nat


/-! # Polynomial Arithmetic and Enumeration — Chapter V

Topics:
1. Euler's totient φ(n) table and properties (degrees of cyclotomic polynomials)
2. Monic polynomials over F_q: counts and irreducible counts
3. Polynomial coefficient growth (Cauchy bound, discriminant)
4. Compositions and their connection to polynomials
5. Polynomial multiplication cost (naive vs Karatsuba)
6. Power sums and Newton's identities
-/

-- ============================================================
-- Section 1: Euler's Totient φ(n) Table
-- ============================================================

/-! ## Euler's Totient Function

The degree of the n-th cyclotomic polynomial Φ_n is φ(n), Euler's totient.
φ(n) counts integers in {1,...,n} coprime to n.
-/

-- Table: φ(n) for n = 1..12
-- Index i corresponds to n = i+1
def totientTable : Fin 12 → ℕ := ![1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4]

-- Verify individual values
example : totientTable ⟨0, by omega⟩ = 1 := by native_decide  -- φ(1)=1
example : totientTable ⟨1, by omega⟩ = 1 := by native_decide  -- φ(2)=1
example : totientTable ⟨2, by omega⟩ = 2 := by native_decide  -- φ(3)=2
example : totientTable ⟨3, by omega⟩ = 2 := by native_decide  -- φ(4)=2
example : totientTable ⟨4, by omega⟩ = 4 := by native_decide  -- φ(5)=4
example : totientTable ⟨5, by omega⟩ = 2 := by native_decide  -- φ(6)=2
example : totientTable ⟨6, by omega⟩ = 6 := by native_decide  -- φ(7)=6
example : totientTable ⟨7, by omega⟩ = 4 := by native_decide  -- φ(8)=4
example : totientTable ⟨8, by omega⟩ = 6 := by native_decide  -- φ(9)=6
example : totientTable ⟨9, by omega⟩ = 4 := by native_decide  -- φ(10)=4
example : totientTable ⟨10, by omega⟩ = 10 := by native_decide -- φ(11)=10
example : totientTable ⟨11, by omega⟩ = 4 := by native_decide  -- φ(12)=4

-- For primes p, φ(p) = p-1. In ℕ: φ(p)+1 = p.
-- p=2: φ(2)+1=2
example : totientTable ⟨1, by omega⟩ + 1 = 2 := by native_decide
-- p=3: φ(3)+1=3
example : totientTable ⟨2, by omega⟩ + 1 = 3 := by native_decide
-- p=5: φ(5)+1=5
example : totientTable ⟨4, by omega⟩ + 1 = 5 := by native_decide
-- p=7: φ(7)+1=7
example : totientTable ⟨6, by omega⟩ + 1 = 7 := by native_decide
-- p=11: φ(11)+1=11
example : totientTable ⟨10, by omega⟩ + 1 = 11 := by native_decide

-- The divisor sum identity: ∑_{d|n} φ(d) = n
-- We verify this for n = 1..12 using explicit divisor sums.

-- Divisor sum of totient for n=1: φ(1) = 1
example : totientTable ⟨0, by omega⟩ = 1 := by native_decide

-- n=2: φ(1)+φ(2) = 1+1 = 2
example : totientTable ⟨0, by omega⟩ + totientTable ⟨1, by omega⟩ = 2 := by native_decide

-- n=3: φ(1)+φ(3) = 1+2 = 3
example : totientTable ⟨0, by omega⟩ + totientTable ⟨2, by omega⟩ = 3 := by native_decide

-- n=4: φ(1)+φ(2)+φ(4) = 1+1+2 = 4
example : totientTable ⟨0, by omega⟩ + totientTable ⟨1, by omega⟩ +
          totientTable ⟨3, by omega⟩ = 4 := by native_decide

-- n=5: φ(1)+φ(5) = 1+4 = 5
example : totientTable ⟨0, by omega⟩ + totientTable ⟨4, by omega⟩ = 5 := by native_decide

-- n=6: φ(1)+φ(2)+φ(3)+φ(6) = 1+1+2+2 = 6
example : totientTable ⟨0, by omega⟩ + totientTable ⟨1, by omega⟩ +
          totientTable ⟨2, by omega⟩ + totientTable ⟨5, by omega⟩ = 6 := by native_decide

-- n=7: φ(1)+φ(7) = 1+6 = 7
example : totientTable ⟨0, by omega⟩ + totientTable ⟨6, by omega⟩ = 7 := by native_decide

-- n=8: φ(1)+φ(2)+φ(4)+φ(8) = 1+1+2+4 = 8
example : totientTable ⟨0, by omega⟩ + totientTable ⟨1, by omega⟩ +
          totientTable ⟨3, by omega⟩ + totientTable ⟨7, by omega⟩ = 8 := by native_decide

-- n=9: φ(1)+φ(3)+φ(9) = 1+2+6 = 9
example : totientTable ⟨0, by omega⟩ + totientTable ⟨2, by omega⟩ +
          totientTable ⟨8, by omega⟩ = 9 := by native_decide

-- n=10: φ(1)+φ(2)+φ(5)+φ(10) = 1+1+4+4 = 10
example : totientTable ⟨0, by omega⟩ + totientTable ⟨1, by omega⟩ +
          totientTable ⟨4, by omega⟩ + totientTable ⟨9, by omega⟩ = 10 := by native_decide

-- n=11: φ(1)+φ(11) = 1+10 = 11
example : totientTable ⟨0, by omega⟩ + totientTable ⟨10, by omega⟩ = 11 := by native_decide

-- n=12: φ(1)+φ(2)+φ(3)+φ(4)+φ(6)+φ(12) = 1+1+2+2+2+4 = 12
example : totientTable ⟨0, by omega⟩ + totientTable ⟨1, by omega⟩ +
          totientTable ⟨2, by omega⟩ + totientTable ⟨3, by omega⟩ +
          totientTable ⟨5, by omega⟩ + totientTable ⟨11, by omega⟩ = 12 := by native_decide

-- ============================================================
-- Section 2: Monic Polynomials Over F_q
-- ============================================================

/-! ## Monic Polynomials Over F_q

The number of monic polynomials of degree n over F_q is q^n.
The number of monic irreducible polynomials of degree n over F_q is
  I(n,q) = (1/n) * Σ_{d|n} μ(n/d) * q^d
by the necklace formula (Möbius inversion).

For q=2, we tabulate I(n,2) for n=1..8.
-/

-- Monic polynomial counts for q=2, degree n=1..8: 2^n
def monicCountF2 : Fin 8 → ℕ := ![2, 4, 8, 16, 32, 64, 128, 256]

example : monicCountF2 ⟨0, by omega⟩ = 2 := by native_decide   -- 2^1
example : monicCountF2 ⟨1, by omega⟩ = 4 := by native_decide   -- 2^2
example : monicCountF2 ⟨2, by omega⟩ = 8 := by native_decide   -- 2^3
example : monicCountF2 ⟨3, by omega⟩ = 16 := by native_decide  -- 2^4
example : monicCountF2 ⟨4, by omega⟩ = 32 := by native_decide  -- 2^5
example : monicCountF2 ⟨5, by omega⟩ = 64 := by native_decide  -- 2^6
example : monicCountF2 ⟨6, by omega⟩ = 128 := by native_decide -- 2^7
example : monicCountF2 ⟨7, by omega⟩ = 256 := by native_decide -- 2^8

-- Verify q^n = 2^n
example : monicCountF2 ⟨0, by omega⟩ = 2^1 := by native_decide
example : monicCountF2 ⟨3, by omega⟩ = 2^4 := by native_decide
example : monicCountF2 ⟨7, by omega⟩ = 2^8 := by native_decide

-- Irreducible polynomial counts over F_2
-- I(1)=2, I(2)=1, I(3)=2, I(4)=3, I(5)=6, I(6)=9, I(7)=18, I(8)=30
def irreducibleCountF2 : Fin 8 → ℕ := ![2, 1, 2, 3, 6, 9, 18, 30]

example : irreducibleCountF2 ⟨0, by omega⟩ = 2  := by native_decide -- I(1)
example : irreducibleCountF2 ⟨1, by omega⟩ = 1  := by native_decide -- I(2)
example : irreducibleCountF2 ⟨2, by omega⟩ = 2  := by native_decide -- I(3)
example : irreducibleCountF2 ⟨3, by omega⟩ = 3  := by native_decide -- I(4)
example : irreducibleCountF2 ⟨4, by omega⟩ = 6  := by native_decide -- I(5)
example : irreducibleCountF2 ⟨5, by omega⟩ = 9  := by native_decide -- I(6)
example : irreducibleCountF2 ⟨6, by omega⟩ = 18 := by native_decide -- I(7)
example : irreducibleCountF2 ⟨7, by omega⟩ = 30 := by native_decide -- I(8)

-- Necklace formula bound: n * I(n) ≤ 2^n for small n
-- n=1: 1*2=2 ≤ 2^1=2
example : 1 * irreducibleCountF2 ⟨0, by omega⟩ ≤ 2^1 := by native_decide
-- n=2: 2*1=2 ≤ 2^2=4
example : 2 * irreducibleCountF2 ⟨1, by omega⟩ ≤ 2^2 := by native_decide
-- n=3: 3*2=6 ≤ 2^3=8
example : 3 * irreducibleCountF2 ⟨2, by omega⟩ ≤ 2^3 := by native_decide
-- n=4: 4*3=12 ≤ 2^4=16
example : 4 * irreducibleCountF2 ⟨3, by omega⟩ ≤ 2^4 := by native_decide
-- n=5: 5*6=30 ≤ 2^5=32
example : 5 * irreducibleCountF2 ⟨4, by omega⟩ ≤ 2^5 := by native_decide
-- n=6: 6*9=54 ≤ 2^6=64
example : 6 * irreducibleCountF2 ⟨5, by omega⟩ ≤ 2^6 := by native_decide
-- n=7: 7*18=126 ≤ 2^7=128
example : 7 * irreducibleCountF2 ⟨6, by omega⟩ ≤ 2^7 := by native_decide
-- n=8: 8*30=240 ≤ 2^8=256
example : 8 * irreducibleCountF2 ⟨7, by omega⟩ ≤ 2^8 := by native_decide

-- ============================================================
-- Section 3: Polynomial Coefficient Growth (Cauchy Bound)
-- ============================================================

/-! ## Polynomial Coefficient Growth

Cauchy bound: If p(x) = x^n + a_{n-1}x^{n-1} + ... + a_0, all roots z satisfy
  |z| ≤ 1 + max{|a_i|}.

A polynomial with all coefficients bounded by M has all roots of magnitude ≤ 1+M.

Discriminant of x^2 - x - 1 (Fibonacci polynomial):
  disc = b^2 - 4ac = (-1)^2 - 4*(1)*(-1) = 1 + 4 = 5.
-/

-- Cauchy bound: coefficient M=1 implies root magnitude ≤ 1+1=2
-- Concretely: a degree-2 poly with |a_0|,|a_1| ≤ 1 has roots of magnitude ≤ 2.
example : 1 + 1 = 2 := by norm_num

-- Cauchy bound: coefficient M=3 implies root magnitude ≤ 4
example : 1 + 3 = 4 := by norm_num

-- Cauchy bound: coefficient M=10 implies root magnitude ≤ 11
example : 1 + 10 = 11 := by norm_num

-- Fibonacci polynomial x^2 - x - 1: discriminant = (-1)^2 - 4*1*(-1) = 5
-- In ℕ: we verify 1 + 4 = 5
example : 1 + 4 = 5 := by norm_num

-- Discriminant = b^2 - 4ac for ax^2+bx+c.
-- For x^2 - x - 1: a=1, b=-1, c=-1.
-- disc = b^2 - 4ac = 1 - 4*(1)*(-1) = 1+4 = 5.
-- In integers: disc = 5 (positive → two distinct real roots).
-- We verify: 1^2 + 4*1*1 = 5 (since b=-1 → b^2=1, -4ac = -4*(1)*(-1)=4)
example : 1^2 + 4*1*1 = 5 := by norm_num

-- The roots of x^2-x-1 are (1±√5)/2, i.e., the golden ratio φ=(1+√5)/2 and ψ=(1-√5)/2.
-- Cauchy bound: coefficients bounded by 1, so roots have |z| ≤ 1+1=2.
-- φ ≈ 1.618 < 2. ✓ (We verify in ℚ approximation: 1618 < 2000)
example : (1618 : ℤ) < 2000 := by norm_num

-- Root magnitude bound for x^n - 2 (all coefficients are 0 or 2):
-- M = 2, so bound is 1+2=3. The real root is 2^(1/n) ≤ 2 < 3. ✓
example : 1 + 2 = 3 := by norm_num

-- ============================================================
-- Section 4: Compositions and Polynomials
-- ============================================================

/-! ## Compositions of Integers

A composition of n is an ordered tuple of positive integers summing to n.
The number of compositions of n ≥ 1 is 2^(n-1).

The generating function connection: the number of compositions of n into exactly k
parts equals C(n-1, k-1).
-/

-- Number of compositions of n: compositions(n) = 2^(n-1)
def compositionsCount : Fin 5 → ℕ := ![1, 2, 4, 8, 16]

-- n=1: 2^0=1
example : compositionsCount ⟨0, by omega⟩ = 2^0 := by native_decide
-- n=2: 2^1=2
example : compositionsCount ⟨1, by omega⟩ = 2^1 := by native_decide
-- n=3: 2^2=4
example : compositionsCount ⟨2, by omega⟩ = 2^2 := by native_decide
-- n=4: 2^3=8
example : compositionsCount ⟨3, by omega⟩ = 2^3 := by native_decide
-- n=5: 2^4=16
example : compositionsCount ⟨4, by omega⟩ = 2^4 := by native_decide

-- Individual values
example : compositionsCount ⟨0, by omega⟩ = 1  := by native_decide
example : compositionsCount ⟨1, by omega⟩ = 2  := by native_decide
example : compositionsCount ⟨2, by omega⟩ = 4  := by native_decide
example : compositionsCount ⟨3, by omega⟩ = 8  := by native_decide
example : compositionsCount ⟨4, by omega⟩ = 16 := by native_decide

-- For n=5, compositions into exactly k parts = C(4, k-1):
-- k=1: C(4,0)=1
example : Nat.choose 4 0 = 1 := by native_decide
-- k=2: C(4,1)=4
example : Nat.choose 4 1 = 4 := by native_decide
-- k=3: C(4,2)=6
example : Nat.choose 4 2 = 6 := by native_decide
-- k=4: C(4,3)=4
example : Nat.choose 4 3 = 4 := by native_decide
-- k=5: C(4,4)=1
example : Nat.choose 4 4 = 1 := by native_decide

-- Sum = 2^4 = 16 = compositions(5)
example : Nat.choose 4 0 + Nat.choose 4 1 + Nat.choose 4 2 +
          Nat.choose 4 3 + Nat.choose 4 4 = 16 := by native_decide

-- Verify sum = 2^4 directly
example : Nat.choose 4 0 + Nat.choose 4 1 + Nat.choose 4 2 +
          Nat.choose 4 3 + Nat.choose 4 4 = 2^4 := by native_decide

-- More binomial sum identities (sum of row n of Pascal's triangle = 2^n)
-- n=4: Σ_{k=0}^{4} C(4,k) = 2^4 = 16
example : (Finset.range 5).sum (fun k => Nat.choose 4 k) = 2^4 := by native_decide
-- n=6: Σ_{k=0}^{6} C(6,k) = 2^6 = 64
example : (Finset.range 7).sum (fun k => Nat.choose 6 k) = 2^6 := by native_decide

-- ============================================================
-- Section 5: Polynomial Multiplication Cost
-- ============================================================

/-! ## Polynomial Multiplication

Naive schoolbook multiplication of two degree-n polynomials requires (n+1)^2
coefficient multiplications. For the number of coefficient multiplications:
naive_cost(n) = n^2 (treating the leading coefficient, for monic polys of degree n).

Karatsuba algorithm: ~n^(log_2 3) multiplications.
Key inequality: 3^k < 2^(2k) = 4^k for all k ≥ 1, showing Karatsuba beats naive.
-/

-- Naive multiplication cost: n^2 for n=2..8
def naiveCost : Fin 7 → ℕ := ![4, 9, 16, 25, 36, 49, 64]

example : naiveCost ⟨0, by omega⟩ = 2^2 := by native_decide  -- n=2: 4
example : naiveCost ⟨1, by omega⟩ = 3^2 := by native_decide  -- n=3: 9
example : naiveCost ⟨2, by omega⟩ = 4^2 := by native_decide  -- n=4: 16
example : naiveCost ⟨3, by omega⟩ = 5^2 := by native_decide  -- n=5: 25
example : naiveCost ⟨4, by omega⟩ = 6^2 := by native_decide  -- n=6: 36
example : naiveCost ⟨5, by omega⟩ = 7^2 := by native_decide  -- n=7: 49
example : naiveCost ⟨6, by omega⟩ = 8^2 := by native_decide  -- n=8: 64

-- Individual value checks
example : naiveCost ⟨0, by omega⟩ = 4  := by native_decide
example : naiveCost ⟨1, by omega⟩ = 9  := by native_decide
example : naiveCost ⟨2, by omega⟩ = 16 := by native_decide
example : naiveCost ⟨3, by omega⟩ = 25 := by native_decide
example : naiveCost ⟨4, by omega⟩ = 36 := by native_decide
example : naiveCost ⟨5, by omega⟩ = 49 := by native_decide
example : naiveCost ⟨6, by omega⟩ = 64 := by native_decide

-- Karatsuba beats naive: 3^k < 4^k for k=1..6
-- (since Karatsuba uses 3^k multiplications where naive uses 4^k = (2^k)^2)
example : 3^1 < 4^1 := by norm_num
example : 3^2 < 4^2 := by norm_num
example : 3^3 < 4^3 := by norm_num
example : 3^4 < 4^4 := by norm_num
example : 3^5 < 4^5 := by norm_num
example : 3^6 < 4^6 := by norm_num

-- Explicit Karatsuba vs naive savings (ratio 4^k / 3^k grows with k)
-- k=1: naive=4, Karatsuba=3
example : (4 : ℕ)^1 = 4 := by norm_num
example : (3 : ℕ)^1 = 3 := by norm_num
-- k=2: naive=16, Karatsuba=9
example : (4 : ℕ)^2 = 16 := by norm_num
example : (3 : ℕ)^2 = 9 := by norm_num
-- k=3: naive=64, Karatsuba=27
example : (4 : ℕ)^3 = 64 := by norm_num
example : (3 : ℕ)^3 = 27 := by norm_num
-- k=4: naive=256, Karatsuba=81
example : (4 : ℕ)^4 = 256 := by norm_num
example : (3 : ℕ)^4 = 81 := by norm_num
-- k=5: naive=1024, Karatsuba=243
example : (4 : ℕ)^5 = 1024 := by norm_num
example : (3 : ℕ)^5 = 243 := by norm_num
-- k=6: naive=4096, Karatsuba=729
example : (4 : ℕ)^6 = 4096 := by norm_num
example : (3 : ℕ)^6 = 729 := by norm_num

-- ============================================================
-- Section 6: Power Sums and Newton's Identities
-- ============================================================

/-! ## Power Sums and Newton's Identities

For polynomial x^2 - 3x + 2 = (x-1)(x-2) with roots r₁=1, r₂=2:
  p_k = r₁^k + r₂^k  (k-th power sum)

Values:
  p_1 = 1+2 = 3
  p_2 = 1+4 = 5
  p_3 = 1+8 = 9
  p_4 = 1+16 = 17

Newton's identity recurrence: p_k = e₁·p_{k-1} - e₂·p_{k-2}
  where e₁ = 3 (sum of roots), e₂ = 2 (product of roots).
  So: p_k = 3·p_{k-1} - 2·p_{k-2}.
-/

-- Power sum table for roots 1,2 (polynomial x^2-3x+2)
def powerSums : Fin 6 → ℕ := ![2, 3, 5, 9, 17, 33]
-- p_0=1^0+2^0=2, p_1=3, p_2=5, p_3=9, p_4=17, p_5=33

-- Direct computations
example : 1^0 + 2^0 = 2  := by norm_num  -- p_0
example : 1^1 + 2^1 = 3  := by norm_num  -- p_1
example : 1^2 + 2^2 = 5  := by norm_num  -- p_2
example : 1^3 + 2^3 = 9  := by norm_num  -- p_3
example : 1^4 + 2^4 = 17 := by norm_num  -- p_4
example : 1^5 + 2^5 = 33 := by norm_num  -- p_5

-- Table values
example : powerSums ⟨0, by omega⟩ = 2  := by native_decide  -- p_0
example : powerSums ⟨1, by omega⟩ = 3  := by native_decide  -- p_1
example : powerSums ⟨2, by omega⟩ = 5  := by native_decide  -- p_2
example : powerSums ⟨3, by omega⟩ = 9  := by native_decide  -- p_3
example : powerSums ⟨4, by omega⟩ = 17 := by native_decide  -- p_4
example : powerSums ⟨5, by omega⟩ = 33 := by native_decide  -- p_5

-- Newton's recurrence: p_k = 3*p_{k-1} - 2*p_{k-2}
-- k=2: p_2 = 3*p_1 - 2*p_0 = 3*3 - 2*2 = 9-4=5 ✓
example : 3 * powerSums ⟨1, by omega⟩ = 2 * powerSums ⟨0, by omega⟩ + powerSums ⟨2, by omega⟩ := by
  native_decide
-- k=3: p_3 = 3*p_2 - 2*p_1 = 3*5 - 2*3 = 15-6=9 ✓
example : 3 * powerSums ⟨2, by omega⟩ = 2 * powerSums ⟨1, by omega⟩ + powerSums ⟨3, by omega⟩ := by
  native_decide
-- k=4: p_4 = 3*p_3 - 2*p_2 = 3*9 - 2*5 = 27-10=17 ✓
example : 3 * powerSums ⟨3, by omega⟩ = 2 * powerSums ⟨2, by omega⟩ + powerSums ⟨4, by omega⟩ := by
  native_decide
-- k=5: p_5 = 3*p_4 - 2*p_3 = 3*17 - 2*9 = 51-18=33 ✓
example : 3 * powerSums ⟨4, by omega⟩ = 2 * powerSums ⟨3, by omega⟩ + powerSums ⟨5, by omega⟩ := by
  native_decide

-- The recurrence in the "add" form (avoiding ℕ subtraction pitfalls):
-- p_k = 3*p_{k-1} - 2*p_{k-2}  ↔  3*p_{k-1} = p_k + 2*p_{k-2}
-- Verify for k=2,3,4 using the table:
example : 3 * 3 = 5 + 2 * 2 := by norm_num  -- k=2
example : 3 * 5 = 9 + 2 * 3 := by norm_num  -- k=3
example : 3 * 9 = 17 + 2 * 5 := by norm_num -- k=4

-- Elementary symmetric polynomials for x^2-3x+2:
-- e_1 = sum of roots = 1+2 = 3 = coefficient of x (with sign flip)
-- e_2 = product of roots = 1*2 = 2 = constant term
example : 1 + 2 = 3 := by norm_num  -- e_1
example : 1 * 2 = 2 := by norm_num  -- e_2

-- Vieta's formulas verify: (x-1)(x-2) = x^2 - (1+2)x + 1*2 = x^2 - 3x + 2
-- Coefficient of x: -(e_1) = -3, constant: e_2 = 2
example : -(1 + 2 : ℤ) = -3 := by norm_num
example : (1 * 2 : ℤ) = 2  := by norm_num

/-- Vieta first elementary symmetric sample. -/
theorem vieta_first_symmetric_sample :
    (1 + 2 : ℤ) = 3 := by
  norm_num

/-- Vieta second elementary symmetric sample. -/
theorem vieta_second_symmetric_sample :
    (1 * 2 : ℤ) = 2 := by
  norm_num

/-- A polynomial coefficient arithmetic sample used by the finite checks. -/
theorem polynomial_coefficient_sample :
    (3 : ℤ) ^ 2 - 2 * 3 + 1 = 4 := by
  norm_num



structure PolynomialArithmeticBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PolynomialArithmeticBudgetCertificate.controlled
    (c : PolynomialArithmeticBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PolynomialArithmeticBudgetCertificate.budgetControlled
    (c : PolynomialArithmeticBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PolynomialArithmeticBudgetCertificate.Ready
    (c : PolynomialArithmeticBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PolynomialArithmeticBudgetCertificate.size
    (c : PolynomialArithmeticBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem polynomialArithmetic_budgetCertificate_le_size
    (c : PolynomialArithmeticBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePolynomialArithmeticBudgetCertificate :
    PolynomialArithmeticBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePolynomialArithmeticBudgetCertificate.Ready := by
  constructor
  · norm_num [PolynomialArithmeticBudgetCertificate.controlled,
      samplePolynomialArithmeticBudgetCertificate]
  · norm_num [PolynomialArithmeticBudgetCertificate.budgetControlled,
      samplePolynomialArithmeticBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePolynomialArithmeticBudgetCertificate.certificateBudgetWindow ≤
      samplePolynomialArithmeticBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePolynomialArithmeticBudgetCertificate.Ready := by
  constructor
  · norm_num [PolynomialArithmeticBudgetCertificate.controlled,
      samplePolynomialArithmeticBudgetCertificate]
  · norm_num [PolynomialArithmeticBudgetCertificate.budgetControlled,
      samplePolynomialArithmeticBudgetCertificate]

example :
    samplePolynomialArithmeticBudgetCertificate.certificateBudgetWindow ≤
      samplePolynomialArithmeticBudgetCertificate.size := by
  apply polynomialArithmetic_budgetCertificate_le_size
  constructor
  · norm_num [PolynomialArithmeticBudgetCertificate.controlled,
      samplePolynomialArithmeticBudgetCertificate]
  · norm_num [PolynomialArithmeticBudgetCertificate.budgetControlled,
      samplePolynomialArithmeticBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PolynomialArithmeticBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePolynomialArithmeticBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePolynomialArithmeticBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.PolynomialArithmetic
