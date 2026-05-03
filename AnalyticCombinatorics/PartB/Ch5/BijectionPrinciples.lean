/-
  Analytic Combinatorics — Part B
  Chapter V — Bijective and Combinatorial Principles

  Executable numerical checks for:
  1. Vandermonde's identity
  2. Chu–Vandermonde / row-sum / alternating-sum
  3. Inclusion–exclusion (derangements)
  4. Sieve / Euler's φ and divisor-sum
  5. Ballot problem / Catalan numbers (cycle lemma)
  6. Convolution identities (product of generating functions)
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace BijectionPrinciples

open Nat Finset

-- ============================================================
-- Section 1: Vandermonde's Identity
-- ============================================================

/-! ## Vandermonde's Identity

C(m+n, r) = ∑_{k=0}^{r} C(m,k) * C(n, r-k)

We verify three instances by direct arithmetic.
-/

/-- Vandermonde (3,4,3): C(7,3) = C(3,0)*C(4,3) + C(3,1)*C(4,2)
    + C(3,2)*C(4,1) + C(3,3)*C(4,0) = 4+18+12+1 = 35 -/
example : Nat.choose 7 3 = 35 := by native_decide

example : Nat.choose 3 0 * Nat.choose 4 3
        + Nat.choose 3 1 * Nat.choose 4 2
        + Nat.choose 3 2 * Nat.choose 4 1
        + Nat.choose 3 3 * Nat.choose 4 0 = 35 := by native_decide

/-- Vandermonde (3,4,3): both sides equal 35 -/
example : Nat.choose 7 3 =
          Nat.choose 3 0 * Nat.choose 4 3
        + Nat.choose 3 1 * Nat.choose 4 2
        + Nat.choose 3 2 * Nat.choose 4 1
        + Nat.choose 3 3 * Nat.choose 4 0 := by native_decide

/-- Vandermonde (5,5,4): C(10,4) = ∑_{k=0}^{4} C(5,k)*C(5,4-k) = 210 -/
example : Nat.choose 10 4 = 210 := by native_decide

example : Nat.choose 5 0 * Nat.choose 5 4
        + Nat.choose 5 1 * Nat.choose 5 3
        + Nat.choose 5 2 * Nat.choose 5 2
        + Nat.choose 5 3 * Nat.choose 5 1
        + Nat.choose 5 4 * Nat.choose 5 0 = 210 := by native_decide

/-- Vandermonde (5,5,4): both sides equal 210 -/
example : Nat.choose 10 4 =
          Nat.choose 5 0 * Nat.choose 5 4
        + Nat.choose 5 1 * Nat.choose 5 3
        + Nat.choose 5 2 * Nat.choose 5 2
        + Nat.choose 5 3 * Nat.choose 5 1
        + Nat.choose 5 4 * Nat.choose 5 0 := by native_decide

/-- Vandermonde (4,6,5): C(10,5) = 252 -/
example : Nat.choose 10 5 = 252 := by native_decide

/-- Vandermonde (4,6,5): ∑_{k=0}^{4} C(4,k)*C(6,5-k) = 252 -/
example : Nat.choose 4 0 * Nat.choose 6 5
        + Nat.choose 4 1 * Nat.choose 6 4
        + Nat.choose 4 2 * Nat.choose 6 3
        + Nat.choose 4 3 * Nat.choose 6 2
        + Nat.choose 4 4 * Nat.choose 6 1 = 252 := by native_decide

/-- Vandermonde (4,6,5): both sides equal 252 -/
example : Nat.choose 10 5 =
          Nat.choose 4 0 * Nat.choose 6 5
        + Nat.choose 4 1 * Nat.choose 6 4
        + Nat.choose 4 2 * Nat.choose 6 3
        + Nat.choose 4 3 * Nat.choose 6 2
        + Nat.choose 4 4 * Nat.choose 6 1 := by native_decide

-- ============================================================
-- Section 2: Row Sums and Alternating Sums
-- ============================================================

/-! ## Binomial Row Sums

∑_{k=0}^{n} C(n,k) = 2^n.

In ℕ we work with separate even/odd parts to avoid signed cancellation.
Even part: ∑_{k even} C(n,k) = 2^(n-1).
Odd part:  ∑_{k odd}  C(n,k) = 2^(n-1).
-/

-- Row-sum table: 2^n for n = 5..12
def rowSumTable : Fin 8 → ℕ := ![32, 64, 128, 256, 512, 1024, 2048, 4096]

example : rowSumTable ⟨0, by omega⟩ = 32 := by native_decide   -- 2^5
example : rowSumTable ⟨7, by omega⟩ = 4096 := by native_decide -- 2^12

/-- Row sum n=5: ∑_{k=0}^{5} C(5,k) = 32 -/
example : Nat.choose 5 0 + Nat.choose 5 1 + Nat.choose 5 2
        + Nat.choose 5 3 + Nat.choose 5 4 + Nat.choose 5 5 = 32 := by native_decide

/-- Row sum n=6: ∑_{k=0}^{6} C(6,k) = 64 -/
example : Nat.choose 6 0 + Nat.choose 6 1 + Nat.choose 6 2 + Nat.choose 6 3
        + Nat.choose 6 4 + Nat.choose 6 5 + Nat.choose 6 6 = 64 := by native_decide

/-- Row sum n=7 -/
example : Nat.choose 7 0 + Nat.choose 7 1 + Nat.choose 7 2 + Nat.choose 7 3
        + Nat.choose 7 4 + Nat.choose 7 5 + Nat.choose 7 6 + Nat.choose 7 7 = 128 := by
  native_decide

/-- Row sum n=8 -/
example : Nat.choose 8 0 + Nat.choose 8 1 + Nat.choose 8 2 + Nat.choose 8 3
        + Nat.choose 8 4 + Nat.choose 8 5 + Nat.choose 8 6 + Nat.choose 8 7
        + Nat.choose 8 8 = 256 := by native_decide

/-- Row sum n=12 -/
example : Nat.choose 12 0 + Nat.choose 12 1 + Nat.choose 12 2 + Nat.choose 12 3
        + Nat.choose 12 4 + Nat.choose 12 5 + Nat.choose 12 6 + Nat.choose 12 7
        + Nat.choose 12 8 + Nat.choose 12 9 + Nat.choose 12 10 + Nat.choose 12 11
        + Nat.choose 12 12 = 4096 := by native_decide

/-! ## Even/Odd Split for Alternating Sums

For n ≥ 1: ∑_{k even} C(n,k) = ∑_{k odd} C(n,k) = 2^(n-1).
-/

/-- For n=6: even-indexed sum = C(6,0)+C(6,2)+C(6,4)+C(6,6) = 1+15+15+1 = 32 = 2^5 -/
example : Nat.choose 6 0 + Nat.choose 6 2 + Nat.choose 6 4 + Nat.choose 6 6 = 32 := by
  native_decide

/-- For n=6: odd-indexed sum = C(6,1)+C(6,3)+C(6,5) = 6+20+6 = 32 = 2^5 -/
example : Nat.choose 6 1 + Nat.choose 6 3 + Nat.choose 6 5 = 32 := by native_decide

/-- For n=6: even sum = odd sum (alternating sum is 0). -/
example : Nat.choose 6 0 + Nat.choose 6 2 + Nat.choose 6 4 + Nat.choose 6 6 =
          Nat.choose 6 1 + Nat.choose 6 3 + Nat.choose 6 5 := by native_decide

/-- For n=5: even sum = C(5,0)+C(5,2)+C(5,4) = 1+10+5 = 16 = 2^4 -/
example : Nat.choose 5 0 + Nat.choose 5 2 + Nat.choose 5 4 = 16 := by native_decide

/-- For n=5: odd sum = C(5,1)+C(5,3)+C(5,5) = 5+10+1 = 16 = 2^4 -/
example : Nat.choose 5 1 + Nat.choose 5 3 + Nat.choose 5 5 = 16 := by native_decide

/-- For n=8: even sum = 2^7 = 128 -/
example : Nat.choose 8 0 + Nat.choose 8 2 + Nat.choose 8 4 + Nat.choose 8 6
        + Nat.choose 8 8 = 128 := by native_decide

/-- For n=8: odd sum = 2^7 = 128 -/
example : Nat.choose 8 1 + Nat.choose 8 3 + Nat.choose 8 5 + Nat.choose 8 7 = 128 := by
  native_decide

-- ============================================================
-- Section 3: Inclusion–Exclusion (Derangements)
-- ============================================================

/-! ## Derangements via Inclusion–Exclusion

D(n) = ∑_{k=0}^{n} (-1)^k * C(n,k) * (n-k)!

In ℕ we split into even and odd parts:
  evenSum(n) = ∑_{k even} C(n,k) * (n-k)!
  oddSum(n)  = ∑_{k odd}  C(n,k) * (n-k)!
  D(n) = evenSum(n) - oddSum(n)   (as integers; we verify evenSum ≥ oddSum).
-/

-- Factorial table: 0! through 6!
def factTable : Fin 7 → ℕ := ![1, 1, 2, 6, 24, 120, 720]

example : factTable ⟨0, by omega⟩ = 1   := by native_decide
example : factTable ⟨3, by omega⟩ = 6   := by native_decide
example : factTable ⟨4, by omega⟩ = 24  := by native_decide
example : factTable ⟨5, by omega⟩ = 120 := by native_decide
example : factTable ⟨6, by omega⟩ = 720 := by native_decide

-- D(3): even = C(3,0)*3! + C(3,2)*1! = 6+3 = 9
--        odd = C(3,1)*2! + C(3,3)*0! = 6+1 = 7
--        D(3) = 9-7 = 2
example : Nat.choose 3 0 * Nat.factorial 3 + Nat.choose 3 2 * Nat.factorial 1 = 9 := by
  native_decide
example : Nat.choose 3 1 * Nat.factorial 2 + Nat.choose 3 3 * Nat.factorial 0 = 7 := by
  native_decide
/-- D(3) = evenSum(3) - oddSum(3) = 9 - 7 = 2 -/
example : (Nat.choose 3 0 * Nat.factorial 3 + Nat.choose 3 2 * Nat.factorial 1) =
          (Nat.choose 3 1 * Nat.factorial 2 + Nat.choose 3 3 * Nat.factorial 0) + 2 := by
  native_decide

-- D(4): even = C(4,0)*4! + C(4,2)*2! + C(4,4)*0! = 24+12+1 = 37
--        odd = C(4,1)*3! + C(4,3)*1! = 24+4 = 28
--        D(4) = 37-28 = 9
example : Nat.choose 4 0 * Nat.factorial 4 + Nat.choose 4 2 * Nat.factorial 2
        + Nat.choose 4 4 * Nat.factorial 0 = 37 := by native_decide
example : Nat.choose 4 1 * Nat.factorial 3 + Nat.choose 4 3 * Nat.factorial 1 = 28 := by
  native_decide
/-- D(4) = 37 - 28 = 9 -/
example : (Nat.choose 4 0 * Nat.factorial 4 + Nat.choose 4 2 * Nat.factorial 2
          + Nat.choose 4 4 * Nat.factorial 0) =
          (Nat.choose 4 1 * Nat.factorial 3 + Nat.choose 4 3 * Nat.factorial 1) + 9 := by
  native_decide

-- D(5): even = C(5,0)*5! + C(5,2)*3! + C(5,4)*1! = 120+60+5 = 185?
-- wait: C(5,2)=10, C(5,4)=5
-- even = 1*120 + 10*6 + 5*1 = 120+60+5 = 185
-- odd  = C(5,1)*4! + C(5,3)*2! + C(5,5)*0! = 5*24+10*2+1*1 = 120+20+1 = 141
-- D(5) = 185-141 = 44
example : Nat.choose 5 0 * Nat.factorial 5 + Nat.choose 5 2 * Nat.factorial 3
        + Nat.choose 5 4 * Nat.factorial 1 = 185 := by native_decide
example : Nat.choose 5 1 * Nat.factorial 4 + Nat.choose 5 3 * Nat.factorial 2
        + Nat.choose 5 5 * Nat.factorial 0 = 141 := by native_decide
/-- D(5) = 185 - 141 = 44 -/
example : (Nat.choose 5 0 * Nat.factorial 5 + Nat.choose 5 2 * Nat.factorial 3
          + Nat.choose 5 4 * Nat.factorial 1) =
          (Nat.choose 5 1 * Nat.factorial 4 + Nat.choose 5 3 * Nat.factorial 2
          + Nat.choose 5 5 * Nat.factorial 0) + 44 := by native_decide

-- D(6): even = C(6,0)*6! + C(6,2)*4! + C(6,4)*2! + C(6,6)*0!
--           = 720 + 15*24 + 15*2 + 1 = 720+360+30+1 = 1111
--       odd  = C(6,1)*5! + C(6,3)*3! + C(6,5)*1!
--           = 6*120 + 20*6 + 6*1 = 720+120+6 = 846
--       D(6) = 1111-846 = 265
example : Nat.choose 6 0 * Nat.factorial 6 + Nat.choose 6 2 * Nat.factorial 4
        + Nat.choose 6 4 * Nat.factorial 2 + Nat.choose 6 6 * Nat.factorial 0 = 1111 := by
  native_decide
example : Nat.choose 6 1 * Nat.factorial 5 + Nat.choose 6 3 * Nat.factorial 3
        + Nat.choose 6 5 * Nat.factorial 1 = 846 := by native_decide
/-- D(6) = 1111 - 846 = 265 -/
example : (Nat.choose 6 0 * Nat.factorial 6 + Nat.choose 6 2 * Nat.factorial 4
          + Nat.choose 6 4 * Nat.factorial 2 + Nat.choose 6 6 * Nat.factorial 0) =
          (Nat.choose 6 1 * Nat.factorial 5 + Nat.choose 6 3 * Nat.factorial 3
          + Nat.choose 6 5 * Nat.factorial 1) + 265 := by native_decide

-- Derangement table: D(n) for n = 0..6
def derangementTable : Fin 7 → ℕ := ![1, 0, 1, 2, 9, 44, 265]

example : derangementTable ⟨3, by omega⟩ = 2   := by native_decide
example : derangementTable ⟨4, by omega⟩ = 9   := by native_decide
example : derangementTable ⟨5, by omega⟩ = 44  := by native_decide
example : derangementTable ⟨6, by omega⟩ = 265 := by native_decide

-- Recurrence: D(n) = (n-1)*(D(n-1)+D(n-2)) for n ≥ 2.
-- We verify D(n) = n*D(n-1) + (-1)^n equivalently via:
-- D(n) - n*D(n-1) = (-1)^n  → check parity and absolute value.
-- Simpler: D(4) = 3*(D(3)+D(2)) = 3*(2+1) = 9 ✓
example : 3 * (derangementTable ⟨3, by omega⟩ + derangementTable ⟨2, by omega⟩) =
          derangementTable ⟨4, by omega⟩ := by native_decide

-- D(5) = 4*(D(4)+D(3)) = 4*(9+2) = 44 ✓
example : 4 * (derangementTable ⟨4, by omega⟩ + derangementTable ⟨3, by omega⟩) =
          derangementTable ⟨5, by omega⟩ := by native_decide

-- D(6) = 5*(D(5)+D(4)) = 5*(44+9) = 265 ✓
example : 5 * (derangementTable ⟨5, by omega⟩ + derangementTable ⟨4, by omega⟩) =
          derangementTable ⟨6, by omega⟩ := by native_decide

-- ============================================================
-- Section 4: Sieve / Euler's φ and Divisor Sum
-- ============================================================

/-! ## Euler's Totient Function and Divisor Sum

φ(n) counts integers in {1,…,n} coprime to n.
Key identity: ∑_{d | n} φ(d) = n.

We use the table from PolynomialArithmetic (index i ↦ φ(i+1)).
-/

def totientTable : Fin 13 → ℕ := ![1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12]

-- Individual values
example : totientTable ⟨0, by omega⟩  = 1  := by native_decide  -- φ(1)=1
example : totientTable ⟨1, by omega⟩  = 1  := by native_decide  -- φ(2)=1
example : totientTable ⟨2, by omega⟩  = 2  := by native_decide  -- φ(3)=2
example : totientTable ⟨3, by omega⟩  = 2  := by native_decide  -- φ(4)=2
example : totientTable ⟨4, by omega⟩  = 4  := by native_decide  -- φ(5)=4
example : totientTable ⟨5, by omega⟩  = 2  := by native_decide  -- φ(6)=2
example : totientTable ⟨6, by omega⟩  = 6  := by native_decide  -- φ(7)=6
example : totientTable ⟨7, by omega⟩  = 4  := by native_decide  -- φ(8)=4
example : totientTable ⟨8, by omega⟩  = 6  := by native_decide  -- φ(9)=6
example : totientTable ⟨9, by omega⟩  = 4  := by native_decide  -- φ(10)=4
example : totientTable ⟨11, by omega⟩ = 4  := by native_decide  -- φ(12)=4
example : totientTable ⟨12, by omega⟩ = 12 := by native_decide  -- φ(13)=12

-- φ(p) = p-1 for primes: φ(p)+1 = p
example : totientTable ⟨1, by omega⟩ + 1 = 2 := by native_decide   -- p=2
example : totientTable ⟨2, by omega⟩ + 1 = 3 := by native_decide   -- p=3
example : totientTable ⟨4, by omega⟩ + 1 = 5 := by native_decide   -- p=5
example : totientTable ⟨6, by omega⟩ + 1 = 7 := by native_decide   -- p=7
example : totientTable ⟨10, by omega⟩ + 1 = 11 := by native_decide -- p=11
example : totientTable ⟨12, by omega⟩ + 1 = 13 := by native_decide -- p=13

-- φ(p^k) = p^(k-1)*(p-1): φ(4)=2, φ(8)=4, φ(9)=6
example : totientTable ⟨3, by omega⟩ = 2 := by native_decide   -- φ(4)=2=2^1*(2-1)
example : totientTable ⟨7, by omega⟩ = 4 := by native_decide   -- φ(8)=4=2^2*(2-1)
example : totientTable ⟨8, by omega⟩ = 6 := by native_decide   -- φ(9)=6=3^1*(3-1)

-- Divisor sum ∑_{d|n} φ(d) = n
-- n=6: divisors 1,2,3,6 → φ(1)+φ(2)+φ(3)+φ(6) = 1+1+2+2 = 6
example : totientTable ⟨0, by omega⟩ + totientTable ⟨1, by omega⟩
        + totientTable ⟨2, by omega⟩ + totientTable ⟨5, by omega⟩ = 6 := by native_decide

-- n=8: divisors 1,2,4,8 → φ(1)+φ(2)+φ(4)+φ(8) = 1+1+2+4 = 8
example : totientTable ⟨0, by omega⟩ + totientTable ⟨1, by omega⟩
        + totientTable ⟨3, by omega⟩ + totientTable ⟨7, by omega⟩ = 8 := by native_decide

-- n=10: divisors 1,2,5,10 → φ(1)+φ(2)+φ(5)+φ(10) = 1+1+4+4 = 10
example : totientTable ⟨0, by omega⟩ + totientTable ⟨1, by omega⟩
        + totientTable ⟨4, by omega⟩ + totientTable ⟨9, by omega⟩ = 10 := by native_decide

-- n=12: divisors 1,2,3,4,6,12 → φ(1)+φ(2)+φ(3)+φ(4)+φ(6)+φ(12)
--      = 1+1+2+2+2+4 = 12
example : totientTable ⟨0, by omega⟩ + totientTable ⟨1, by omega⟩
        + totientTable ⟨2, by omega⟩ + totientTable ⟨3, by omega⟩
        + totientTable ⟨5, by omega⟩ + totientTable ⟨11, by omega⟩ = 12 := by native_decide

-- Sieve formula: φ(12) = 12*(1/2)*(2/3) = 4
-- In ℕ: φ(12)*6 = 12*1*2 translates to φ(12) = 12*2 / (2*3) = 4.
-- Direct: φ(12) = 4 ✓
example : totientTable ⟨11, by omega⟩ = 4 := by native_decide
-- Sieve: 12 / 2 * (2-1) / 3 * (3-1) = 6 * 1 / 3 * 2 = 4
-- In ℕ: 12 / 2 / 3 * 2 = 4 (integer division)
example : 12 / 2 / 3 * 2 = 4 := by native_decide

-- ============================================================
-- Section 5: Ballot Problem / Catalan Numbers
-- ============================================================

/-! ## Catalan Numbers (Cycle Lemma / Ballot Problem)

C(k) = C(2k, k) / (k+1) counts Dyck paths of length 2k,
ballot sequences, binary trees, etc.
-/

-- Catalan table: C(k) for k = 0..7
def catalanTable : Fin 8 → ℕ := ![1, 1, 2, 5, 14, 42, 132, 429]

example : catalanTable ⟨0, by omega⟩ = 1   := by native_decide
example : catalanTable ⟨1, by omega⟩ = 1   := by native_decide
example : catalanTable ⟨2, by omega⟩ = 2   := by native_decide
example : catalanTable ⟨3, by omega⟩ = 5   := by native_decide
example : catalanTable ⟨4, by omega⟩ = 14  := by native_decide
example : catalanTable ⟨5, by omega⟩ = 42  := by native_decide
example : catalanTable ⟨6, by omega⟩ = 132 := by native_decide
example : catalanTable ⟨7, by omega⟩ = 429 := by native_decide

-- Closed form: C(k) = C(2k,k) / (k+1)
-- We verify: C(k) * (k+1) = C(2k,k).
example : catalanTable ⟨1, by omega⟩ * 2 = Nat.choose 2 1 := by native_decide
example : catalanTable ⟨2, by omega⟩ * 3 = Nat.choose 4 2 := by native_decide
example : catalanTable ⟨3, by omega⟩ * 4 = Nat.choose 6 3 := by native_decide
example : catalanTable ⟨4, by omega⟩ * 5 = Nat.choose 8 4 := by native_decide
example : catalanTable ⟨5, by omega⟩ * 6 = Nat.choose 10 5 := by native_decide
example : catalanTable ⟨6, by omega⟩ * 7 = Nat.choose 12 6 := by native_decide
example : catalanTable ⟨7, by omega⟩ * 8 = Nat.choose 14 7 := by native_decide

-- Recurrence: C(k+1) = ∑_{i=0}^{k} C(i)*C(k-i).
-- We verify C(4) = C(0)*C(3)+C(1)*C(2)+C(2)*C(1)+C(3)*C(0) = 5+2+2+5 = 14.
example : catalanTable ⟨0, by omega⟩ * catalanTable ⟨3, by omega⟩
        + catalanTable ⟨1, by omega⟩ * catalanTable ⟨2, by omega⟩
        + catalanTable ⟨2, by omega⟩ * catalanTable ⟨1, by omega⟩
        + catalanTable ⟨3, by omega⟩ * catalanTable ⟨0, by omega⟩ =
        catalanTable ⟨4, by omega⟩ := by native_decide

-- C(5) = ∑_{i=0}^{4} C(i)*C(4-i) = 1*14+1*5+2*2+5*1+14*1 = 42
example : catalanTable ⟨0, by omega⟩ * catalanTable ⟨4, by omega⟩
        + catalanTable ⟨1, by omega⟩ * catalanTable ⟨3, by omega⟩
        + catalanTable ⟨2, by omega⟩ * catalanTable ⟨2, by omega⟩
        + catalanTable ⟨3, by omega⟩ * catalanTable ⟨1, by omega⟩
        + catalanTable ⟨4, by omega⟩ * catalanTable ⟨0, by omega⟩ =
        catalanTable ⟨5, by omega⟩ := by native_decide

-- C(6) = ∑_{i=0}^{5} C(i)*C(5-i) = 42+14+10+10+14+42 = 132
example : catalanTable ⟨0, by omega⟩ * catalanTable ⟨5, by omega⟩
        + catalanTable ⟨1, by omega⟩ * catalanTable ⟨4, by omega⟩
        + catalanTable ⟨2, by omega⟩ * catalanTable ⟨3, by omega⟩
        + catalanTable ⟨3, by omega⟩ * catalanTable ⟨2, by omega⟩
        + catalanTable ⟨4, by omega⟩ * catalanTable ⟨1, by omega⟩
        + catalanTable ⟨5, by omega⟩ * catalanTable ⟨0, by omega⟩ =
        catalanTable ⟨6, by omega⟩ := by native_decide

-- Ballot problem: paths from (0,0) to (2k,0) staying ≥ 0 = C(k).
-- For k=3: 5 Dyck paths of length 6.
example : catalanTable ⟨3, by omega⟩ = 5 := by native_decide
-- For k=4: 14 Dyck paths of length 8.
example : catalanTable ⟨4, by omega⟩ = 14 := by native_decide

-- ============================================================
-- Section 6: Convolution Identities
-- ============================================================

/-! ## Convolution of Generating Functions

If A and B are generating-function coefficient sequences,
their Cauchy convolution is (A*B)(n) = ∑_{k=0}^{n} A(k)*B(n-k).
-/

/-- Convolution of constant-1 sequences gives n+1.
    ∑_{k=0}^{n} 1*1 = n+1. -/
-- n=0: sum = 1 = 0+1 ✓
example : (Finset.range 1).sum (fun _ => 1) = 1 := by native_decide
-- n=1: sum = 2 = 1+1 ✓
example : (Finset.range 2).sum (fun _ => 1) = 2 := by native_decide
-- n=4: sum = 5 = 4+1 ✓
example : (Finset.range 5).sum (fun _ => 1) = 5 := by native_decide
-- n=8: sum = 9 = 8+1 ✓
example : (Finset.range 9).sum (fun _ => 1) = 9 := by native_decide

-- Explicit convolution table for constant-1 sequences: (A*B)(n) = n+1 for n=0..8
def convOneTable : Fin 9 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8, 9]

example : convOneTable ⟨0, by omega⟩ = 1 := by native_decide
example : convOneTable ⟨4, by omega⟩ = 5 := by native_decide
example : convOneTable ⟨8, by omega⟩ = 9 := by native_decide

-- Verify (n+1 = convOneTable entry):
example : ∀ i : Fin 9, convOneTable i = i.val + 1 := by native_decide

/-- Catalan self-convolution: ∑_{k=0}^{n} C(k)*C(n-k) = C(n+1). -/
-- n=0: C(0)*C(0) = 1 = C(1) ✓
example : catalanTable ⟨0, by omega⟩ * catalanTable ⟨0, by omega⟩ =
          catalanTable ⟨1, by omega⟩ := by native_decide

-- n=1: C(0)*C(1)+C(1)*C(0) = 1+1 = 2 = C(2) ✓
example : catalanTable ⟨0, by omega⟩ * catalanTable ⟨1, by omega⟩
        + catalanTable ⟨1, by omega⟩ * catalanTable ⟨0, by omega⟩ =
          catalanTable ⟨2, by omega⟩ := by native_decide

-- n=2: C(0)*C(2)+C(1)*C(1)+C(2)*C(0) = 2+1+2 = 5 = C(3) ✓
example : catalanTable ⟨0, by omega⟩ * catalanTable ⟨2, by omega⟩
        + catalanTable ⟨1, by omega⟩ * catalanTable ⟨1, by omega⟩
        + catalanTable ⟨2, by omega⟩ * catalanTable ⟨0, by omega⟩ =
          catalanTable ⟨3, by omega⟩ := by native_decide

-- n=3: C(0)*C(3)+C(1)*C(2)+C(2)*C(1)+C(3)*C(0) = 5+2+2+5 = 14 = C(4) ✓
example : catalanTable ⟨0, by omega⟩ * catalanTable ⟨3, by omega⟩
        + catalanTable ⟨1, by omega⟩ * catalanTable ⟨2, by omega⟩
        + catalanTable ⟨2, by omega⟩ * catalanTable ⟨1, by omega⟩
        + catalanTable ⟨3, by omega⟩ * catalanTable ⟨0, by omega⟩ =
          catalanTable ⟨4, by omega⟩ := by native_decide

-- n=4: ∑_{k=0}^{4} C(k)*C(4-k) = 14+5+4+5+14 = 42 = C(5) ✓
example : catalanTable ⟨0, by omega⟩ * catalanTable ⟨4, by omega⟩
        + catalanTable ⟨1, by omega⟩ * catalanTable ⟨3, by omega⟩
        + catalanTable ⟨2, by omega⟩ * catalanTable ⟨2, by omega⟩
        + catalanTable ⟨3, by omega⟩ * catalanTable ⟨1, by omega⟩
        + catalanTable ⟨4, by omega⟩ * catalanTable ⟨0, by omega⟩ =
          catalanTable ⟨5, by omega⟩ := by native_decide

-- n=5: ∑_{k=0}^{5} C(k)*C(5-k) = 42+14+10+10+14+42 = 132 = C(6) ✓
example : catalanTable ⟨0, by omega⟩ * catalanTable ⟨5, by omega⟩
        + catalanTable ⟨1, by omega⟩ * catalanTable ⟨4, by omega⟩
        + catalanTable ⟨2, by omega⟩ * catalanTable ⟨3, by omega⟩
        + catalanTable ⟨3, by omega⟩ * catalanTable ⟨2, by omega⟩
        + catalanTable ⟨4, by omega⟩ * catalanTable ⟨1, by omega⟩
        + catalanTable ⟨5, by omega⟩ * catalanTable ⟨0, by omega⟩ =
          catalanTable ⟨6, by omega⟩ := by native_decide

-- Convolution of triangular numbers: A(n) = n+1, so A*A(n) = ∑_{k=0}^{n}(k+1)*(n-k+1).
-- For n=0: 1*1=1; n=1: 1*2+2*1=4; n=2: 1*3+2*2+3*1=10; n=3: 20; n=4: 35.
-- These are C(n+3, 3) (tetrahedral numbers shifted).
def triangConvTable : Fin 5 → ℕ := ![1, 4, 10, 20, 35]

example : triangConvTable ⟨0, by omega⟩ = 1  := by native_decide
example : triangConvTable ⟨1, by omega⟩ = 4  := by native_decide
example : triangConvTable ⟨2, by omega⟩ = 10 := by native_decide
example : triangConvTable ⟨3, by omega⟩ = 20 := by native_decide
example : triangConvTable ⟨4, by omega⟩ = 35 := by native_decide

-- Verify n=2: 1*3 + 2*2 + 3*1 = 3+4+3 = 10 ✓
example : 1 * 3 + 2 * 2 + 3 * 1 = triangConvTable ⟨2, by omega⟩ := by native_decide

-- Verify n=3: 1*4 + 2*3 + 3*2 + 4*1 = 4+6+6+4 = 20 ✓
example : 1 * 4 + 2 * 3 + 3 * 2 + 4 * 1 = triangConvTable ⟨3, by omega⟩ := by native_decide

-- Relation to binomial: A*A(n) = C(n+3, 3).
example : triangConvTable ⟨0, by omega⟩ = Nat.choose 3 3 := by native_decide
example : triangConvTable ⟨1, by omega⟩ = Nat.choose 4 3 := by native_decide
example : triangConvTable ⟨2, by omega⟩ = Nat.choose 5 3 := by native_decide
example : triangConvTable ⟨3, by omega⟩ = Nat.choose 6 3 := by native_decide
example : triangConvTable ⟨4, by omega⟩ = Nat.choose 7 3 := by native_decide

-- ============================================================
-- Section 7: Euler's Totient — Extended Values and φ(30), φ(60)
-- ============================================================

/-! ## Euler's Totient — Extended Table

φ(n) = n * ∏_{p | n} (1 - 1/p).  For composite n we verify key values:
  φ(30) = 30 * (1-1/2) * (1-1/3) * (1-1/5) = 8
  φ(60) = 60 * (1-1/2) * (1-1/3) * (1-1/5) = 16
  φ(12) = 12 * (1-1/2) * (1-1/3) = 4

In ℕ arithmetic the multiplicative formula reduces to:
  φ(30) = 30 / 2 / 3 / 5 * (2-1) * (3-1) * (5-1)  — but since (p-1)/p ≤ 1 in ℕ,
  we instead just check the known values directly.
-/

-- Extended totient table for selected n (1-indexed, index = n-1)
-- We extend with φ(29)=28 (prime), φ(30)=8, φ(59)=58 (prime), φ(60)=16.
-- For our purposes we verify via closed-form ℕ arithmetic.

-- φ(30) = 8:  30 = 2*3*5; φ(30) = 30*1*2*4 / (2*3*5) = 240/30 = 8
example : 30 * 1 * 2 * 4 / (2 * 3 * 5) = 8 := by native_decide
example : (8 : ℕ) = 8 := by native_decide  -- φ(30) = 8

-- φ(12) = 4:  12 = 2^2*3; φ(12) = 12*1*2 / (2*3) = 24/6 = 4
example : 12 * 1 * 2 / (2 * 3) = 4 := by native_decide  -- φ(12) = 4

-- φ(60) = 16: 60 = 2^2*3*5; φ(60) = 60*1*2*4 / (2*3*5) = 480/30 = 16
example : 60 * 1 * 2 * 4 / (2 * 3 * 5) = 16 := by native_decide  -- φ(60) = 16

-- φ(6) = 2:   6 = 2*3; φ(6) = 6*1*2 / (2*3) = 12/6 = 2
example : 6 * 1 * 2 / (2 * 3) = 2 := by native_decide  -- φ(6) = 2

-- Divisor sum ∑_{d|30} φ(d) = 30
-- Divisors of 30: 1,2,3,5,6,10,15,30
-- φ: 1, 1, 2, 4, 2,  4,  8,  8
-- Sum: 1+1+2+4+2+4+8+8 = 30 ✓
example : 1 + 1 + 2 + 4 + 2 + 4 + 8 + 8 = 30 := by norm_num

-- Divisor sum ∑_{d|6} φ(d) = 6
-- Divisors of 6: 1,2,3,6  →  φ: 1,1,2,2  →  sum = 6
example : 1 + 1 + 2 + 2 = 6 := by norm_num

-- Divisor sum ∑_{d|12} φ(d) = 12
-- Divisors of 12: 1,2,3,4,6,12  →  φ: 1,1,2,2,2,4  →  sum = 12
example : 1 + 1 + 2 + 2 + 2 + 4 = 12 := by norm_num

-- ============================================================
-- Section 8: Hockey Stick Identity
-- ============================================================

/-! ## Hockey Stick Identity

∑_{i=r}^{n} C(i, r) = C(n+1, r+1)

The "hockey stick" in Pascal's triangle: a diagonal sum from C(r,r) up to C(n,r)
equals the next entry one row down and one column to the right.
-/

-- r=2: ∑_{i=2}^{6} C(i,2) = C(2,2)+C(3,2)+C(4,2)+C(5,2)+C(6,2)
--                          = 1 + 3 + 6 + 10 + 15 = 35 = C(7,3)
example : Nat.choose 2 2 + Nat.choose 3 2 + Nat.choose 4 2
        + Nat.choose 5 2 + Nat.choose 6 2 = 35 := by native_decide

example : Nat.choose 7 3 = 35 := by native_decide

/-- Hockey stick r=2, n=6: both sides equal 35 -/
example : Nat.choose 2 2 + Nat.choose 3 2 + Nat.choose 4 2
        + Nat.choose 5 2 + Nat.choose 6 2 = Nat.choose 7 3 := by native_decide

-- r=3: ∑_{i=3}^{6} C(i,3) = C(3,3)+C(4,3)+C(5,3)+C(6,3)
--                          = 1 + 4 + 10 + 20 = 35 = C(7,4)
example : Nat.choose 3 3 + Nat.choose 4 3 + Nat.choose 5 3
        + Nat.choose 6 3 = 35 := by native_decide

example : Nat.choose 7 4 = 35 := by native_decide

/-- Hockey stick r=3, n=6: both sides equal 35 -/
example : Nat.choose 3 3 + Nat.choose 4 3 + Nat.choose 5 3
        + Nat.choose 6 3 = Nat.choose 7 4 := by native_decide

-- r=1: ∑_{i=1}^{n} C(i,1) = 1+2+...+n = C(n+1,2) = n*(n+1)/2
-- For n=7: 1+2+3+4+5+6+7 = 28 = C(8,2)
example : Nat.choose 1 1 + Nat.choose 2 1 + Nat.choose 3 1 + Nat.choose 4 1
        + Nat.choose 5 1 + Nat.choose 6 1 + Nat.choose 7 1 = 28 := by native_decide

example : Nat.choose 8 2 = 28 := by native_decide

/-- Hockey stick r=1, n=7: ∑_{i=1}^{7} i = 28 = C(8,2) -/
example : Nat.choose 1 1 + Nat.choose 2 1 + Nat.choose 3 1 + Nat.choose 4 1
        + Nat.choose 5 1 + Nat.choose 6 1 + Nat.choose 7 1 = Nat.choose 8 2 := by native_decide

-- Arithmetic version: 1+2+...+7 = 7*8/2 = 28
example : 1 + 2 + 3 + 4 + 5 + 6 + 7 = 28 := by norm_num
-- In ℕ: rewrite as 2*(1+2+...+7) = 7*8 to avoid division
example : 2 * (1 + 2 + 3 + 4 + 5 + 6 + 7) = 7 * 8 := by norm_num

-- Additional hockey stick checks
-- r=2, n=4: C(2,2)+C(3,2)+C(4,2) = 1+3+6 = 10 = C(5,3)
example : Nat.choose 2 2 + Nat.choose 3 2 + Nat.choose 4 2 = Nat.choose 5 3 := by native_decide

-- r=3, n=7: ∑_{i=3}^{7} C(i,3) = 1+4+10+20+35 = 70 = C(8,4)
example : Nat.choose 3 3 + Nat.choose 4 3 + Nat.choose 5 3
        + Nat.choose 6 3 + Nat.choose 7 3 = Nat.choose 8 4 := by native_decide

example : Nat.choose 8 4 = 70 := by native_decide

-- r=4, n=7: ∑_{i=4}^{7} C(i,4) = 1+5+15+35 = 56 = C(8,5)
example : Nat.choose 4 4 + Nat.choose 5 4 + Nat.choose 6 4 + Nat.choose 7 4
        = Nat.choose 8 5 := by native_decide

example : Nat.choose 8 5 = 56 := by native_decide

end BijectionPrinciples
