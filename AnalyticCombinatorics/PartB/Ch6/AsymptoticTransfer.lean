/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Asymptotic Transfer: Coefficient Verification

  This file verifies the concrete coefficient formulas arising from the
  Transfer Theorems (F&S §VI.2–VI.3). All proofs use native_decide.

  Content:
  1. Standard algebraic scale: [z^n](1-z)^{-α} = C(n+α-1, n)
  2. Catalan-type / central binomial recurrence
  3. Logarithmic transfer: partial sums (harmonic numbers)
  4. Polylogarithm / zeta partial sums
  5. Supercritical composition scheme
  6. O-transfer for algebraic functions: C(2n+2,n+1) < 4·C(2n,n)
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace AsymptoticTransfer

-- ============================================================
-- Section 1: Standard algebraic scale
-- ============================================================

/-! ## 1. Standard Scale: [z^n](1-z)^{-α} = C(n+α-1, n)

The Transfer Theorem (F&S §VI.2) gives the exact coefficient formula
for the standard algebraic scale function. For integer α ≥ 1:
  [z^n](1-z)^{-α} = C(n+α-1, n)
-/

/-- Transfer coefficient for (1-z)^{-α}: the n-th coefficient is C(n+α-1, n). -/
def transferCoeff (alpha n : ℕ) : ℕ := Nat.choose (n + alpha - 1) n

-- α = 1: geometric series, all coefficients = 1
-- C(n+0, n) = C(n, n) = 1
example : transferCoeff 1 0 = 1 := by native_decide
example : transferCoeff 1 1 = 1 := by native_decide
example : transferCoeff 1 2 = 1 := by native_decide
example : transferCoeff 1 3 = 1 := by native_decide
example : transferCoeff 1 4 = 1 := by native_decide
example : transferCoeff 1 5 = 1 := by native_decide
example : transferCoeff 1 6 = 1 := by native_decide
example : transferCoeff 1 7 = 1 := by native_decide
example : transferCoeff 1 8 = 1 := by native_decide
example : transferCoeff 1 9 = 1 := by native_decide
example : transferCoeff 1 10 = 1 := by native_decide

-- α = 2: [z^n](1-z)^{-2} = n+1
-- C(n+1, n) = n+1
example : transferCoeff 2 0 = 1 := by native_decide
example : transferCoeff 2 1 = 2 := by native_decide
example : transferCoeff 2 2 = 3 := by native_decide
example : transferCoeff 2 3 = 4 := by native_decide
example : transferCoeff 2 4 = 5 := by native_decide
example : transferCoeff 2 5 = 6 := by native_decide
example : transferCoeff 2 6 = 7 := by native_decide
example : transferCoeff 2 7 = 8 := by native_decide
example : transferCoeff 2 8 = 9 := by native_decide
example : transferCoeff 2 9 = 10 := by native_decide
example : transferCoeff 2 10 = 11 := by native_decide

-- α = 3: [z^n](1-z)^{-3} = C(n+2, 2) = (n+1)(n+2)/2
example : transferCoeff 3 0 = 1 := by native_decide
example : transferCoeff 3 1 = 3 := by native_decide
example : transferCoeff 3 2 = 6 := by native_decide
example : transferCoeff 3 3 = 10 := by native_decide
example : transferCoeff 3 4 = 15 := by native_decide
example : transferCoeff 3 5 = 21 := by native_decide
example : transferCoeff 3 6 = 28 := by native_decide
example : transferCoeff 3 7 = 36 := by native_decide
example : transferCoeff 3 8 = 45 := by native_decide
example : transferCoeff 3 9 = 55 := by native_decide
example : transferCoeff 3 10 = 66 := by native_decide

-- α = 3 matches Nat.choose (n+2) 2
example : transferCoeff 3 0 = Nat.choose 2 2 := by native_decide
example : transferCoeff 3 1 = Nat.choose 3 2 := by native_decide
example : transferCoeff 3 2 = Nat.choose 4 2 := by native_decide
example : transferCoeff 3 3 = Nat.choose 5 2 := by native_decide
example : transferCoeff 3 4 = Nat.choose 6 2 := by native_decide
example : transferCoeff 3 5 = Nat.choose 7 2 := by native_decide
example : transferCoeff 3 6 = Nat.choose 8 2 := by native_decide
example : transferCoeff 3 7 = Nat.choose 9 2 := by native_decide

-- α = 4: [z^n](1-z)^{-4} = C(n+3, 3)
example : transferCoeff 4 0 = 1 := by native_decide
example : transferCoeff 4 1 = 4 := by native_decide
example : transferCoeff 4 2 = 10 := by native_decide
example : transferCoeff 4 3 = 20 := by native_decide
example : transferCoeff 4 4 = 35 := by native_decide
example : transferCoeff 4 5 = 56 := by native_decide
example : transferCoeff 4 6 = 84 := by native_decide
example : transferCoeff 4 7 = 120 := by native_decide
example : transferCoeff 4 8 = 165 := by native_decide
example : transferCoeff 4 9 = 220 := by native_decide
example : transferCoeff 4 10 = 286 := by native_decide

-- α = 4 matches Nat.choose (n+3) 3
example : transferCoeff 4 0 = Nat.choose 3 3 := by native_decide
example : transferCoeff 4 1 = Nat.choose 4 3 := by native_decide
example : transferCoeff 4 2 = Nat.choose 5 3 := by native_decide
example : transferCoeff 4 3 = Nat.choose 6 3 := by native_decide
example : transferCoeff 4 4 = Nat.choose 7 3 := by native_decide
example : transferCoeff 4 5 = Nat.choose 8 3 := by native_decide
example : transferCoeff 4 6 = Nat.choose 9 3 := by native_decide

-- α = 5: [z^n](1-z)^{-5} = C(n+4, 4)
example : transferCoeff 5 0 = 1 := by native_decide
example : transferCoeff 5 1 = 5 := by native_decide
example : transferCoeff 5 2 = 15 := by native_decide
example : transferCoeff 5 3 = 35 := by native_decide
example : transferCoeff 5 4 = 70 := by native_decide
example : transferCoeff 5 5 = 126 := by native_decide
example : transferCoeff 5 6 = 210 := by native_decide
example : transferCoeff 5 7 = 330 := by native_decide
example : transferCoeff 5 8 = 495 := by native_decide
example : transferCoeff 5 9 = 715 := by native_decide
example : transferCoeff 5 10 = 1001 := by native_decide

-- α = 5 matches Nat.choose (n+4) 4
example : transferCoeff 5 0 = Nat.choose 4 4 := by native_decide
example : transferCoeff 5 1 = Nat.choose 5 4 := by native_decide
example : transferCoeff 5 2 = Nat.choose 6 4 := by native_decide
example : transferCoeff 5 3 = Nat.choose 7 4 := by native_decide
example : transferCoeff 5 4 = Nat.choose 8 4 := by native_decide
example : transferCoeff 5 5 = Nat.choose 9 4 := by native_decide
example : transferCoeff 5 6 = Nat.choose 10 4 := by native_decide

-- ============================================================
-- Section 2: Catalan-type transfer / Central binomial
-- ============================================================

/-! ## 2. Central Binomial Coefficients

The coefficient [z^n](1-4z)^{-1/2} is C(2n,n), the central binomial.
These satisfy the ratio recurrence C(2n+2,n+1) = 2(2n+1)/(n+1) · C(2n,n),
which in ℕ reads: C(2n+2,n+1)·(n+1) = C(2n,n)·2·(2n+1).
-/

/-- Central binomial coefficient: C(2n, n). -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

-- Values for n = 0..10
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
example : centralBinom 10 = 184756 := by native_decide

-- Ratio recurrence in ℕ: C(2(n+1), n+1) * (n+1) = C(2n, n) * 2 * (2n+1)
example : centralBinom 1 * 1 = centralBinom 0 * 2 * 1 := by native_decide
example : centralBinom 2 * 2 = centralBinom 1 * 2 * 3 := by native_decide
example : centralBinom 3 * 3 = centralBinom 2 * 2 * 5 := by native_decide
example : centralBinom 4 * 4 = centralBinom 3 * 2 * 7 := by native_decide
example : centralBinom 5 * 5 = centralBinom 4 * 2 * 9 := by native_decide
example : centralBinom 6 * 6 = centralBinom 5 * 2 * 11 := by native_decide
example : centralBinom 7 * 7 = centralBinom 6 * 2 * 13 := by native_decide
example : centralBinom 8 * 8 = centralBinom 7 * 2 * 15 := by native_decide
example : centralBinom 9 * 9 = centralBinom 8 * 2 * 17 := by native_decide

-- ============================================================
-- Section 3: Logarithmic transfer: harmonic numbers
-- ============================================================

/-! ## 3. Logarithmic Transfer: H_n = [z^n] ln(1/(1-z))

The coefficient [z^n] ln(1/(1-z)) = 1/n for n ≥ 1.
The partial sums H_n = Σ_{k=1}^n 1/k are the harmonic numbers.
-/

/-- Harmonic number H_n = Σ_{k=1}^n 1/k, as a rational. -/
def harmonicRat (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

-- Small values
example : harmonicRat 0 = 0 := by native_decide
example : harmonicRat 1 = 1 := by native_decide
example : harmonicRat 2 = 3 / 2 := by native_decide
example : harmonicRat 3 = 11 / 6 := by native_decide
example : harmonicRat 4 = 25 / 12 := by native_decide
example : harmonicRat 5 = 137 / 60 := by native_decide
example : harmonicRat 6 = 49 / 20 := by native_decide
example : harmonicRat 7 = 363 / 140 := by native_decide
example : harmonicRat 8 = 761 / 280 := by native_decide

-- Multiplier verifications matching the transfer theorem
-- 12 * H_4 = 25
example : 12 * harmonicRat 4 = 25 := by native_decide
-- 20 * H_6 = 49
example : 20 * harmonicRat 6 = 49 := by native_decide
-- 280 * H_8 = 761
example : 280 * harmonicRat 8 = 761 := by native_decide

-- Incremental check: H_{n+1} = H_n + 1/(n+1)
example : harmonicRat 5 = harmonicRat 4 + 1 / 5 := by native_decide
example : harmonicRat 6 = harmonicRat 5 + 1 / 6 := by native_decide
example : harmonicRat 7 = harmonicRat 6 + 1 / 7 := by native_decide
example : harmonicRat 8 = harmonicRat 7 + 1 / 8 := by native_decide

-- ============================================================
-- Section 4: Polylogarithm / zeta partial sums
-- ============================================================

/-! ## 4. Polylogarithm: [z^n] Li_s(z) = 1/n^s

Li_s(z) = Σ_{n≥1} z^n / n^s.
The partial sums ζ(s, N) = Σ_{k=1}^N 1/k^s approximate the Riemann zeta value.
-/

/-- Partial sum ζ(s, N) = Σ_{k=1}^N 1/k^s, as a rational. -/
def zetaPartial (s n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ) ^ s

-- zetaPartial 1 n = harmonicRat n
example : zetaPartial 1 1 = 1 := by native_decide
example : zetaPartial 1 2 = 3 / 2 := by native_decide
example : zetaPartial 1 4 = 25 / 12 := by native_decide

-- Li_2: ζ(2, N) = Σ 1/k^2
-- ζ(2,1) = 1
example : zetaPartial 2 1 = 1 := by native_decide
-- ζ(2,2) = 1 + 1/4 = 5/4
example : zetaPartial 2 2 = 5 / 4 := by native_decide
-- ζ(2,3) = 1 + 1/4 + 1/9 = 49/36
example : zetaPartial 2 3 = 49 / 36 := by native_decide
-- ζ(2,4) = 1 + 1/4 + 1/9 + 1/16 = 205/144
example : zetaPartial 2 4 = 205 / 144 := by native_decide
-- ζ(2,5) = 205/144 + 1/25 = 5269/3600
example : zetaPartial 2 5 = 5269 / 3600 := by native_decide

-- Li_3: ζ(3, N) = Σ 1/k^3
-- ζ(3,1) = 1
example : zetaPartial 3 1 = 1 := by native_decide
-- ζ(3,2) = 1 + 1/8 = 9/8
example : zetaPartial 3 2 = 9 / 8 := by native_decide
-- ζ(3,3) = 1 + 1/8 + 1/27 = 251/216
example : zetaPartial 3 3 = 251 / 216 := by native_decide
-- ζ(3,4) = 251/216 + 1/64
example : zetaPartial 3 4 = 2035 / 1728 := by native_decide

-- Li_4: ζ(4, N)
example : zetaPartial 4 1 = 1 := by native_decide
example : zetaPartial 4 2 = 17 / 16 := by native_decide
example : zetaPartial 4 3 = 1393 / 1296 := by native_decide

-- Incremental check: zetaPartial s (n+1) = zetaPartial s n + 1/(n+1)^s
example : zetaPartial 2 4 = zetaPartial 2 3 + 1 / (4 : ℚ) ^ 2 := by native_decide
example : zetaPartial 3 4 = zetaPartial 3 3 + 1 / (4 : ℚ) ^ 3 := by native_decide
example : zetaPartial 2 5 = zetaPartial 2 4 + 1 / (5 : ℚ) ^ 2 := by native_decide

-- ============================================================
-- Section 5: Supercritical composition scheme
-- ============================================================

/-! ## 5. Supercritical Composition Scheme

If f(z) = 1/(1-z)^2 (so [z^k]f = k+1) and g(z) = f(z)/(1-z) = 1/(1-z)^3,
then [z^n]g = Σ_{k=0}^n [z^k]f = Σ_{k=0}^n (k+1) = (n+1)(n+2)/2 = C(n+2,2).

This is the "convolution with 1/(1-z) = summing coefficients" schema.
-/

-- Σ_{k=0}^4 (k+1) = 1+2+3+4+5 = 15 = C(6,2)
example : ∑ k ∈ Finset.range 5, (k + 1) = Nat.choose 6 2 := by native_decide

-- Σ_{k=0}^7 (k+1) = 1+2+...+8 = 36 = C(9,2)
example : ∑ k ∈ Finset.range 8, (k + 1) = Nat.choose 9 2 := by native_decide

-- Σ_{k=0}^9 (k+1) = 1+2+...+10 = 55 = C(11,2)
example : ∑ k ∈ Finset.range 10, (k + 1) = Nat.choose 11 2 := by native_decide

-- More checks: n=2..6
example : ∑ k ∈ Finset.range 3, (k + 1) = Nat.choose 4 2 := by native_decide
example : ∑ k ∈ Finset.range 4, (k + 1) = Nat.choose 5 2 := by native_decide
example : ∑ k ∈ Finset.range 6, (k + 1) = Nat.choose 7 2 := by native_decide
example : ∑ k ∈ Finset.range 7, (k + 1) = Nat.choose 8 2 := by native_decide
example : ∑ k ∈ Finset.range 9, (k + 1) = Nat.choose 10 2 := by native_decide

-- Agreement with transferCoeff 3 n:
-- transferCoeff 3 n = C(n+2, n) = C(n+2, 2) = (n+1)(n+2)/2
example : ∑ k ∈ Finset.range 5, (k + 1) = transferCoeff 3 4 := by native_decide
example : ∑ k ∈ Finset.range 8, (k + 1) = transferCoeff 3 7 := by native_decide
example : ∑ k ∈ Finset.range 10, (k + 1) = transferCoeff 3 9 := by native_decide

-- Iterated: Σ_{k=0}^n (k+1)(k+2)/2 = C(n+3,3) = transferCoeff 4 n
-- (summing [z^k](1-z)^{-3} gives [z^n](1-z)^{-4})
example : ∑ k ∈ Finset.range 4, Nat.choose (k + 2) 2 = transferCoeff 4 3 := by native_decide
example : ∑ k ∈ Finset.range 5, Nat.choose (k + 2) 2 = transferCoeff 4 4 := by native_decide
example : ∑ k ∈ Finset.range 6, Nat.choose (k + 2) 2 = transferCoeff 4 5 := by native_decide

-- ============================================================
-- Section 6: O-transfer for algebraic functions
-- ============================================================

/-! ## 6. O-Transfer: [z^n](1-z)^{-1/2} ~ C(2n,n)/4^n

The coefficient of z^n in (1-z)^{-1/2} is exactly C(2n,n)/4^n.
As n → ∞ this converges to 1/√(πn).

Key monotonicity: C(2n+2,n+1) < 4·C(2n,n) for all n ≥ 0.
This shows the ratio C(2n,n)/4^n is strictly decreasing.
-/

-- C(2n+2,n+1) < 4·C(2n,n) for n = 0..10
example : Nat.choose 2 1 < 4 * Nat.choose 0 0 := by native_decide
example : Nat.choose 4 2 < 4 * Nat.choose 2 1 := by native_decide
example : Nat.choose 6 3 < 4 * Nat.choose 4 2 := by native_decide
example : Nat.choose 8 4 < 4 * Nat.choose 6 3 := by native_decide
example : Nat.choose 10 5 < 4 * Nat.choose 8 4 := by native_decide
example : Nat.choose 12 6 < 4 * Nat.choose 10 5 := by native_decide
example : Nat.choose 14 7 < 4 * Nat.choose 12 6 := by native_decide
example : Nat.choose 16 8 < 4 * Nat.choose 14 7 := by native_decide
example : Nat.choose 18 9 < 4 * Nat.choose 16 8 := by native_decide
example : Nat.choose 20 10 < 4 * Nat.choose 18 9 := by native_decide
example : Nat.choose 22 11 < 4 * Nat.choose 20 10 := by native_decide

-- In terms of centralBinom: centralBinom (n+1) < 4 * centralBinom n
example : centralBinom 1 < 4 * centralBinom 0 := by native_decide
example : centralBinom 2 < 4 * centralBinom 1 := by native_decide
example : centralBinom 3 < 4 * centralBinom 2 := by native_decide
example : centralBinom 4 < 4 * centralBinom 3 := by native_decide
example : centralBinom 5 < 4 * centralBinom 4 := by native_decide
example : centralBinom 6 < 4 * centralBinom 5 := by native_decide
example : centralBinom 7 < 4 * centralBinom 6 := by native_decide
example : centralBinom 8 < 4 * centralBinom 7 := by native_decide
example : centralBinom 9 < 4 * centralBinom 8 := by native_decide
example : centralBinom 10 < 4 * centralBinom 9 := by native_decide

-- Explicit values of 4^n and C(2n,n) for small n:
-- n=1: C(2,1)=2 < 4^1=4
example : centralBinom 1 < 4 ^ 1 := by native_decide
-- n=2: C(4,2)=6 < 4^2=16
example : centralBinom 2 < 4 ^ 2 := by native_decide
-- n=3: C(6,3)=20 < 4^3=64
example : centralBinom 3 < 4 ^ 3 := by native_decide
-- n=4: C(8,4)=70 < 4^4=256
example : centralBinom 4 < 4 ^ 4 := by native_decide
-- n=5: C(10,5)=252 < 4^5=1024
example : centralBinom 5 < 4 ^ 5 := by native_decide
-- n=6: C(12,6)=924 < 4^6=4096
example : centralBinom 6 < 4 ^ 6 := by native_decide
-- n=7: C(14,7)=3432 < 4^7=16384
example : centralBinom 7 < 4 ^ 7 := by native_decide
-- n=8: C(16,8)=12870 < 4^8=65536
example : centralBinom 8 < 4 ^ 8 := by native_decide

end AsymptoticTransfer
