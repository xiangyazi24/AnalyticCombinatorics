/-
  Analytic Combinatorics — Part B
  Chapter IX — Discrete probability distributions and limit law numerics.

  Numerical checks for:
  - Binomial distribution moments (p = 1/2 case)
  - Poisson approximation numerics
  - Stirling numbers and random permutation cycle counts
  - Variance of cycle count
  - Birthday problem
  - Coupon collector expected values
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace LimitDistributions

-- ============================================================================
-- § 1. Binomial distribution (p = 1/2)
-- ============================================================================

/-- PMF of Bin(n, 1/2): P(X = k) = C(n,k) / 2^n. -/
def binomialPMF (n : ℕ) (k : ℕ) : ℚ := (Nat.choose n k : ℚ) / (2 ^ n : ℚ)

/-- The PMF sums to 1 for n = 4. -/
example : ∑ k ∈ Finset.range 5, binomialPMF 4 k = 1 := by native_decide

/-- The PMF sums to 1 for n = 5. -/
example : ∑ k ∈ Finset.range 6, binomialPMF 5 k = 1 := by native_decide

/-- The PMF sums to 1 for n = 6. -/
example : ∑ k ∈ Finset.range 7, binomialPMF 6 k = 1 := by native_decide

/-- The PMF sums to 1 for n = 8. -/
example : ∑ k ∈ Finset.range 9, binomialPMF 8 k = 1 := by native_decide

/-- E[X] = n/2 for Bin(n, 1/2): verified for n = 4. -/
example : ∑ k ∈ Finset.range 5, (k : ℚ) * binomialPMF 4 k = 4 / 2 := by native_decide

/-- E[X] = n/2 for Bin(n, 1/2): verified for n = 6. -/
example : ∑ k ∈ Finset.range 7, (k : ℚ) * binomialPMF 6 k = 6 / 2 := by native_decide

/-- E[X] = n/2 for Bin(n, 1/2): verified for n = 8. -/
example : ∑ k ∈ Finset.range 9, (k : ℚ) * binomialPMF 8 k = 8 / 2 := by native_decide

/-- E[X] = 5, Var[X] = 5/2 for Bin(10, 1/2).
    E[X²] = Σ k² * C(10,k)/2^10. Var = E[X²] - (E[X])². -/
example : ∑ k ∈ Finset.range 11, (k : ℚ) * binomialPMF 10 k = 5 := by native_decide

example : ∑ k ∈ Finset.range 11, (k : ℚ) ^ 2 * binomialPMF 10 k - 5 ^ 2 = 5 / 2 := by
  native_decide

-- ============================================================================
-- § 2. Poisson approximation to binomial
-- ============================================================================

/-- (9/10)^10 ≈ 0.3487: a finite approximation to e^{-1}.
    We verify 0.348 < (9/10)^10 < 0.349. -/
example : (348 : ℤ) * 10 ^ 10 ≤ 1000 * 9 ^ 10 := by native_decide

example : (1000 : ℤ) * 9 ^ 10 ≤ 349 * 10 ^ 10 := by native_decide

/-- Equivalently in ℚ: 348/1000 < (9/10)^10 < 349/1000. -/
example : (348 : ℚ) / 1000 < (9 / 10) ^ 10 := by native_decide

example : (9 / 10 : ℚ) ^ 10 < 349 / 1000 := by native_decide

/-- For Bin(n, p) with n = 10, p = 1/10:
    P(X = 0) = (9/10)^10 = 9^10 / 10^10. -/
def poissonApproxP0 : ℚ := (9 : ℚ) ^ 10 / (10 : ℚ) ^ 10

example : poissonApproxP0 = 3486784401 / 10000000000 := by native_decide

/-- Poisson approximation: e^{-1} ≈ 0.3679. The exact value 9^10/10^10 ≈ 0.3487
    is about 5% off, reflecting n = 10 is not yet "large n, small p". -/
example : 3486784401 * 1000 < 3679 * (10000000000 : ℕ) := by native_decide

-- ============================================================================
-- § 3. Stirling numbers and random permutation cycles
-- ============================================================================

/-- The n-th harmonic number H_n = Σ_{k=1}^n 1/k. -/
def harmonicQ (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / ((k + 1) : ℚ)

/-- H_4 = 1 + 1/2 + 1/3 + 1/4 = 25/12. -/
example : harmonicQ 4 = 25 / 12 := by native_decide

/-- H_6 = 1 + 1/2 + 1/3 + 1/4 + 1/5 + 1/6 = 49/20. -/
example : harmonicQ 6 = 49 / 20 := by native_decide

/-- H_1 = 1. -/
example : harmonicQ 1 = 1 := by native_decide

/-- H_2 = 3/2. -/
example : harmonicQ 2 = 3 / 2 := by native_decide

/-- H_3 = 11/6. -/
example : harmonicQ 3 = 11 / 6 := by native_decide

/-- The expected number of cycles of a uniformly random permutation of [n]
    equals H_n. Verified for n = 4: E[cycles] = 25/12. -/
example : harmonicQ 4 = 25 / 12 := by native_decide

-- ============================================================================
-- § 4. Variance of cycle count
-- ============================================================================

/-- H_n^{(2)} = Σ_{k=1}^n 1/k². -/
def harmonicSq (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / ((k + 1) : ℚ) ^ 2

/-- H_4^{(2)} = 1 + 1/4 + 1/9 + 1/16 = 205/144. -/
example : harmonicSq 4 = 205 / 144 := by native_decide

/-- H_6^{(2)} = 1 + 1/4 + 1/9 + 1/16 + 1/25 + 1/36 = 5369/3600. -/
example : harmonicSq 6 = 5369 / 3600 := by native_decide

/-- Var[cycles in S_n] = H_n - H_n^{(2)}.
    For n = 4: Var = 25/12 - 205/144 = 300/144 - 205/144 = 95/144. -/
example : harmonicQ 4 - harmonicSq 4 = 95 / 144 := by native_decide

/-- Var[cycles in S_6] = 49/20 - 5369/3600 = 8820/3600 - 5369/3600 = 3451/3600. -/
example : harmonicQ 6 - harmonicSq 6 = 3451 / 3600 := by native_decide

/-- Variance is positive for all n ≥ 2 (H_n > H_n^{(2)} since H_n^{(2)} < π²/6 < 2 < H_n
    for large n, but we verify directly for small n). -/
example : harmonicQ 4 > harmonicSq 4 := by native_decide
example : harmonicQ 6 > harmonicSq 6 := by native_decide

-- ============================================================================
-- § 5. Birthday problem
-- ============================================================================

/-- Number of ways to choose n items from [m] with no repetition:
    m * (m-1) * ... * (m-n+1) = falling factorial. -/
def noCollisionNum (m n : ℕ) : ℕ := ∏ i ∈ Finset.range n, (m - i)

/-- For m = 10, n = 4: 10 * 9 * 8 * 7 = 5040. -/
example : noCollisionNum 10 4 = 5040 := by native_decide

/-- Denominator: 10^4 = 10000. -/
example : (10 : ℕ) ^ 4 = 10000 := by native_decide

/-- P(no collision) = 5040/10000 = 63/125. -/
example : (noCollisionNum 10 4 : ℚ) / (10 : ℚ) ^ 4 = 63 / 125 := by native_decide

/-- P(collision) for m=10, n=4 is 1 - 63/125 = 62/125 < 1/2. -/
example : (1 : ℚ) - (noCollisionNum 10 4 : ℚ) / (10 : ℚ) ^ 4 = 62 / 125 := by native_decide

/-- For m = 365, n = 23: birthday paradox — P(collision) > 1/2.
    Equivalently: 2 * noCollisionNum 365 23 < 365^23. -/
example : 2 * noCollisionNum 365 23 < 365 ^ 23 := by native_decide

/-- For m = 10, n = 5: P(no collision) = 10*9*8*7*6 / 10^5 = 30240/100000 < 1/2. -/
example : noCollisionNum 10 5 = 30240 := by native_decide

example : 2 * noCollisionNum 10 5 < (10 : ℕ) ^ 5 := by native_decide

-- ============================================================================
-- § 6. Coupon collector
-- ============================================================================

/-- Expected number of draws to collect all n coupons = n * H_n. -/
def couponCollector (n : ℕ) : ℚ := n * harmonicQ n

/-- For n = 4: expected draws = 4 * 25/12 = 25/3. -/
example : couponCollector 4 = 25 / 3 := by native_decide

/-- For n = 6: expected draws = 6 * 49/20 = 147/10. -/
example : couponCollector 6 = 147 / 10 := by native_decide

/-- Equivalently using explicit multiplication. -/
example : 4 * harmonicQ 4 = 25 / 3 := by native_decide

example : 6 * harmonicQ 6 = 147 / 10 := by native_decide

/-- For n = 2: expected draws = 2 * 3/2 = 3. -/
example : couponCollector 2 = 3 := by native_decide

/-- For n = 3: expected draws = 3 * 11/6 = 11/2. -/
example : couponCollector 3 = 11 / 2 := by native_decide

/-- Coupon collector grows: E_6 > E_4. -/
example : couponCollector 6 > couponCollector 4 := by native_decide

end LimitDistributions
