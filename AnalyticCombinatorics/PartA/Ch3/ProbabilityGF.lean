import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-! # Ch III — Probability Generating Functions: basic distributions

This file formalizes elementary probability distribution computations
from Flajolet & Sedgewick Chapter III:
- Binomial distribution moments (p = 1/2)
- Poisson partial sums (λ = 1)
- Geometric partial sums
- Falling factorials
- Binomial second moment / variance
-/

namespace ProbabilityGF

/-! ## 1. Binomial distribution mean numerator -/

/-- Sum of k * C(n,k) for k = 0..n. For Binomial(n,1/2), dividing by 2^n gives the mean. -/
def binomialMeanNumer (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), k * Nat.choose n k

/-- Verify: binomialMeanNumer n = n * 2^(n-1) for n = 1..8. -/
example : binomialMeanNumer 1 = 1 * 2 ^ 0 := by native_decide
example : binomialMeanNumer 2 = 2 * 2 ^ 1 := by native_decide
example : binomialMeanNumer 3 = 3 * 2 ^ 2 := by native_decide
example : binomialMeanNumer 4 = 4 * 2 ^ 3 := by native_decide
example : binomialMeanNumer 5 = 5 * 2 ^ 4 := by native_decide
example : binomialMeanNumer 6 = 6 * 2 ^ 5 := by native_decide
example : binomialMeanNumer 7 = 7 * 2 ^ 6 := by native_decide
example : binomialMeanNumer 8 = 8 * 2 ^ 7 := by native_decide

/-! ## 2. Poisson partial sums (λ = 1) -/

/-- Partial sum of e^1 = Σ_{k=0}^{trunc-1} 1/k! as a rational number. -/
def poissonPartialSum (trunc : ℕ) : ℚ :=
  ∑ k ∈ Finset.range trunc, 1 / (Nat.factorial k : ℚ)

/-- Verify: poissonPartialSum 5 = 65/24 (= 1 + 1 + 1/2 + 1/6 + 1/24). -/
example : poissonPartialSum 5 = 65 / 24 := by native_decide

/-- Verify: poissonPartialSum 8 < 3. -/
example : poissonPartialSum 8 < 3 := by native_decide

/-! ## 3. Geometric partial sums -/

/-- Σ_{k=0}^{n-1} (1/2)^{k+1} = Σ_{k=1}^n (1/2)^k. -/
def geomPartialSum (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / (2 : ℚ) ^ (k + 1)

example : geomPartialSum 1 = 1 / 2 := by native_decide
example : geomPartialSum 2 = 3 / 4 := by native_decide
example : geomPartialSum 3 = 7 / 8 := by native_decide

/-- Verify: geomPartialSum n = 1 - 1/2^n for n = 1..8. -/
example : geomPartialSum 1 = 1 - 1 / (2 : ℚ) ^ 1 := by native_decide
example : geomPartialSum 2 = 1 - 1 / (2 : ℚ) ^ 2 := by native_decide
example : geomPartialSum 3 = 1 - 1 / (2 : ℚ) ^ 3 := by native_decide
example : geomPartialSum 4 = 1 - 1 / (2 : ℚ) ^ 4 := by native_decide
example : geomPartialSum 5 = 1 - 1 / (2 : ℚ) ^ 5 := by native_decide
example : geomPartialSum 6 = 1 - 1 / (2 : ℚ) ^ 6 := by native_decide
example : geomPartialSum 7 = 1 - 1 / (2 : ℚ) ^ 7 := by native_decide
example : geomPartialSum 8 = 1 - 1 / (2 : ℚ) ^ 8 := by native_decide

/-! ## 4. Falling factorial -/

/-- Falling factorial: n * (n-1) * ... * (n-k+1), i.e. n!/(n-k)! for k ≤ n. -/
def fallingFactorial (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (n - i)

example : fallingFactorial 5 0 = 1 := by native_decide
example : fallingFactorial 5 1 = 5 := by native_decide
example : fallingFactorial 5 2 = 20 := by native_decide
example : fallingFactorial 5 3 = 60 := by native_decide
example : fallingFactorial 5 5 = 120 := by native_decide
example : fallingFactorial 5 5 = Nat.factorial 5 := by native_decide

/-- Verify: fallingFactorial n n = n! for n = 0..6. -/
example : fallingFactorial 0 0 = Nat.factorial 0 := by native_decide
example : fallingFactorial 1 1 = Nat.factorial 1 := by native_decide
example : fallingFactorial 2 2 = Nat.factorial 2 := by native_decide
example : fallingFactorial 3 3 = Nat.factorial 3 := by native_decide
example : fallingFactorial 4 4 = Nat.factorial 4 := by native_decide
example : fallingFactorial 5 5 = Nat.factorial 5 := by native_decide
example : fallingFactorial 6 6 = Nat.factorial 6 := by native_decide

/-! ## 5. Binomial second moment and variance -/

/-- Sum of k^2 * C(n,k) for k = 0..n. Numerator of E[X^2] for Binomial(n,1/2). -/
def binomialSecondMomentNumer (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), k ^ 2 * Nat.choose n k

/-- Verify: Σ_k k^2 * C(n,k) = n*(n+1)*2^{n-2} for n = 2..8. -/
example : binomialSecondMomentNumer 2 = 2 * 3 * 2 ^ 0 := by native_decide
example : binomialSecondMomentNumer 3 = 3 * 4 * 2 ^ 1 := by native_decide
example : binomialSecondMomentNumer 4 = 4 * 5 * 2 ^ 2 := by native_decide
example : binomialSecondMomentNumer 5 = 5 * 6 * 2 ^ 3 := by native_decide
example : binomialSecondMomentNumer 6 = 6 * 7 * 2 ^ 4 := by native_decide
example : binomialSecondMomentNumer 7 = 7 * 8 * 2 ^ 5 := by native_decide
example : binomialSecondMomentNumer 8 = 8 * 9 * 2 ^ 6 := by native_decide

end ProbabilityGF
