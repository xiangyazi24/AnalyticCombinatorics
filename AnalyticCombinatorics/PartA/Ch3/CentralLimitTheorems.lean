import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-! # Ch III / IX — Central Limit Theorems in Combinatorics

Formalizes numerical verifications of moments, Poisson approximation,
Gaussian behavior of Eulerian numbers, cycle variance, and fixed-point
distributions. All checks use `native_decide` on rational or natural arithmetic.
-/

namespace CentralLimitTheorems

/-! ## 1. Binomial distribution moments: Bin(n, 1/2) -/

/-- Mean of Bin(n, 1/2). -/
def binomialMean (n : ℕ) : ℚ := n / 2

/-- Variance of Bin(n, 1/2). -/
def binomialVariance (n : ℕ) : ℚ := n / 4

/-- Second moment E[X^2] = n(n+1)/4 for Bin(n, 1/2). -/
def binomialSecondMoment (n : ℕ) : ℚ := n * (n + 1) / 4

example : binomialMean 10 = 5 := by native_decide

example : binomialVariance 10 = 5 / 2 := by native_decide

example : binomialSecondMoment 10 = 55 / 2 := by native_decide

example : (10 * 11 : ℚ) / 4 = 55 / 2 := by native_decide

/-! ## 2. Poisson approximation: partial sums of 1/k! -/

/-- Partial sum Σ_{k=0}^n 1/k! as a rational number. -/
def expPartialSum : ℕ → ℚ
  | 0 => 1
  | n + 1 => expPartialSum n + 1 / Nat.factorial (n + 1)

example : expPartialSum 5 = 163 / 60 := by native_decide

example : (1 : ℚ) + 1 + 1 / 2 + 1 / 6 + 1 / 24 + 1 / 120 = 163 / 60 := by native_decide

/-! ## 3. Normal approximation: central binomial coefficient -/

example : Nat.choose 20 10 = 184756 := by native_decide

example : 4 ^ 10 = (1048576 : ℕ) := by native_decide

/-- C(2n, n) for small n. -/
def centralBinomial (n : ℕ) : ℕ := Nat.choose (2 * n) n

example : centralBinomial 10 = 184756 := by native_decide

example : centralBinomial 5 = 252 := by native_decide

example : centralBinomial 3 = 20 := by native_decide

/-! ## 4. Gaussian-like behavior of Eulerian numbers -/

/-- Eulerian number E(n, k): permutations of {1..n} with exactly k descents.
    Uses the standard recurrence E(n,k) = (k+1)*E(n-1,k) + (n-k)*E(n-1,k-1). -/
def eulerianNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 =>
    (k + 2) * eulerianNumber n (k + 1) + (n - k) * eulerianNumber n k

/-- Table for n=4. -/
def eulerianTable4 : Fin 4 → ℕ := ![1, 11, 11, 1]

/-- Table for n=5. -/
def eulerianTable5 : Fin 5 → ℕ := ![1, 26, 66, 26, 1]

-- Verify Eulerian numbers for n=4
example : eulerianNumber 4 0 = 1 := by native_decide
example : eulerianNumber 4 1 = 11 := by native_decide
example : eulerianNumber 4 2 = 11 := by native_decide
example : eulerianNumber 4 3 = 1 := by native_decide

-- Sum = 4!
example : eulerianNumber 4 0 + eulerianNumber 4 1 + eulerianNumber 4 2 +
    eulerianNumber 4 3 = Nat.factorial 4 := by native_decide

-- Verify Eulerian numbers for n=5
example : eulerianNumber 5 0 = 1 := by native_decide
example : eulerianNumber 5 1 = 26 := by native_decide
example : eulerianNumber 5 2 = 66 := by native_decide
example : eulerianNumber 5 3 = 26 := by native_decide
example : eulerianNumber 5 4 = 1 := by native_decide

-- Sum = 5!
example : eulerianNumber 5 0 + eulerianNumber 5 1 + eulerianNumber 5 2 +
    eulerianNumber 5 3 + eulerianNumber 5 4 = Nat.factorial 5 := by native_decide

-- Symmetry: E(4, k) = E(4, 3-k)
example : eulerianNumber 4 0 = eulerianNumber 4 3 := by native_decide
example : eulerianNumber 4 1 = eulerianNumber 4 2 := by native_decide

-- Symmetry: E(5, k) = E(5, 4-k)
example : eulerianNumber 5 0 = eulerianNumber 5 4 := by native_decide
example : eulerianNumber 5 1 = eulerianNumber 5 3 := by native_decide

/-! ## 5. Variance of number of cycles in random permutation -/

/-- Harmonic number H_n = Σ_{k=1}^n 1/k. -/
def harmonicNumber : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonicNumber n + 1 / (n + 1)

/-- Generalized harmonic number H_n^{(2)} = Σ_{k=1}^n 1/k^2. -/
def harmonicNumberSq : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonicNumberSq n + 1 / ((n + 1) * (n + 1))

/-- Variance of cycle count in S_n: Var = H_n - H_n^{(2)}. -/
def cycleCountVariance (n : ℕ) : ℚ := harmonicNumber n - harmonicNumberSq n

-- H_4 = 1 + 1/2 + 1/3 + 1/4 = 25/12
example : harmonicNumber 4 = 25 / 12 := by native_decide

-- H_4^{(2)} = 1 + 1/4 + 1/9 + 1/16 = 205/144
example : harmonicNumberSq 4 = 205 / 144 := by native_decide

-- Var = 25/12 - 205/144 = 95/144
example : cycleCountVariance 4 = 95 / 144 := by native_decide

example : (25 : ℚ) / 12 - 205 / 144 = 95 / 144 := by native_decide

/-! ## 6. Distribution of fixed points -/

/-- Subfactorial (number of derangements). D(n) = n! * Σ_{k=0}^n (-1)^k/k!. -/
def subfactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (subfactorial (n + 1) + subfactorial n)

-- Verify subfactorial values
example : subfactorial 0 = 1 := by native_decide
example : subfactorial 1 = 0 := by native_decide
example : subfactorial 2 = 1 := by native_decide
example : subfactorial 3 = 2 := by native_decide
example : subfactorial 4 = 9 := by native_decide
example : subfactorial 5 = 44 := by native_decide

/-- Number of permutations of n with exactly k fixed points. -/
def fixedPointCount (n k : ℕ) : ℕ := Nat.choose n k * subfactorial (n - k)

-- For n=5: verify all counts
example : fixedPointCount 5 0 = 44 := by native_decide
example : fixedPointCount 5 1 = 45 := by native_decide
example : fixedPointCount 5 2 = 20 := by native_decide
example : fixedPointCount 5 3 = 10 := by native_decide
example : fixedPointCount 5 4 = 0 := by native_decide
example : fixedPointCount 5 5 = 1 := by native_decide

-- Sum of all fixed-point counts = 5!
example : fixedPointCount 5 0 + fixedPointCount 5 1 + fixedPointCount 5 2 +
    fixedPointCount 5 3 + fixedPointCount 5 4 + fixedPointCount 5 5 =
    Nat.factorial 5 := by native_decide

example : 44 + 45 + 20 + 10 + 0 + 1 = Nat.factorial 5 := by native_decide

end CentralLimitTheorems
