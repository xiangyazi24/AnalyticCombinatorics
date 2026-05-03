import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace LargeDeviations

open Finset

/-!
  Chapter VIII saddle-point support numerics: large-deviation kernels used
  to bound tails around saddle points.  The checks are deliberately finite
  and decidable.  Exponential Chernoff factors are encoded with an integer
  base `b`, read as `b = exp s`; inequalities are cross-multiplied to avoid
  real-valued division.
-/

/-! ## 1. Chernoff kernels and moment identities -/

/-- Total scaled mass on the finite support `{0, ..., N}`. -/
def finiteTotalWeight (N : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (N + 1), w x

/-- Scaled tail mass for the event `X >= t`. -/
def finiteTailWeight (N t : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (N + 1), if t ≤ x then w x else 0

/-- Scaled first moment. -/
def finiteMeanWeight (N : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (N + 1), w x * x

/-- Scaled exponential moment with integer base `b = exp s`. -/
def finiteExpMomentWeight (N b : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (N + 1), w x * b ^ x

/--
Cross-multiplied Chernoff form
`P(X >= t) <= E[b^X] / b^t`, with `b = exp s`.
-/
def chernoffKernel (N t b : ℕ) (w : ℕ → ℕ) : Prop :=
  finiteTailWeight N t w * b ^ t ≤ finiteExpMomentWeight N b w

/-- A two-point distribution: mass `1` at `0` and mass `1` at `3`. -/
def twoPointMass : ℕ → ℕ
  | 0 => 1
  | 3 => 1
  | _ => 0

/-- A three-point distribution with total mass `4`. -/
def threePointMass : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 4 => 1
  | _ => 0

theorem twoPoint_moment_identities :
    finiteTotalWeight 3 twoPointMass = 2 ∧
      finiteMeanWeight 3 twoPointMass = 3 ∧
      finiteExpMomentWeight 3 2 twoPointMass = 9 ∧
      finiteExpMomentWeight 3 3 twoPointMass = 28 := by
  native_decide

theorem threePoint_moment_identities :
    finiteTotalWeight 4 threePointMass = 4 ∧
      finiteMeanWeight 4 threePointMass = 6 ∧
      finiteExpMomentWeight 4 2 threePointMass = 21 ∧
      finiteExpMomentWeight 4 3 threePointMass = 88 := by
  native_decide

theorem chernoff_bound_structure_samples :
    finiteTailWeight 3 3 twoPointMass * 2 ^ 3 ≤
        finiteExpMomentWeight 3 2 twoPointMass ∧
      finiteTailWeight 3 3 twoPointMass * 3 ^ 3 ≤
        finiteExpMomentWeight 3 3 twoPointMass ∧
      finiteTailWeight 4 4 threePointMass * 2 ^ 4 ≤
        finiteExpMomentWeight 4 2 threePointMass ∧
      finiteTailWeight 4 2 threePointMass * 3 ^ 2 ≤
        finiteExpMomentWeight 4 3 threePointMass := by
  native_decide

/-! ## 2. Binomial tail bounds -/

/-- Scaled tail count for `Bin(n, 1/2)`: denominator is `2^n`. -/
def binomialHalfTail (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), if k ≤ j then Nat.choose n j else 0

/-- Scaled exponential moment for `Bin(n, 1/2)`: `sum C(n,j)b^j`. -/
def binomialHalfExpMomentWeight (n b : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), Nat.choose n j * b ^ j

/--
Chernoff kernel for `Bin(n, 1/2)`:
`P(X >= k) <= ((1+b)/2)^n / b^k`.
-/
def binomialChernoffKernel (n k b : ℕ) : Prop :=
  binomialHalfTail n k * b ^ k ≤ binomialHalfExpMomentWeight n b

theorem binomial_tail_values :
    binomialHalfTail 10 8 = 56 ∧
      binomialHalfTail 12 9 = 299 ∧
      binomialHalfTail 16 12 = 2517 := by
  native_decide

theorem binomial_tail_probability_bounds :
    16 * binomialHalfTail 10 8 ≤ 2 ^ 10 ∧
      8 * binomialHalfTail 12 9 ≤ 2 ^ 12 ∧
      16 * binomialHalfTail 16 12 ≤ 2 ^ 16 := by
  native_decide

theorem binomial_exp_moment_identities_base2 :
    binomialHalfExpMomentWeight 10 2 = 3 ^ 10 ∧
      binomialHalfExpMomentWeight 12 2 = 3 ^ 12 ∧
      binomialHalfExpMomentWeight 16 2 = 3 ^ 16 := by
  native_decide

theorem binomial_chernoff_base2_samples :
    binomialHalfTail 10 8 * 2 ^ 8 ≤ binomialHalfExpMomentWeight 10 2 ∧
      binomialHalfTail 12 9 * 2 ^ 9 ≤ binomialHalfExpMomentWeight 12 2 ∧
      binomialHalfTail 16 12 * 2 ^ 12 ≤ binomialHalfExpMomentWeight 16 2 := by
  native_decide

/-! ## 3. Poisson CDF numerical verifications -/

/--
For integer `lambda`, this is
`k! * sum_{j=0}^k lambda^j / j!`, the polynomial part of the Poisson CDF
`exp(-lambda) * sum_{j=0}^k lambda^j / j!`.
-/
def poissonCdfSeriesScaled (lambda k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), lambda ^ j * Nat.factorial k / Nat.factorial j

def expNeg1Lower100000 : ℕ := 36787
def expNeg1Upper100000 : ℕ := 36788
def expNeg2Lower100000 : ℕ := 13533
def expNeg2Upper100000 : ℕ := 13534

theorem poisson_cdf_series_values :
    poissonCdfSeriesScaled 1 3 = 16 ∧
      poissonCdfSeriesScaled 1 5 = 326 ∧
      poissonCdfSeriesScaled 2 4 = 168 ∧
      poissonCdfSeriesScaled 3 3 = 78 := by
  native_decide

/-- `P(Poisson(1) <= 2)` lies in `[0.91967, 0.91970]`. -/
theorem poisson_one_cdf_le_two_decimal_window :
    Nat.factorial 2 * 91967 ≤
        poissonCdfSeriesScaled 1 2 * expNeg1Lower100000 ∧
      poissonCdfSeriesScaled 1 2 * expNeg1Upper100000 ≤
        Nat.factorial 2 * 91970 := by
  native_decide

/-- `P(Poisson(2) <= 4)` lies in `[0.94731, 0.94738]`. -/
theorem poisson_two_cdf_le_four_decimal_window :
    Nat.factorial 4 * 94731 ≤
        poissonCdfSeriesScaled 2 4 * expNeg2Lower100000 ∧
      poissonCdfSeriesScaled 2 4 * expNeg2Upper100000 ≤
        Nat.factorial 4 * 94738 := by
  native_decide

/-! ## 4. Hoeffding-type concentration checks -/

def expNegTwoUpper100000 : ℕ := 13534
def expNegThreeUpper100000 : ℕ := 4979
def expNegFourUpper100000 : ℕ := 1832
def expNegFourThirdsUpper100000 : ℕ := 26360

theorem hoeffding_binomial_tail_values :
    binomialHalfTail 4 4 = 1 ∧
      binomialHalfTail 6 6 = 1 ∧
      binomialHalfTail 6 5 = 7 ∧
      binomialHalfTail 8 8 = 1 := by
  native_decide

/--
Small Hoeffding checks for sums of independent `{0,1}` variables.
The right sides are decimal upper brackets for the corresponding
`exp(-2 r^2 / n)` terms.
-/
theorem hoeffding_small_cases :
    100000 * binomialHalfTail 4 4 ≤ 2 ^ 4 * expNegTwoUpper100000 ∧
      100000 * binomialHalfTail 6 6 ≤ 2 ^ 6 * expNegThreeUpper100000 ∧
      100000 * binomialHalfTail 6 5 ≤ 2 ^ 6 * expNegFourThirdsUpper100000 ∧
      100000 * binomialHalfTail 8 8 ≤ 2 ^ 8 * expNegFourUpper100000 := by
  native_decide

/-! ## 5. Markov inequality examples -/

def dieMass : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

/-- Markov kernel `P(X >= t) <= E[X] / t`, cross-multiplied. -/
def markovKernel (N t : ℕ) (w : ℕ → ℕ) : Prop :=
  finiteTailWeight N t w * t ≤ finiteMeanWeight N w

theorem markov_die_examples :
    finiteTotalWeight 6 dieMass = 6 ∧
      finiteMeanWeight 6 dieMass = 21 ∧
      finiteTailWeight 6 5 dieMass * 5 ≤ finiteMeanWeight 6 dieMass ∧
      finiteTailWeight 6 6 dieMass * 6 ≤ finiteMeanWeight 6 dieMass := by
  native_decide

def binomialHalfMass (n : ℕ) : ℕ → ℕ :=
  fun k => if k ≤ n then Nat.choose n k else 0

theorem markov_binomial_examples :
    finiteTotalWeight 4 (binomialHalfMass 4) = 2 ^ 4 ∧
      finiteMeanWeight 4 (binomialHalfMass 4) = 4 * 2 ^ 3 ∧
      finiteTailWeight 4 3 (binomialHalfMass 4) = 5 ∧
      finiteTailWeight 4 3 (binomialHalfMass 4) * 3 ≤
        finiteMeanWeight 4 (binomialHalfMass 4) := by
  native_decide

/-! ## 6. Exact exponential moments -/

/--
Closed form for a geometric distribution on `0,1,2,...` with ratio `q`:
`P(X=k) = (1-q)q^k`, so `E[y^X] = (1-q)/(1-qy)`.
-/
def geometricExpMoment (q y : ℚ) : ℚ :=
  (1 - q) / (1 - q * y)

/-- Exact binomial moment: `E[y^X] = (1 - p + p*y)^n`. -/
def binomialExpMoment (n : ℕ) (p y : ℚ) : ℚ :=
  (1 - p + p * y) ^ n

/-- Direct finite-sum form of the same binomial exponential moment. -/
def binomialExpMomentSum (n : ℕ) (p y : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℚ) * p ^ k * (1 - p) ^ (n - k) * y ^ k

theorem geometric_exp_moment_exact_values :
    geometricExpMoment ((1 : ℚ) / 4) 2 = (3 : ℚ) / 2 ∧
      geometricExpMoment ((1 : ℚ) / 5) 3 = 2 ∧
      geometricExpMoment ((1 : ℚ) / 6) 4 = (5 : ℚ) / 2 := by
  native_decide

theorem binomial_exp_moment_exact_values :
    binomialExpMoment 4 ((1 : ℚ) / 2) 3 = 16 ∧
      binomialExpMoment 3 ((1 : ℚ) / 3) 4 = 8 ∧
      binomialExpMoment 5 ((2 : ℚ) / 5) 2 = (16807 : ℚ) / 3125 := by
  native_decide

theorem binomial_exp_moment_sum_identities :
    binomialExpMomentSum 4 ((1 : ℚ) / 2) 3 =
        binomialExpMoment 4 ((1 : ℚ) / 2) 3 ∧
      binomialExpMomentSum 3 ((1 : ℚ) / 3) 4 =
        binomialExpMoment 3 ((1 : ℚ) / 3) 4 ∧
      binomialExpMomentSum 5 ((2 : ℚ) / 5) 2 =
        binomialExpMoment 5 ((2 : ℚ) / 5) 2 := by
  native_decide

end LargeDeviations
