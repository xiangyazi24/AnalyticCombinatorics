import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace CouponCollector

open Finset

/-!
# Coupon Collector and Occupancy Statistics

Finite, decidable checks for Chapter IX coupon-collector, occupancy, birthday,
and hashing estimates.  The asymptotic statements are represented by exact
rational formulae and scaled integer shadows, so every proof is discharged by
`native_decide`.
-/

/-! ## 1. Coupon collector expectation -/

/-- Harmonic number `H_n = 1 + 1/2 + ... + 1/n`. -/
def harmonicNumber (n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n, 1 / ((i + 1 : Nat) : ℚ)

/-- Coupon collector expected time: `E[T_n] = n H_n`. -/
def couponCollectorExpectedTime (n : Nat) : ℚ :=
  (n : ℚ) * harmonicNumber n

/-- Integer numerator of `n! H_n`, computed as `Σ n!/k`. -/
def harmonicScaledByFactorial (n : Nat) : Nat :=
  ∑ i ∈ Finset.range n, Nat.factorial n / (i + 1)

/-- Pair representation of `H_n` scaled by `n!`. -/
def harmonicFactorialPair (n : Nat) : Nat × Nat :=
  (harmonicScaledByFactorial n, Nat.factorial n)

/-- Pair representation of `E[T_n] = n H_n` scaled by `n!`. -/
def expectedTimeFactorialPair (n : Nat) : Nat × Nat :=
  (n * harmonicScaledByFactorial n, Nat.factorial n)

theorem harmonic_values_1_to_6 :
    harmonicNumber 1 = 1 ∧
    harmonicNumber 2 = 3 / 2 ∧
    harmonicNumber 3 = 11 / 6 ∧
    harmonicNumber 4 = 25 / 12 ∧
    harmonicNumber 5 = 137 / 60 ∧
    harmonicNumber 6 = 49 / 20 := by
  native_decide

theorem coupon_collector_expectation_values_1_to_6 :
    couponCollectorExpectedTime 1 = 1 ∧
    couponCollectorExpectedTime 2 = 3 ∧
    couponCollectorExpectedTime 3 = 11 / 2 ∧
    couponCollectorExpectedTime 4 = 25 / 3 ∧
    couponCollectorExpectedTime 5 = 137 / 12 ∧
    couponCollectorExpectedTime 6 = 147 / 10 := by
  native_decide

theorem harmonic_factorial_pairs_1_to_6 :
    [harmonicFactorialPair 1,
     harmonicFactorialPair 2,
     harmonicFactorialPair 3,
     harmonicFactorialPair 4,
     harmonicFactorialPair 5,
     harmonicFactorialPair 6] =
      [(1, 1), (3, 2), (11, 6), (50, 24), (274, 120), (1764, 720)] := by
  native_decide

theorem expected_time_factorial_pairs_1_to_6 :
    [expectedTimeFactorialPair 1,
     expectedTimeFactorialPair 2,
     expectedTimeFactorialPair 3,
     expectedTimeFactorialPair 4,
     expectedTimeFactorialPair 5,
     expectedTimeFactorialPair 6] =
      [(1, 1), (6, 2), (33, 6), (200, 24), (1370, 120), (10584, 720)] := by
  native_decide

/-! ## 2. Coupon collector variance -/

/--
Variance of the coupon collector time:

`Var[T_n] = Σ_{j=1}^n n(n-j)/j^2 = n^2 H_n^{(2)} - n H_n`.
-/
def couponCollectorVariance (n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n,
    let j := i + 1
    ((n * (n - j) : Nat) : ℚ) / ((j : ℚ) ^ 2)

/-- Integer numerator after scaling `Var[T_n]` by `(n!)^2`. -/
def varianceScaledByFactorialSquared (n : Nat) : Nat :=
  ∑ i ∈ Finset.range n,
    let j := i + 1
    n * (n - j) * (Nat.factorial n / j) ^ 2

/-- Pair representation of `Var[T_n]` scaled by `(n!)^2`. -/
def varianceFactorialSquaredPair (n : Nat) : Nat × Nat :=
  (varianceScaledByFactorialSquared n, (Nat.factorial n) ^ 2)

/-- Decimal integer shadow of `π^2/6 ≈ 1.644934`, scaled by `10^6`. -/
def piSquaredOverSixScaled : Nat := 1644934

theorem variance_values_1_to_6 :
    couponCollectorVariance 1 = 0 ∧
    couponCollectorVariance 2 = 2 ∧
    couponCollectorVariance 3 = 27 / 4 ∧
    couponCollectorVariance 4 = 130 / 9 ∧
    couponCollectorVariance 5 = 3625 / 144 ∧
    couponCollectorVariance 6 = 3899 / 100 := by
  native_decide

theorem variance_factorial_squared_pairs_1_to_6 :
    [varianceFactorialSquaredPair 1,
     varianceFactorialSquaredPair 2,
     varianceFactorialSquaredPair 3,
     varianceFactorialSquaredPair 4,
     varianceFactorialSquaredPair 5,
     varianceFactorialSquaredPair 6] =
      [(0, 1), (8, 4), (243, 36), (8320, 576), (362500, 14400),
        (20212416, 518400)] := by
  native_decide

theorem variance_below_basel_shadow_n6 :
    couponCollectorVariance 6 * 1000000 <
      ((6 : ℚ) ^ 2) * (piSquaredOverSixScaled : ℚ) := by
  native_decide

/-! ## 3. Birthday collision threshold -/

/-- Falling factorial `n(n-1)...(n-k+1)`, the no-collision assignment count. -/
def fallingFactorial (n k : Nat) : Nat :=
  ∏ i ∈ Finset.range k, (n - i)

/-- Exact no-collision probability for `k` draws from `n` urns. -/
def birthdayNoCollisionProbability (n k : Nat) : ℚ :=
  (fallingFactorial n k : ℚ) / ((n ^ k : Nat) : ℚ)

/-- Collision probability for `k` draws from `n` urns. -/
def birthdayCollisionProbability (n k : Nat) : ℚ :=
  1 - birthdayNoCollisionProbability n k

/-- Integer numerator/denominator pair for the no-collision probability. -/
def birthdayNoCollisionPair (n k : Nat) : Nat × Nat :=
  (fallingFactorial n k, n ^ k)

/-- Integer approximation to `ln 2`, scaled by `1000`. -/
def ln2ScaledBy1000 : Nat := 693

/-- Integer shadow of the median birthday threshold equation `k^2 ≈ 2 n ln 2`. -/
def birthdayThresholdRightScaled (n : Nat) : Nat :=
  2 * n * ln2ScaledBy1000

/-- Left side `k^2`, scaled by the same factor as `ln2ScaledBy1000`. -/
def birthdayThresholdLeftScaled (k : Nat) : Nat :=
  k ^ 2 * 1000

theorem birthday_threshold_365_between_22_and_23 :
    birthdayThresholdLeftScaled 22 < birthdayThresholdRightScaled 365 ∧
    birthdayThresholdRightScaled 365 < birthdayThresholdLeftScaled 23 := by
  native_decide

theorem birthday_no_collision_pair_365_23 :
    birthdayNoCollisionPair 365 23 =
      (42200819302092359872395663074908957253749760700776448000000,
        85651679353150321236814267844395152689354622364044189453125) := by
  native_decide

theorem birthday_collision_probability_small_values :
    birthdayCollisionProbability 365 1 = 0 ∧
    birthdayCollisionProbability 365 2 = 1 / 365 ∧
    birthdayCollisionProbability 365 3 = 1093 / 133225 := by
  native_decide

/-! ## 4. Expected distinct values after repeated draws -/

/-- Expected number of distinct values observed after `m` draws from `n` types. -/
def expectedDistinctValues (n m : Nat) : ℚ :=
  (n : ℚ) * (1 - (1 - 1 / (n : ℚ)) ^ m)

/-- Numerator over denominator `n^m` for the expected-distinct formula. -/
def expectedDistinctScaledPair (n m : Nat) : Nat × Nat :=
  (n * (n ^ m - (n - 1) ^ m), n ^ m)

theorem expected_distinct_six_draws_six_types :
    expectedDistinctValues 6 6 = 31031 / 7776 ∧
    expectedDistinctScaledPair 6 6 = (186186, 46656) := by
  native_decide

theorem expected_distinct_small_values :
    expectedDistinctValues 6 0 = 0 ∧
    expectedDistinctValues 6 1 = 1 ∧
    expectedDistinctValues 6 2 = 11 / 6 ∧
    expectedDistinctValues 6 3 = 91 / 36 := by
  native_decide

/-! ## 5. Double coverage -/

/--
Integral/inclusion-exclusion term for collecting every coupon at least twice:

`E[T_{n,2}] = n Σ_{j=1}^n (-1)^(j+1) C(n,j)
  Σ_{l=0}^j C(j,l) l! / j^(l+1)`.
-/
def doubleCoverageInnerTerm (j : Nat) : ℚ :=
  ∑ l ∈ Finset.range (j + 1),
    (Nat.choose j l : ℚ) * (Nat.factorial l : ℚ) / ((j : ℚ) ^ (l + 1))

/-- Expected time to collect every coupon at least twice. -/
def doubleCoverageExpectedTime (n : Nat) : ℚ :=
  (n : ℚ) *
    ∑ i ∈ Finset.range n,
      let j := i + 1
      (-1 : ℚ) ^ (j + 1) * (Nat.choose n j : ℚ) * doubleCoverageInnerTerm j

theorem double_coverage_expected_values_1_to_6 :
    doubleCoverageExpectedTime 1 = 2 ∧
    doubleCoverageExpectedTime 2 = 11 / 2 ∧
    doubleCoverageExpectedTime 3 = 347 / 36 ∧
    doubleCoverageExpectedTime 4 = 12259 / 864 ∧
    doubleCoverageExpectedTime 5 = 41129339 / 2160000 ∧
    doubleCoverageExpectedTime 6 = 390968681 / 16200000 := by
  native_decide

theorem double_coverage_exceeds_single_coverage_1_to_6 :
    couponCollectorExpectedTime 1 < doubleCoverageExpectedTime 1 ∧
    couponCollectorExpectedTime 2 < doubleCoverageExpectedTime 2 ∧
    couponCollectorExpectedTime 3 < doubleCoverageExpectedTime 3 ∧
    couponCollectorExpectedTime 4 < doubleCoverageExpectedTime 4 ∧
    couponCollectorExpectedTime 5 < doubleCoverageExpectedTime 5 ∧
    couponCollectorExpectedTime 6 < doubleCoverageExpectedTime 6 := by
  native_decide

/-! ## 6. Flajolet-Martin bit-pattern estimator -/

/-- Number of trailing zero bits before the first one, capped by `width`. -/
def trailingZerosBounded : Nat → Nat → Nat
  | _, 0 => 0
  | x, width + 1 =>
      if x % 2 = 1 then 0 else 1 + trailingZerosBounded (x / 2) width

/-- Flajolet-Martin register: the maximum observed trailing-zero count. -/
def fmRegister : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, width => Nat.max (trailingZerosBounded x width) (fmRegister xs width)

/-- Flajolet-Martin correction constant `φ ≈ 0.77351`, scaled by `100000`. -/
def fmPhiScaledBy100000 : Nat := 77351

/-- FM estimate `2^R / φ`, represented as an exact rational using scaled `φ`. -/
def flajoletMartinEstimate (register : Nat) : ℚ :=
  (((2 ^ register : Nat) : ℚ) * 100000) / (fmPhiScaledBy100000 : ℚ)

theorem trailing_zero_bit_patterns :
    trailingZerosBounded 1 8 = 0 ∧
    trailingZerosBounded 2 8 = 1 ∧
    trailingZerosBounded 4 8 = 2 ∧
    trailingZerosBounded 8 8 = 3 ∧
    trailingZerosBounded 40 8 = 3 ∧
    trailingZerosBounded 96 8 = 5 ∧
    trailingZerosBounded 0 8 = 8 := by
  native_decide

theorem flajolet_martin_register_examples :
    fmRegister [1, 2, 4, 8, 40] 8 = 3 ∧
    fmRegister [3, 5, 12, 96, 128] 8 = 7 := by
  native_decide

theorem flajolet_martin_estimate_examples :
    flajoletMartinEstimate 3 = 800000 / 77351 ∧
    flajoletMartinEstimate 7 = 12800000 / 77351 := by
  native_decide

end CouponCollector
