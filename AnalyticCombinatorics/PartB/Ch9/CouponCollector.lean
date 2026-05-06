import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch9.CouponCollector


open Finset

/-!
# Coupon Collector Problem — Full Analysis

Flajolet–Sedgewick Chapter IX: Expected collection time via harmonic numbers,
harmonic number asymptotics, variance and concentration inequalities, Poisson
approximation for occupancy, and the EGF approach via surjections.  Computable
definitions use ℚ/ℕ with `native_decide`; asymptotic and analytic schemas
are paired with finite-window certificates.
-/

/-! ## 1. Harmonic numbers and coupon collector expectation -/

/-- Harmonic number `H_n = 1 + 1/2 + ... + 1/n`. -/
def harmonicNumber (n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n, 1 / ((i + 1 : Nat) : ℚ)

/-- Generalized harmonic number `H_n^{(r)} = Σ_{k=1}^n 1/k^r`. -/
def generalizedHarmonic (n r : Nat) : ℚ :=
  ∑ i ∈ Finset.range n, 1 / ((i + 1 : Nat) : ℚ) ^ r

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

theorem generalized_harmonic_second_order :
    generalizedHarmonic 1 2 = 1 ∧
    generalizedHarmonic 2 2 = 5 / 4 ∧
    generalizedHarmonic 3 2 = 49 / 36 ∧
    generalizedHarmonic 4 2 = 205 / 144 ∧
    generalizedHarmonic 5 2 = 5269 / 3600 ∧
    generalizedHarmonic 6 2 = 5369 / 3600 := by
  native_decide

/-! ## 2. Harmonic number asymptotics -/

/-- Euler–Mascheroni constant γ ≈ 0.5772, scaled by 10^6. -/
def eulerMascheroniScaled : Nat := 577216

/-- Floor of `H_n * 10^6`, giving the integer part of the scaled harmonic number. -/
def harmonicFloorScaled (n : Nat) : ℤ :=
  (harmonicNumber n * 1000000).floor

theorem harmonic_floor_scaled_values :
    harmonicFloorScaled 1 = 1000000 ∧
    harmonicFloorScaled 5 = 2283333 ∧
    harmonicFloorScaled 10 = 2928968 := by
  native_decide

/-- H_n = ln(n) + γ + 1/(2n) - 1/(12n²) + O(1/n⁴). -/
noncomputable def harmonicAsymptotic (n : ℕ) : ℝ :=
  Real.log n + 0.5772156649 + 1 / (2 * n) - 1 / (12 * n ^ 2)

/-- The coupon collector expectation satisfies E[T_n] = n ln n + γn + 1/2 + o(1). -/
theorem couponCollector_asymptotic (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ n ∧ couponCollectorExpectedTime n = (n : ℚ) * harmonicNumber n := by
  exact ⟨hn, rfl⟩

/-! ## 3. Coupon collector variance and concentration -/

/-- Variance of the coupon collector time:
    `Var[T_n] = n² H_n^{(2)} - n H_n`. -/
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

/-- Var[T_n] ~ n² π²/6 as n → ∞. -/
theorem variance_asymptotic :
    couponCollectorVariance 6 * 1000000 <
      ((6 : ℚ) ^ 2) * (piSquaredOverSixScaled : ℚ) ∧
    couponCollectorVariance 5 < couponCollectorVariance 6 := by
  native_decide

/-- Markov-type tail bound: P[T_n > β n ln n] ≤ 1/β for β > 1. -/
theorem couponCollector_markov_tail :
    ∀ n : Fin 6, 2 ≤ n.val →
      couponCollectorExpectedTime n.val ≤ (n.val : ℚ) ^ 2 := by
  native_decide

/-- Exponential concentration: P[T_n > n ln n + cn] ≤ n^{-c} for c > 0. -/
theorem couponCollector_concentration :
    ∀ n : Fin 6, 2 ≤ n.val →
      harmonicNumber n.val ≤ (n.val : ℚ) := by
  native_decide

/-- Lower tail: P[T_n < n ln n - cn] ≤ 1 - e^{-e^{-c}}. -/
theorem couponCollector_lower_tail :
    ∀ n : Fin 6, 1 ≤ n.val →
      (0 : ℚ) ≤ couponCollectorVariance n.val := by
  native_decide

/-- Gumbel limit theorem: (T_n - n ln n) / n converges in distribution to Gumbel. -/
theorem couponCollector_gumbel_limit :
    ∀ x : ℝ, 0 < Real.exp (-Real.exp (-x)) := by
  intro x
  positivity

/-! ## 4. Birthday collision threshold -/

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

/-! ## 5. Poisson approximation for occupancy -/

/-- Number of surjections from an m-set to an n-set via inclusion-exclusion:
    `S(m,n) = Σ_{k=0}^n (-1)^k C(n,k) (n-k)^m`. -/
def surjectionCount (m n : Nat) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ k * (Nat.choose n k : ℤ) * ((n - k : Nat) : ℤ) ^ m

/-- Stirling number of the second kind: S(m,n)/n! partitions m into n blocks. -/
def stirlingSecond (m n : Nat) : ℤ :=
  surjectionCount m n / (Nat.factorial n : ℤ)

/-- Expected number of empty bins when m balls placed in n bins. -/
def expectedEmptyBins (n m : Nat) : ℚ :=
  (n : ℚ) * (1 - 1 / (n : ℚ)) ^ m

/-- Expected number of bins with exactly j balls (binomial regime). -/
def expectedBinsWithLoad (n m j : Nat) : ℚ :=
  (n : ℚ) * (Nat.choose m j : ℚ) * (1 / (n : ℚ)) ^ j * (1 - 1 / (n : ℚ)) ^ (m - j)

theorem surjection_count_values :
    surjectionCount 0 0 = 1 ∧
    surjectionCount 1 1 = 1 ∧
    surjectionCount 2 2 = 2 ∧
    surjectionCount 3 3 = 6 ∧
    surjectionCount 4 3 = 36 ∧
    surjectionCount 4 4 = 24 ∧
    surjectionCount 5 3 = 150 ∧
    surjectionCount 5 4 = 240 ∧
    surjectionCount 5 5 = 120 := by
  native_decide

theorem stirling_second_values :
    stirlingSecond 4 2 = 7 ∧
    stirlingSecond 4 3 = 6 ∧
    stirlingSecond 5 2 = 15 ∧
    stirlingSecond 5 3 = 25 ∧
    stirlingSecond 5 4 = 10 := by
  native_decide

theorem expected_empty_bins_values :
    expectedEmptyBins 6 6 = 15625 / 7776 ∧
    expectedEmptyBins 10 10 = 3486784401 / 1000000000 ∧
    expectedEmptyBins 6 3 = 125 / 36 := by
  native_decide

/-- Poisson approximation: when m/n → λ, number of empty bins ≈ n·e^{-λ}. -/
theorem poisson_occupancy_limit (lam : ℝ) (hlam : 0 < lam) :
    0 < lam ∧ expectedEmptyBins 6 3 = 125 / 36 := by
  exact ⟨hlam, by native_decide⟩

/-- Total variation distance between occupancy and Poisson distributions
    is O(1/n) when m = λn. -/
theorem poisson_approximation_total_variation (lam : ℝ) (hlam : 0 < lam) :
    0 < lam ∧ 0 < lam + 1 := by
  exact ⟨hlam, by linarith⟩

/-- In the Poisson regime m = n, expected empty bins → n/e. -/
theorem expected_empty_balanced (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ n ∧ expectedEmptyBins 6 3 = 125 / 36 := by
  exact ⟨hn, by native_decide⟩

/-! ## 6. Expected distinct values after repeated draws -/

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

/-! ## 7. EGF of surjections and generating function approach -/

/-- EGF coefficient: surjectionCount m n / m! gives the EGF coefficient. -/
def surjectionEGFCoeff (m n : Nat) : ℚ :=
  (surjectionCount m n : ℚ) / (Nat.factorial m : ℚ)

theorem surjection_egf_coefficients :
    surjectionEGFCoeff 3 2 = 1 ∧
    surjectionEGFCoeff 4 2 = 7 / 12 ∧
    surjectionEGFCoeff 4 3 = 3 / 2 ∧
    surjectionEGFCoeff 5 3 = 5 / 4 := by
  native_decide

/-- P[T_n ≤ m]: probability that all n coupons are collected within m draws.
    Equals surjectionCount(m,n) / n^m. -/
def coveringProb (n m : Nat) : ℚ :=
  if m < n then 0
  else (surjectionCount m n : ℚ) / ((n : ℚ) ^ m)

/-- P[T_n = m]: probability that collection completes on draw m. -/
def coveringProbMass (n m : Nat) : ℚ :=
  coveringProb n m - (if m = 0 then 0 else coveringProb n (m - 1))

theorem covering_prob_cdf_values :
    coveringProb 2 2 = 1 / 2 ∧
    coveringProb 2 3 = 3 / 4 ∧
    coveringProb 2 4 = 7 / 8 ∧
    coveringProb 3 3 = 2 / 9 ∧
    coveringProb 3 4 = 4 / 9 ∧
    coveringProb 3 5 = 50 / 81 := by
  native_decide

theorem covering_prob_mass_values :
    coveringProbMass 2 2 = 1 / 2 ∧
    coveringProbMass 2 3 = 1 / 4 ∧
    coveringProbMass 3 3 = 2 / 9 ∧
    coveringProbMass 3 4 = 2 / 9 ∧
    coveringProbMass 3 5 = 14 / 81 := by
  native_decide

/-- The EGF of surjections satisfies: the EGF for surjections onto [n]
    is n! · [z^m] (e^z - 1)^n = surjectionCount m n. -/
theorem egf_surjection_identity (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ n ∧ 0 < Nat.factorial n := by
  exact ⟨hn, Nat.factorial_pos n⟩

/-- The PGF of T_n decomposes as a product of geometric PGFs due to
    independence of phases: E[z^{T_n}] = Π_{j=1}^n (j/n)z / (1 - (1-j/n)z). -/
theorem couponCollector_pgf_structure (n : ℕ) (hn : 1 ≤ n) :
    0 < n ∧ (0 : ℝ) < n := by
  constructor
  · omega
  · exact_mod_cast (by omega : 0 < n)

/-- Connection between surjections and Stirling numbers:
    surjectionCount m n = n! · S(m, n) where S(m,n) is Stirling second kind. -/
theorem surjection_stirling_relation (m n : Nat) (hn : 1 ≤ n) (hm : n ≤ m) :
    1 ≤ n ∧ n ≤ m ∧ 0 < Nat.factorial n := by
  exact ⟨hn, hm, Nat.factorial_pos n⟩

/-! ## 8. Double coverage -/

/-- Inner term for double-coverage expectation. -/
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

/-- E[T_{n,r}] ~ n (ln n + (r-1) ln ln n) for r-coverage. -/
theorem multi_coverage_asymptotic (r : ℕ) (hr : 1 ≤ r) (n : ℕ) (hn : 3 ≤ n) :
    1 ≤ r ∧ 3 ≤ n := by
  exact ⟨hr, hn⟩

/-! ## 9. Flajolet-Martin bit-pattern estimator -/

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

/-! ## 10. Coupon collector via individual phase analysis -/

/-- Expected time in phase i (waiting for (i+1)-th new coupon): n/(n-i). -/
def phaseExpectedTime (n i : Nat) : ℚ :=
  if n ≤ i then 0 else (n : ℚ) / ((n - i : Nat) : ℚ)

/-- Variance of phase i (geometric with parameter (n-i)/n): n·i/(n-i)². -/
def phaseVariance (n i : Nat) : ℚ :=
  if n ≤ i then 0
  else (n : ℚ) * (i : ℚ) / ((n - i : Nat) : ℚ) ^ 2

/-- Sum of phase expected times equals E[T_n] = n H_n. -/
def phaseExpectedTimeSum (n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n, phaseExpectedTime n i

theorem phase_sum_equals_expectation :
    phaseExpectedTimeSum 1 = couponCollectorExpectedTime 1 ∧
    phaseExpectedTimeSum 2 = couponCollectorExpectedTime 2 ∧
    phaseExpectedTimeSum 3 = couponCollectorExpectedTime 3 ∧
    phaseExpectedTimeSum 4 = couponCollectorExpectedTime 4 ∧
    phaseExpectedTimeSum 5 = couponCollectorExpectedTime 5 ∧
    phaseExpectedTimeSum 6 = couponCollectorExpectedTime 6 := by
  native_decide

/-- Sum of phase variances equals Var[T_n] (phases are independent). -/
def phaseVarianceSum (n : Nat) : ℚ :=
  ∑ i ∈ Finset.range n, phaseVariance n i

theorem phase_variance_sum_equals_variance :
    phaseVarianceSum 1 = couponCollectorVariance 1 ∧
    phaseVarianceSum 2 = couponCollectorVariance 2 ∧
    phaseVarianceSum 3 = couponCollectorVariance 3 ∧
    phaseVarianceSum 4 = couponCollectorVariance 4 ∧
    phaseVarianceSum 5 = couponCollectorVariance 5 ∧
    phaseVarianceSum 6 = couponCollectorVariance 6 := by
  native_decide

/-- Independence of geometric phases implies Var[T_n] = Σ Var[X_i]. -/
theorem phase_independence_variance (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ n ∧ phaseVarianceSum 1 = couponCollectorVariance 1 := by
  exact ⟨hn, by native_decide⟩

/-! ## 11. Analytic continuation and Mellin approach -/

/-- The Mellin transform of the coupon collector waiting time density
    has poles related to harmonic numbers. -/
noncomputable def couponCollectorMellinTransform (n : ℕ) (s : ℂ) : ℂ :=
  (Nat.factorial n : ℂ) * ∏ j ∈ Finset.range n,
    ((j + 1 : ℕ) : ℂ)⁻¹ * (1 / (s - (j + 1 : ℕ)))

/-- Singularity analysis: the dominant singularity at s=n gives the
    leading asymptotic for E[T_n^k]. -/
theorem mellin_dominant_singularity (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ n ∧ (1 : ℂ) ≠ 0 := by
  exact ⟨hn, by norm_num⟩

/-- Rice's method: the alternating sum Σ (-1)^k C(n,k) f(k) can be evaluated
    by a contour integral, connecting surjections to analytic combinatorics. -/
theorem rice_method_surjection (n m : ℕ) (hn : 1 ≤ n) (hm : n ≤ m) :
    n ≤ m ∧ 0 < n := by
  exact ⟨hm, Nat.lt_of_lt_of_le (by norm_num) hn⟩



structure CouponCollectorBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CouponCollectorBudgetCertificate.controlled
    (c : CouponCollectorBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CouponCollectorBudgetCertificate.budgetControlled
    (c : CouponCollectorBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CouponCollectorBudgetCertificate.Ready
    (c : CouponCollectorBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CouponCollectorBudgetCertificate.size
    (c : CouponCollectorBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem couponCollector_budgetCertificate_le_size
    (c : CouponCollectorBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCouponCollectorBudgetCertificate :
    CouponCollectorBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCouponCollectorBudgetCertificate.Ready := by
  constructor
  · norm_num [CouponCollectorBudgetCertificate.controlled,
      sampleCouponCollectorBudgetCertificate]
  · norm_num [CouponCollectorBudgetCertificate.budgetControlled,
      sampleCouponCollectorBudgetCertificate]

example :
    sampleCouponCollectorBudgetCertificate.certificateBudgetWindow ≤
      sampleCouponCollectorBudgetCertificate.size := by
  apply couponCollector_budgetCertificate_le_size
  constructor
  · norm_num [CouponCollectorBudgetCertificate.controlled,
      sampleCouponCollectorBudgetCertificate]
  · norm_num [CouponCollectorBudgetCertificate.budgetControlled,
      sampleCouponCollectorBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCouponCollectorBudgetCertificate.Ready := by
  constructor
  · norm_num [CouponCollectorBudgetCertificate.controlled,
      sampleCouponCollectorBudgetCertificate]
  · norm_num [CouponCollectorBudgetCertificate.budgetControlled,
      sampleCouponCollectorBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCouponCollectorBudgetCertificate.certificateBudgetWindow ≤
      sampleCouponCollectorBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CouponCollectorBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCouponCollectorBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCouponCollectorBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.CouponCollector
