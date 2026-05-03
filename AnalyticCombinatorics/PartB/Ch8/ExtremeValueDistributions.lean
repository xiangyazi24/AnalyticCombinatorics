import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace ExtremeValueDistributions

open Finset

/-!
  Extreme-value and order-statistic tables from Chapter VIII themes:
  maxima, records, discrete order statistics, and small LIS bounds.

  The statements are deliberately finite.  The data are kept in `Fin` tables
  and the checks are bounded numerical identities.
-/

/-! ## Continuous uniform maxima

  For `n` independent continuous uniform samples on `[0,1]`,
  `E max = n/(n+1)`.  The following tables store the numerators and
  denominators for `n = 1, ..., 12`.
-/

def uniformMaxExpectedNumerator : Fin 12 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def uniformMaxExpectedDenominator : Fin 12 → ℕ :=
  ![2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

theorem uniformMaxExpected_table :
    ∀ i : Fin 12,
      uniformMaxExpectedNumerator i + 1 = uniformMaxExpectedDenominator i := by
  native_decide

theorem uniformMaxExpected_numerator_sum :
    (∑ i : Fin 12, uniformMaxExpectedNumerator i) = 78 := by
  native_decide

theorem uniformMaxExpected_last_denominator :
    uniformMaxExpectedDenominator 11 = 13 := by
  native_decide

/-! ## Record values in permutations

  The expected number of left-to-right records in a random permutation of
  `n` elements is the harmonic number `H_n`.  Multiplying by `n!` gives the
  integer table `n! H_n` for `n = 1, ..., 12`.
-/

def recordExpectationScaledNumerator : Fin 12 → ℕ :=
  ![1, 3, 11, 50, 274, 1764, 13068, 109584, 1026576, 10628640, 120543840,
    1486442880]

def factorialHarmonicNumerator (n : ℕ) : ℕ :=
  ∑ k ∈ range n, Nat.factorial n / (k + 1)

theorem recordExpectationScaled_table :
    ∀ i : Fin 12,
      recordExpectationScaledNumerator i = factorialHarmonicNumerator (i.1 + 1) := by
  native_decide

theorem recordExpectationScaled_six :
    recordExpectationScaledNumerator 5 = 1764 := by
  native_decide

/-! ## Record-count distribution

  The distribution of the number of records in permutations has the same
  rows as unsigned Stirling numbers of the first kind.  The row below is
  for permutations of size `6`, indexed by the number of records.
-/

def recordCountDistributionSix : Fin 7 → ℕ :=
  ![0, 120, 274, 225, 85, 15, 1]

theorem recordCountDistributionSix_total :
    (∑ k : Fin 7, recordCountDistributionSix k) = Nat.factorial 6 := by
  native_decide

theorem recordCountDistributionSix_weighted_total :
    (∑ k : Fin 7, k.1 * recordCountDistributionSix k) =
      recordExpectationScaledNumerator 5 := by
  native_decide

theorem recordCountDistributionSix_mode :
    recordCountDistributionSix 2 = 274 ∧
      recordCountDistributionSix 2 > recordCountDistributionSix 3 := by
  native_decide

/-! ## Discrete uniform order statistics

  For samples from `{1, ..., m}`, the total maximum over all `m^n` words is
  `Σ j, j * (j^n - (j-1)^n)`.  These are integer numerators for expected
  maxima.
-/

def discreteUniformMaxTotal (m n : ℕ) : ℕ :=
  ∑ j ∈ range m, (j + 1) * ((j + 1) ^ n - j ^ n)

def discreteUniformMaxTotalFour : Fin 8 → ℕ :=
  ![10, 50, 220, 926, 3820, 15590, 63220, 255326]

def discreteUniformMaxTotalFive : Fin 6 → ℕ :=
  ![15, 95, 525, 2771, 14325, 73235]

theorem discreteUniformMaxTotalFour_table :
    ∀ i : Fin 8,
      discreteUniformMaxTotalFour i = discreteUniformMaxTotal 4 (i.1 + 1) := by
  native_decide

theorem discreteUniformMaxTotalFive_table :
    ∀ i : Fin 6,
      discreteUniformMaxTotalFive i = discreteUniformMaxTotal 5 (i.1 + 1) := by
  native_decide

theorem discreteUniformMaxTotalFour_upper_bound :
    ∀ i : Fin 8,
      discreteUniformMaxTotalFour i ≤ 4 ^ (i.1 + 1) * 4 := by
  native_decide

theorem discreteUniformMaxTotalFive_first_moment :
    discreteUniformMaxTotalFive 0 = 1 + 2 + 3 + 4 + 5 := by
  native_decide

/-! ## Longest increasing subsequences

  For permutations of size `4`, the counts by LIS length `0,1,2,3,4` are
  stored below.  The Catalan number `14` appears as the number with
  LIS length at most `2`, i.e. the `123`-avoiding permutations.
-/

def lisLengthDistributionFour : Fin 5 → ℕ :=
  ![0, 1, 13, 9, 1]

theorem lisLengthDistributionFour_total :
    (∑ k : Fin 5, lisLengthDistributionFour k) = Nat.factorial 4 := by
  native_decide

theorem lisLengthDistributionFour_avoid123 :
    lisLengthDistributionFour 1 + lisLengthDistributionFour 2 = 14 := by
  native_decide

theorem lisLengthDistributionFour_extreme_terms :
    lisLengthDistributionFour 1 = 1 ∧ lisLengthDistributionFour 4 = 1 := by
  native_decide

/-! ## Small Erdos-Szekeres square-root bounds

  The table records the guaranteed lower bound on `max(LIS,LDS)` given by
  the square-root form for permutation lengths `1, ..., 10`.
-/

def lisOrLdsGuaranteed : Fin 10 → ℕ :=
  ![1, 2, 2, 2, 3, 3, 3, 3, 3, 4]

def ceilSqrtSmall (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else if n ≤ 4 then 2 else if n ≤ 9 then 3 else 4

theorem lisOrLdsGuaranteed_table :
    ∀ i : Fin 10, lisOrLdsGuaranteed i = ceilSqrtSmall (i.1 + 1) := by
  native_decide

theorem lisOrLdsGuaranteed_square_characterization :
    ∀ i : Fin 10,
      (lisOrLdsGuaranteed i - 1) ^ 2 < i.1 + 1 ∧
        i.1 + 1 ≤ (lisOrLdsGuaranteed i) ^ 2 := by
  native_decide

end ExtremeValueDistributions
