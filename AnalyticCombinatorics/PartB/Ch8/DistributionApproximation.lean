import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch8.DistributionApproximation


open scoped BigOperators

/-!
Finite tables for distribution approximation and convergence checks in the
spirit of Chapter VIII.  Probabilities are represented by integer numerators
or by fixed decimal scalings, so every statement is a bounded computation.
-/

def absDiff (a b : ℕ) : ℕ :=
  if a ≤ b then b - a else a - b

/-! ## Binomial CDF and a normal-approximation table -/

def binom10Mass : Fin 11 → ℕ :=
  ![1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1]

def binom10CdfNumerator : Fin 11 → ℕ :=
  ![1, 11, 56, 176, 386, 638, 848, 968, 1013, 1023, 1024]

def binom10CdfNumeratorFormula (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), Nat.choose 10 j

def binom10CdfPerMille : Fin 11 → ℕ :=
  ![0, 10, 54, 171, 376, 623, 828, 945, 989, 999, 1000]

/-- Continuity-corrected normal CDF values, scaled by `1000`, for `Binomial(10,1/2)`. -/
def normalApproxBinom10CdfPerMille : Fin 11 → ℕ :=
  ![2, 13, 57, 171, 376, 624, 829, 943, 987, 998, 1000]

def binomNormalCdfAbsError : Fin 11 → ℕ :=
  ![2, 3, 3, 0, 0, 1, 1, 2, 2, 1, 0]

theorem binom10_mass_matches_choose :
    (fun k : Fin 11 => Nat.choose 10 k.val) = binom10Mass := by
  native_decide

theorem binom10_cdf_matches_formula :
    (fun k : Fin 11 => binom10CdfNumeratorFormula k.val) = binom10CdfNumerator := by
  native_decide

theorem binom10_cdf_per_mille_table :
    (fun k : Fin 11 => 1000 * binom10CdfNumerator k / 2 ^ 10) = binom10CdfPerMille := by
  native_decide

theorem binom10_normal_cdf_error_table :
    (fun k : Fin 11 => absDiff (binom10CdfPerMille k) (normalApproxBinom10CdfPerMille k))
      = binomNormalCdfAbsError := by
  native_decide

theorem binom10_normal_cdf_error_bound :
    ∀ k : Fin 11, binomNormalCdfAbsError k ≤ 3 := by
  native_decide

theorem binom10_cdf_row_total :
    binom10CdfNumerator 10 = 2 ^ 10 := by
  native_decide

/-! ## Chi-squared critical values -/

/-- Rounded `0.95` chi-squared critical values, scaled by `10`, for degrees `1..8`. -/
def chiSquare95CriticalTenths : Fin 8 → ℕ :=
  ![38, 60, 78, 95, 111, 126, 140, 155]

/-- Rounded Wilson-Hilferty approximation, scaled by `10`, for degrees `1..8`. -/
def chiSquare95WilsonHilfertyTenths : Fin 8 → ℕ :=
  ![38, 59, 78, 95, 111, 125, 140, 154]

def chiSquare95AbsErrorTenths : Fin 8 → ℕ :=
  ![0, 1, 0, 0, 0, 1, 0, 1]

theorem chi_square_error_table :
    (fun d : Fin 8 => absDiff (chiSquare95CriticalTenths d) (chiSquare95WilsonHilfertyTenths d))
      = chiSquare95AbsErrorTenths := by
  native_decide

theorem chi_square_error_at_most_one_tenth :
    ∀ d : Fin 8, chiSquare95AbsErrorTenths d ≤ 1 := by
  native_decide

theorem chi_square_critical_values_increase :
    chiSquare95CriticalTenths 0 < chiSquare95CriticalTenths 1 ∧
    chiSquare95CriticalTenths 1 < chiSquare95CriticalTenths 2 ∧
    chiSquare95CriticalTenths 2 < chiSquare95CriticalTenths 3 ∧
    chiSquare95CriticalTenths 3 < chiSquare95CriticalTenths 4 ∧
    chiSquare95CriticalTenths 4 < chiSquare95CriticalTenths 5 ∧
    chiSquare95CriticalTenths 5 < chiSquare95CriticalTenths 6 ∧
    chiSquare95CriticalTenths 6 < chiSquare95CriticalTenths 7 := by
  native_decide

/-! ## Kolmogorov-Smirnov finite tables -/

/-- Standard `5%` one-sample Kolmogorov-Smirnov critical values, scaled by `1000`, for `n=1..10`. -/
def ksFivePercentCriticalMilli : Fin 10 → ℕ :=
  ![975, 842, 708, 624, 565, 521, 486, 457, 432, 410]

/-- The asymptotic `1.36 / sqrt(n)` rule, rounded and scaled by `1000`, for `n=1..10`. -/
def ksAsymptoticRuleMilli : Fin 10 → ℕ :=
  ![1360, 962, 785, 680, 608, 555, 514, 481, 453, 430]

def ksAsymptoticExcessMilli : Fin 10 → ℕ :=
  ![385, 120, 77, 56, 43, 34, 28, 24, 21, 20]

theorem ks_asymptotic_excess_table :
    (fun n : Fin 10 => ksAsymptoticRuleMilli n - ksFivePercentCriticalMilli n)
      = ksAsymptoticExcessMilli := by
  native_decide

theorem ks_asymptotic_rule_is_upper_table :
    ∀ n : Fin 10, ksFivePercentCriticalMilli n ≤ ksAsymptoticRuleMilli n := by
  native_decide

theorem ks_critical_values_decrease :
    ksFivePercentCriticalMilli 0 > ksFivePercentCriticalMilli 1 ∧
    ksFivePercentCriticalMilli 1 > ksFivePercentCriticalMilli 2 ∧
    ksFivePercentCriticalMilli 2 > ksFivePercentCriticalMilli 3 ∧
    ksFivePercentCriticalMilli 3 > ksFivePercentCriticalMilli 4 ∧
    ksFivePercentCriticalMilli 4 > ksFivePercentCriticalMilli 5 ∧
    ksFivePercentCriticalMilli 5 > ksFivePercentCriticalMilli 6 ∧
    ksFivePercentCriticalMilli 6 > ksFivePercentCriticalMilli 7 ∧
    ksFivePercentCriticalMilli 7 > ksFivePercentCriticalMilli 8 ∧
    ksFivePercentCriticalMilli 8 > ksFivePercentCriticalMilli 9 := by
  native_decide

/-! ## Discrete uniform moments -/

def sumBelow (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range m, k

def sumSquaresBelow (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range m, k ^ 2

/-- `2 * sum_{k=0}^{m-1} k` for `m=1..10`. -/
def uniformTwiceFirstMomentNumerator : Fin 10 → ℕ :=
  ![0, 2, 6, 12, 20, 30, 42, 56, 72, 90]

/-- `sum_{k=0}^{m-1} k^2` for `m=1..10`. -/
def uniformSecondMomentNumerator : Fin 10 → ℕ :=
  ![0, 1, 5, 14, 30, 55, 91, 140, 204, 285]

theorem uniform_first_moment_table :
    (fun m : Fin 10 => 2 * sumBelow (m.val + 1)) = uniformTwiceFirstMomentNumerator := by
  native_decide

theorem uniform_second_moment_table :
    (fun m : Fin 10 => sumSquaresBelow (m.val + 1)) = uniformSecondMomentNumerator := by
  native_decide

theorem uniform_second_moment_closed_form_small :
    ∀ m : Fin 10,
      6 * uniformSecondMomentNumerator m = m.val * (m.val + 1) * (2 * m.val + 1) := by
  native_decide

/-! ## Geometric partial sums -/

/-- Numerators of `P(X < m) = 1 - 2^{-m}`, scaled by `2^m`, for `m=1..10`. -/
def geometricHalfPartialNumerator : Fin 10 → ℕ :=
  ![1, 3, 7, 15, 31, 63, 127, 255, 511, 1023]

theorem geometric_half_partial_sum_table :
    (fun m : Fin 10 => 2 ^ (m.val + 1) - 1) = geometricHalfPartialNumerator := by
  native_decide

theorem geometric_half_partial_sum_below_denominator :
    ∀ m : Fin 10, geometricHalfPartialNumerator m < 2 ^ (m.val + 1) := by
  native_decide

theorem geometric_half_partial_last_value :
    geometricHalfPartialNumerator 9 = 1023 := by
  native_decide

/-! ## Negative binomial coefficient tables -/

/-- Failure counts before the third success: `choose(k+2,2)` for `k=0..9`. -/
def negativeBinomialR3Mass : Fin 10 → ℕ :=
  ![1, 3, 6, 10, 15, 21, 28, 36, 45, 55]

/-- Cumulative numerators for the same row: `sum_{j=0}^k choose(j+2,2)`. -/
def negativeBinomialR3CdfNumerator : Fin 10 → ℕ :=
  ![1, 4, 10, 20, 35, 56, 84, 120, 165, 220]

/-- Failure counts before the fourth success: `choose(k+3,3)` for `k=0..9`. -/
def negativeBinomialR4Mass : Fin 10 → ℕ :=
  ![1, 4, 10, 20, 35, 56, 84, 120, 165, 220]

def negativeBinomialR3CdfFormula (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), Nat.choose (j + 2) 2

theorem negative_binomial_r3_mass_table :
    (fun k : Fin 10 => Nat.choose (k.val + 2) 2) = negativeBinomialR3Mass := by
  native_decide

theorem negative_binomial_r3_cdf_table :
    (fun k : Fin 10 => negativeBinomialR3CdfFormula k.val) = negativeBinomialR3CdfNumerator := by
  native_decide

theorem negative_binomial_hockey_stick_small :
    negativeBinomialR3CdfNumerator = negativeBinomialR4Mass := by
  native_decide



structure DistributionApproximationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DistributionApproximationBudgetCertificate.controlled
    (c : DistributionApproximationBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DistributionApproximationBudgetCertificate.budgetControlled
    (c : DistributionApproximationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DistributionApproximationBudgetCertificate.Ready
    (c : DistributionApproximationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DistributionApproximationBudgetCertificate.size
    (c : DistributionApproximationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem distributionApproximation_budgetCertificate_le_size
    (c : DistributionApproximationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDistributionApproximationBudgetCertificate :
    DistributionApproximationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleDistributionApproximationBudgetCertificate.Ready := by
  constructor
  · norm_num [DistributionApproximationBudgetCertificate.controlled,
      sampleDistributionApproximationBudgetCertificate]
  · norm_num [DistributionApproximationBudgetCertificate.budgetControlled,
      sampleDistributionApproximationBudgetCertificate]

example :
    sampleDistributionApproximationBudgetCertificate.certificateBudgetWindow ≤
      sampleDistributionApproximationBudgetCertificate.size := by
  apply distributionApproximation_budgetCertificate_le_size
  constructor
  · norm_num [DistributionApproximationBudgetCertificate.controlled,
      sampleDistributionApproximationBudgetCertificate]
  · norm_num [DistributionApproximationBudgetCertificate.budgetControlled,
      sampleDistributionApproximationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDistributionApproximationBudgetCertificate.Ready := by
  constructor
  · norm_num [DistributionApproximationBudgetCertificate.controlled,
      sampleDistributionApproximationBudgetCertificate]
  · norm_num [DistributionApproximationBudgetCertificate.budgetControlled,
      sampleDistributionApproximationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDistributionApproximationBudgetCertificate.certificateBudgetWindow ≤
      sampleDistributionApproximationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DistributionApproximationBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDistributionApproximationBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDistributionApproximationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.DistributionApproximation
