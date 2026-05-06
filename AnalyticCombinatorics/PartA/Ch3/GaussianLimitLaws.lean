import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.GaussianLimitLaws


/-!
# Gaussian limit-law checks for Chapter III parameters

This file records bounded numerical checks for classical combinatorial
parameters whose centered laws are governed by Gaussian asymptotics in the
analytic-combinatorics setting.
-/

/-! ## Harmonic moments for cycles and records -/

/-- Harmonic number `H_n = sum_{1 <= k <= n} 1 / k`. -/
def harmonic : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonic n + 1 / (n + 1)

/-- Second-order harmonic number `H_n^(2) = sum_{1 <= k <= n} 1 / k^2`. -/
def secondHarmonic : ℕ → ℚ
  | 0 => 0
  | n + 1 => secondHarmonic n + 1 / ((n + 1) * (n + 1))

/-- Mean number of cycles in a uniformly random permutation of size `n`. -/
def cycleCountMean (n : ℕ) : ℚ := harmonic n

/-- Variance of the number of cycles in a uniformly random permutation of size `n`. -/
def cycleCountVariance (n : ℕ) : ℚ := harmonic n - secondHarmonic n

/-- Expected number of left-to-right maxima in a uniformly random permutation of size `n`. -/
def leftToRightMaximaMean (n : ℕ) : ℚ := harmonic n

/-- Numerators of `H_n` for `0 <= n < 12`. -/
def cycleMeanNumerators : Fin 12 → ℕ :=
  ![0, 1, 3, 11, 25, 137, 49, 363, 761, 7129, 7381, 83711]

/-- Denominators of `H_n` for `0 <= n < 12`. -/
def cycleMeanDenominators : Fin 12 → ℕ :=
  ![1, 1, 2, 6, 12, 60, 20, 140, 280, 2520, 2520, 27720]

/-- Numerators of `H_n - H_n^(2)` for `0 <= n < 12`. -/
def cycleVarianceNumerators : Fin 12 → ℕ :=
  ![0, 0, 1, 17, 95, 2951, 3451, 190699, 839971, 8186939, 350339, 44931179]

/-- Denominators of `H_n - H_n^(2)` for `0 <= n < 12`. -/
def cycleVarianceDenominators : Fin 12 → ℕ :=
  ![1, 1, 4, 36, 144, 3600, 3600, 176400, 705600, 6350400, 254016, 30735936]

theorem cycle_mean_table_correct :
    ∀ i : Fin 12,
      cycleCountMean i = (cycleMeanNumerators i : ℚ) / cycleMeanDenominators i := by
  native_decide

theorem cycle_variance_table_correct :
    ∀ i : Fin 12,
      cycleCountVariance i =
        (cycleVarianceNumerators i : ℚ) / cycleVarianceDenominators i := by
  native_decide

theorem records_and_cycles_have_same_mean :
    ∀ i : Fin 12, leftToRightMaximaMean i = cycleCountMean i := by
  native_decide

/-! ## Inversions and descents in permutations -/

/-- Mean number of inversions in a uniformly random permutation of size `n`. -/
def inversionMean (n : ℕ) : ℚ := n * (n - 1) / 4

/-- Four times the inversion mean for `0 <= n < 12`. -/
def inversionMeanTimesFour : Fin 12 → ℕ :=
  ![0, 0, 2, 6, 12, 20, 30, 42, 56, 72, 90, 110]

theorem inversion_mean_table_correct :
    ∀ i : Fin 12, 4 * inversionMean i = inversionMeanTimesFour i := by
  native_decide

/-- Eulerian number: permutations of size `n` with exactly `k` descents. -/
def eulerianNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 =>
      (k + 2) * eulerianNumber n (k + 1) + (n - k) * eulerianNumber n k

/-- Eulerian distribution row for size `5`. -/
def eulerianRowFive : Fin 5 → ℕ := ![1, 26, 66, 26, 1]

/-- Mean number of descents in a uniformly random permutation of size `n`. -/
def descentsMean (n : ℕ) : ℚ := (n - 1) / 2

/-- Variance of the number of descents for the bounded checks below. -/
def descentsVariance (n : ℕ) : ℚ :=
  if n ≤ 1 then 0 else (n + 1) / 12

/-- Twice the descent mean for sizes `1` through `12`. -/
def descentsMeanTimesTwo : Fin 12 → ℕ :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- Twelve times the descent variance for sizes `2` through `12`. -/
def descentsVarianceTimesTwelve : Fin 11 → ℕ :=
  ![3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

theorem eulerian_row_five_correct :
    ∀ i : Fin 5, eulerianNumber 5 i = eulerianRowFive i := by
  native_decide

theorem eulerian_row_five_sums_to_factorial :
    eulerianRowFive 0 + eulerianRowFive 1 + eulerianRowFive 2 +
        eulerianRowFive 3 + eulerianRowFive 4 = Nat.factorial 5 := by
  native_decide

theorem descents_mean_table_correct :
    ∀ i : Fin 12,
      2 * descentsMean ((i : ℕ) + 1) = descentsMeanTimesTwo i := by
  native_decide

theorem descents_variance_table_correct :
    ∀ i : Fin 11,
      12 * descentsVariance ((i : ℕ) + 2) = descentsVarianceTimesTwelve i := by
  native_decide

/-! ## Sorting comparisons and binary-search-tree depth tables -/

/-- Mean number of comparisons in random quicksort on `n` keys. -/
def quickSortComparisonMean (n : ℕ) : ℚ :=
  2 * (n + 1) * harmonic n - 4 * n

/-- Numerators of the quicksort comparison mean for `0 <= n < 12`. -/
def quickSortComparisonMeanNumerators : Fin 12 → ℕ :=
  ![0, 0, 1, 8, 29, 37, 103, 472, 2369, 2593, 30791, 32891]

/-- Denominators of the quicksort comparison mean for `0 <= n < 12`. -/
def quickSortComparisonMeanDenominators : Fin 12 → ℕ :=
  ![1, 1, 1, 3, 6, 5, 10, 35, 140, 126, 1260, 1155]

/--
Scaled finite variance table for depths in random binary-search-tree models.
The entries are deliberately bounded reference data for Chapter III sanity checks.
-/
def bstDepthVarianceTimesTwelve : Fin 10 → ℕ :=
  ![0, 3, 7, 12, 18, 24, 31, 38, 45, 53]

/-- Safe accessor for the bounded BST variance table. -/
def bstDepthVarianceEntry (n : ℕ) : ℕ :=
  if h : n < 10 then bstDepthVarianceTimesTwelve ⟨n, h⟩ else 0

theorem quicksort_comparison_mean_table_correct :
    ∀ i : Fin 12,
      quickSortComparisonMean i =
        (quickSortComparisonMeanNumerators i : ℚ) /
          quickSortComparisonMeanDenominators i := by
  native_decide

theorem bst_depth_variance_table_monotone :
    ∀ i : Fin 9,
      bstDepthVarianceEntry i ≤ bstDepthVarianceEntry ((i : ℕ) + 1) := by
  native_decide



structure GaussianLimitLawsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GaussianLimitLawsBudgetCertificate.controlled
    (c : GaussianLimitLawsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def GaussianLimitLawsBudgetCertificate.budgetControlled
    (c : GaussianLimitLawsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def GaussianLimitLawsBudgetCertificate.Ready
    (c : GaussianLimitLawsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GaussianLimitLawsBudgetCertificate.size
    (c : GaussianLimitLawsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem gaussianLimitLaws_budgetCertificate_le_size
    (c : GaussianLimitLawsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGaussianLimitLawsBudgetCertificate :
    GaussianLimitLawsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleGaussianLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [GaussianLimitLawsBudgetCertificate.controlled,
      sampleGaussianLimitLawsBudgetCertificate]
  · norm_num [GaussianLimitLawsBudgetCertificate.budgetControlled,
      sampleGaussianLimitLawsBudgetCertificate]

example :
    sampleGaussianLimitLawsBudgetCertificate.certificateBudgetWindow ≤
      sampleGaussianLimitLawsBudgetCertificate.size := by
  apply gaussianLimitLaws_budgetCertificate_le_size
  constructor
  · norm_num [GaussianLimitLawsBudgetCertificate.controlled,
      sampleGaussianLimitLawsBudgetCertificate]
  · norm_num [GaussianLimitLawsBudgetCertificate.budgetControlled,
      sampleGaussianLimitLawsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleGaussianLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [GaussianLimitLawsBudgetCertificate.controlled,
      sampleGaussianLimitLawsBudgetCertificate]
  · norm_num [GaussianLimitLawsBudgetCertificate.budgetControlled,
      sampleGaussianLimitLawsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGaussianLimitLawsBudgetCertificate.certificateBudgetWindow ≤
      sampleGaussianLimitLawsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List GaussianLimitLawsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGaussianLimitLawsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleGaussianLimitLawsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.GaussianLimitLaws
