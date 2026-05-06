import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch8.PoissonApproximation


open scoped BigOperators

/-!
Finite, decidable examples for Poisson approximation and rare events.

Probabilities are represented by integer tables, usually scaled by a
fixed denominator.  The tables are deliberately small: every index type
has size at most 12, and every verification is a closed computation.
-/

/-! ## Poisson probability tables -/

/-- `10^6 * e^{-1} / k!`, rounded to nearby integers for `k = 0..7`. -/
def poissonOneScaled : Fin 8 → Nat :=
  ![367879, 367879, 183940, 61313, 15328, 3066, 511, 73]

/-- `10^6 * e^{-2} * 2^k / k!`, rounded to nearby integers for `k = 0..9`. -/
def poissonTwoScaled : Fin 10 → Nat :=
  ![135335, 270671, 270671, 180447, 90224, 36089, 12030, 3437, 859, 191]

/-- `10^6 * e^{-3} * 3^k / k!`, rounded to nearby integers for `k = 0..11`. -/
def poissonThreeScaled : Fin 12 → Nat :=
  ![49787, 149361, 224042, 224042, 168031, 100819,
    50409, 21604, 8101, 2700, 810, 221]

theorem poisson_one_table_total_close :
    poissonOneScaled 0 + poissonOneScaled 1 + poissonOneScaled 2 + poissonOneScaled 3 +
      poissonOneScaled 4 + poissonOneScaled 5 + poissonOneScaled 6 + poissonOneScaled 7
        = 999989 := by
  native_decide

theorem poisson_one_mode_tie :
    poissonOneScaled 0 = poissonOneScaled 1 := by
  native_decide

theorem poisson_two_mode_tie :
    poissonTwoScaled 1 = poissonTwoScaled 2 := by
  native_decide

theorem poisson_three_mode_tie :
    poissonThreeScaled 2 = poissonThreeScaled 3 := by
  native_decide

theorem poisson_three_tail_is_small :
    poissonThreeScaled 9 + poissonThreeScaled 10 + poissonThreeScaled 11 < 4000 := by
  native_decide

/-! ## Binomial rare events and Poisson-binomial comparison -/

/-- Exact distribution of `Binomial(8, 1/8)`, scaled by `8^8`. -/
def binomialEightOneOverEightNumerator : Fin 9 → Nat :=
  ![5764801, 6588344, 3294172, 941192, 168070, 19208, 1372, 56, 1]

/-- Poisson(1) table scaled by `8^8`, rounded to nearby integers, for `k = 0..8`. -/
def poissonOneOnEightScale : Fin 9 → Nat :=
  ![6168103, 6168103, 3084052, 1028017, 257004, 51401, 8567, 1224, 153]

def absDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

def binomPoissonAbsDiff : Fin 9 → Nat :=
  ![403302, 420241, 210120, 86825, 88934, 32193, 7195, 1168, 152]

theorem binomial_rare_event_row_sum :
    binomialEightOneOverEightNumerator 0 + binomialEightOneOverEightNumerator 1 +
      binomialEightOneOverEightNumerator 2 + binomialEightOneOverEightNumerator 3 +
      binomialEightOneOverEightNumerator 4 + binomialEightOneOverEightNumerator 5 +
      binomialEightOneOverEightNumerator 6 + binomialEightOneOverEightNumerator 7 +
      binomialEightOneOverEightNumerator 8 = 8 ^ 8 := by
  native_decide

theorem binomial_poisson_difference_table :
    (fun k : Fin 9 =>
      absDiff (binomialEightOneOverEightNumerator k) (poissonOneOnEightScale k))
        = binomPoissonAbsDiff := by
  native_decide

theorem binomial_poisson_largest_error_at_one :
    ∀ k : Fin 9, binomPoissonAbsDiff k ≤ binomPoissonAbsDiff 1 := by
  native_decide

theorem binomial_poisson_tail_error_bound :
    binomPoissonAbsDiff 5 + binomPoissonAbsDiff 6 +
      binomPoissonAbsDiff 7 + binomPoissonAbsDiff 8 < 41000 := by
  native_decide

/-! ## Occupancy: empty bins among `m` balls and `n` bins -/

/-- Number of allocations of `m` labelled balls into `n` labelled bins with exactly
    `j` empty bins. -/
def occupancyEmptyCount (m n j : Nat) : Nat :=
  Nat.choose n j *
    (∑ i ∈ Finset.range (n - j + 1),
      (-1 : Int) ^ i * Nat.choose (n - j) i * ((n - j - i) ^ m : Nat)).natAbs

/-- Empty-bin counts for `m = 4`, `n = 4`, indexed by `j = 0..4`. -/
def occupancyFourBallsFourBins : Fin 5 → Nat :=
  ![24, 144, 84, 4, 0]

/-- Empty-bin counts for `m = 5`, `n = 5`, indexed by `j = 0..5`. -/
def occupancyFiveBallsFiveBins : Fin 6 → Nat :=
  ![120, 1200, 1500, 300, 5, 0]

theorem occupancy_four_table_matches_formula :
    (fun j : Fin 5 => occupancyEmptyCount 4 4 j.val) = occupancyFourBallsFourBins := by
  native_decide

theorem occupancy_four_total :
    occupancyFourBallsFourBins 0 + occupancyFourBallsFourBins 1 +
      occupancyFourBallsFourBins 2 + occupancyFourBallsFourBins 3 +
      occupancyFourBallsFourBins 4 = 4 ^ 4 := by
  native_decide

theorem occupancy_five_table_matches_formula :
    (fun j : Fin 6 => occupancyEmptyCount 5 5 j.val) = occupancyFiveBallsFiveBins := by
  native_decide

theorem occupancy_five_total :
    occupancyFiveBallsFiveBins 0 + occupancyFiveBallsFiveBins 1 +
      occupancyFiveBallsFiveBins 2 + occupancyFiveBallsFiveBins 3 +
      occupancyFiveBallsFiveBins 4 + occupancyFiveBallsFiveBins 5 = 5 ^ 5 := by
  native_decide

/-! ## Matching problem and fixed-point counts -/

/-- Derangement numbers `!n` for `n = 0..8`. -/
def derangementTable : Fin 9 → Nat :=
  ![1, 0, 1, 2, 9, 44, 265, 1854, 14833]

def derangementSmall (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 9
  | 5 => 44
  | 6 => 265
  | 7 => 1854
  | 8 => 14833
  | _ => 0

/-- Number of permutations of `n` letters with exactly `k` fixed points. -/
def permutationsWithFixedPoints (n k : Nat) : Nat :=
  Nat.choose n k * derangementSmall (n - k)

/-- Fixed-point count distribution for permutations of `6` letters, indexed by `k = 0..6`. -/
def fixedPointCountSix : Fin 7 → Nat :=
  ![265, 264, 135, 40, 15, 0, 1]

theorem derangement_recurrence_small :
    derangementTable 8 =
      7 * (derangementTable 7 + derangementTable 6) := by
  native_decide

theorem fixed_point_table_six :
    (fun k : Fin 7 => permutationsWithFixedPoints 6 k.val) = fixedPointCountSix := by
  native_decide

theorem fixed_point_distribution_total_six :
    fixedPointCountSix 0 + fixedPointCountSix 1 + fixedPointCountSix 2 +
      fixedPointCountSix 3 + fixedPointCountSix 4 + fixedPointCountSix 5 +
      fixedPointCountSix 6 = Nat.factorial 6 := by
  native_decide

theorem matching_zero_and_one_fixed_are_close :
    absDiff (fixedPointCountSix 0) (fixedPointCountSix 1) = 1 := by
  native_decide

/-! ## Stein-Chen style bounded dependency witnesses -/

/-- A small table of dependency degrees for rare events. -/
def dependencyDegree : Fin 6 → Nat :=
  ![0, 1, 1, 2, 2, 3]

/-- A small table of event weights scaled by `1000`. -/
def rareEventWeight : Fin 6 → Nat :=
  ![30, 25, 25, 12, 12, 6]

def steinChenLocalCost (i : Fin 6) : Nat :=
  rareEventWeight i * (dependencyDegree i + 1)

def steinChenLocalCostTable : Fin 6 → Nat :=
  ![30, 50, 50, 36, 36, 24]

theorem stein_chen_local_costs :
    (fun i : Fin 6 => steinChenLocalCost i) = steinChenLocalCostTable := by
  native_decide

theorem stein_chen_total_cost_bound :
    steinChenLocalCostTable 0 + steinChenLocalCostTable 1 +
      steinChenLocalCostTable 2 + steinChenLocalCostTable 3 +
      steinChenLocalCostTable 4 + steinChenLocalCostTable 5 ≤ 226 := by
  native_decide

theorem stein_chen_total_intensity :
    rareEventWeight 0 + rareEventWeight 1 + rareEventWeight 2 +
      rareEventWeight 3 + rareEventWeight 4 + rareEventWeight 5 = 110 := by
  native_decide



structure PoissonApproximationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonApproximationBudgetCertificate.controlled
    (c : PoissonApproximationBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PoissonApproximationBudgetCertificate.budgetControlled
    (c : PoissonApproximationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PoissonApproximationBudgetCertificate.Ready
    (c : PoissonApproximationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PoissonApproximationBudgetCertificate.size
    (c : PoissonApproximationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem poissonApproximation_budgetCertificate_le_size
    (c : PoissonApproximationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePoissonApproximationBudgetCertificate :
    PoissonApproximationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePoissonApproximationBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonApproximationBudgetCertificate.controlled,
      samplePoissonApproximationBudgetCertificate]
  · norm_num [PoissonApproximationBudgetCertificate.budgetControlled,
      samplePoissonApproximationBudgetCertificate]

example :
    samplePoissonApproximationBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonApproximationBudgetCertificate.size := by
  apply poissonApproximation_budgetCertificate_le_size
  constructor
  · norm_num [PoissonApproximationBudgetCertificate.controlled,
      samplePoissonApproximationBudgetCertificate]
  · norm_num [PoissonApproximationBudgetCertificate.budgetControlled,
      samplePoissonApproximationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePoissonApproximationBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonApproximationBudgetCertificate.controlled,
      samplePoissonApproximationBudgetCertificate]
  · norm_num [PoissonApproximationBudgetCertificate.budgetControlled,
      samplePoissonApproximationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePoissonApproximationBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonApproximationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PoissonApproximationBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePoissonApproximationBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePoissonApproximationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.PoissonApproximation
