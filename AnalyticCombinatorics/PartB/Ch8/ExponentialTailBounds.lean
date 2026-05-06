import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch8.ExponentialTailBounds


def binomialCramerRateScaled : Fin 9 → ℕ := ![5545, 2617, 1046, 177, 0, 177, 1046, 2617, 5545]

def momentGeneratingScaled : Fin 7 → ℕ := ![37, 61, 100, 165, 272, 448, 739]

def cumulantGeneratingScaled : Fin 7 → ℕ := ![0, 12, 50, 113, 200, 313, 450]

def tiltedSuccessPermille : Fin 7 → ℕ := ![119, 182, 269, 378, 500, 622, 731]

def empiricalProcessBoundPermillion : Fin 12 → ℕ :=
  ![1000000, 500000, 250000, 125000, 62500, 31250, 15625, 7812, 3906, 1953, 976, 488]

def entropyDefectScaled : Fin 9 → ℕ := ![1000, 544, 189, 31, 0, 31, 189, 544, 1000]

def chernoffExponentScaled : Fin 8 → ℕ := ![0, 2, 8, 18, 32, 50, 72, 98]

theorem binomial_cramer_rate_symmetric :
    binomialCramerRateScaled 0 = binomialCramerRateScaled 8 ∧
      binomialCramerRateScaled 1 = binomialCramerRateScaled 7 ∧
      binomialCramerRateScaled 2 = binomialCramerRateScaled 6 ∧
      binomialCramerRateScaled 3 = binomialCramerRateScaled 5 ∧
      binomialCramerRateScaled 4 = 0 := by
  native_decide

theorem moment_generating_values_increase :
    momentGeneratingScaled 0 < momentGeneratingScaled 1 ∧
      momentGeneratingScaled 1 < momentGeneratingScaled 2 ∧
      momentGeneratingScaled 2 < momentGeneratingScaled 3 ∧
      momentGeneratingScaled 3 < momentGeneratingScaled 4 ∧
      momentGeneratingScaled 4 < momentGeneratingScaled 5 ∧
      momentGeneratingScaled 5 < momentGeneratingScaled 6 := by
  native_decide

theorem cumulant_generating_discrete_convex :
    cumulantGeneratingScaled 0 + cumulantGeneratingScaled 2 ≥ 2 * cumulantGeneratingScaled 1 ∧
      cumulantGeneratingScaled 1 + cumulantGeneratingScaled 3 ≥ 2 * cumulantGeneratingScaled 2 ∧
      cumulantGeneratingScaled 2 + cumulantGeneratingScaled 4 ≥ 2 * cumulantGeneratingScaled 3 ∧
      cumulantGeneratingScaled 3 + cumulantGeneratingScaled 5 ≥ 2 * cumulantGeneratingScaled 4 ∧
      cumulantGeneratingScaled 4 + cumulantGeneratingScaled 6 ≥ 2 * cumulantGeneratingScaled 5 := by
  native_decide

theorem tilted_parameters_cross_half :
    tiltedSuccessPermille 0 < 500 ∧
      tiltedSuccessPermille 1 < 500 ∧
      tiltedSuccessPermille 2 < 500 ∧
      tiltedSuccessPermille 3 < 500 ∧
      tiltedSuccessPermille 4 = 500 ∧
      500 < tiltedSuccessPermille 5 ∧
      500 < tiltedSuccessPermille 6 := by
  native_decide

theorem empirical_process_bounds_decrease :
    empiricalProcessBoundPermillion 0 ≥ 2 * empiricalProcessBoundPermillion 1 ∧
      empiricalProcessBoundPermillion 1 ≥ 2 * empiricalProcessBoundPermillion 2 ∧
      empiricalProcessBoundPermillion 2 ≥ 2 * empiricalProcessBoundPermillion 3 ∧
      empiricalProcessBoundPermillion 3 ≥ 2 * empiricalProcessBoundPermillion 4 ∧
      empiricalProcessBoundPermillion 4 ≥ 2 * empiricalProcessBoundPermillion 5 ∧
      empiricalProcessBoundPermillion 5 ≥ 2 * empiricalProcessBoundPermillion 6 ∧
      empiricalProcessBoundPermillion 6 ≥ 2 * empiricalProcessBoundPermillion 7 ∧
      empiricalProcessBoundPermillion 7 ≥ 2 * empiricalProcessBoundPermillion 8 ∧
      empiricalProcessBoundPermillion 8 ≥ 2 * empiricalProcessBoundPermillion 9 ∧
      empiricalProcessBoundPermillion 9 ≥ 2 * empiricalProcessBoundPermillion 10 ∧
      empiricalProcessBoundPermillion 10 ≥ 2 * empiricalProcessBoundPermillion 11 := by
  native_decide

theorem entropy_defect_symmetric_and_centered :
    entropyDefectScaled 0 = entropyDefectScaled 8 ∧
      entropyDefectScaled 1 = entropyDefectScaled 7 ∧
      entropyDefectScaled 2 = entropyDefectScaled 6 ∧
      entropyDefectScaled 3 = entropyDefectScaled 5 ∧
      entropyDefectScaled 4 = 0 ∧
      entropyDefectScaled 3 < entropyDefectScaled 2 ∧
      entropyDefectScaled 2 < entropyDefectScaled 1 ∧
      entropyDefectScaled 1 < entropyDefectScaled 0 := by
  native_decide

theorem chernoff_exponent_quadratic_grid :
    chernoffExponentScaled 0 = 0 ∧
      chernoffExponentScaled 1 = 2 ∧
      chernoffExponentScaled 2 = 8 ∧
      chernoffExponentScaled 3 = 18 ∧
      chernoffExponentScaled 4 = 32 ∧
      chernoffExponentScaled 5 = 50 ∧
      chernoffExponentScaled 6 = 72 ∧
      chernoffExponentScaled 7 = 98 := by
  native_decide



structure ExponentialTailBoundsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExponentialTailBoundsBudgetCertificate.controlled
    (c : ExponentialTailBoundsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ExponentialTailBoundsBudgetCertificate.budgetControlled
    (c : ExponentialTailBoundsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ExponentialTailBoundsBudgetCertificate.Ready
    (c : ExponentialTailBoundsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ExponentialTailBoundsBudgetCertificate.size
    (c : ExponentialTailBoundsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem exponentialTailBounds_budgetCertificate_le_size
    (c : ExponentialTailBoundsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleExponentialTailBoundsBudgetCertificate :
    ExponentialTailBoundsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleExponentialTailBoundsBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialTailBoundsBudgetCertificate.controlled,
      sampleExponentialTailBoundsBudgetCertificate]
  · norm_num [ExponentialTailBoundsBudgetCertificate.budgetControlled,
      sampleExponentialTailBoundsBudgetCertificate]

example :
    sampleExponentialTailBoundsBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialTailBoundsBudgetCertificate.size := by
  apply exponentialTailBounds_budgetCertificate_le_size
  constructor
  · norm_num [ExponentialTailBoundsBudgetCertificate.controlled,
      sampleExponentialTailBoundsBudgetCertificate]
  · norm_num [ExponentialTailBoundsBudgetCertificate.budgetControlled,
      sampleExponentialTailBoundsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleExponentialTailBoundsBudgetCertificate.Ready := by
  constructor
  · norm_num [ExponentialTailBoundsBudgetCertificate.controlled,
      sampleExponentialTailBoundsBudgetCertificate]
  · norm_num [ExponentialTailBoundsBudgetCertificate.budgetControlled,
      sampleExponentialTailBoundsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleExponentialTailBoundsBudgetCertificate.certificateBudgetWindow ≤
      sampleExponentialTailBoundsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ExponentialTailBoundsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleExponentialTailBoundsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleExponentialTailBoundsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.ExponentialTailBounds
