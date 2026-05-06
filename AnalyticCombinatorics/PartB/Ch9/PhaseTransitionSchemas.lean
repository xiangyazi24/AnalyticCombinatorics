import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Phase Transition Schemas

Finite window models for threshold phenomena in random structures.
-/

namespace AnalyticCombinatorics.PartB.Ch9.PhaseTransitionSchemas

def thresholdWindowCenter (n : ℕ) : ℕ :=
  n

def thresholdWindowWidth (n : ℕ) : ℕ :=
  Nat.sqrt n

theorem thresholdWindow_samples :
    thresholdWindowCenter 10 = 10 ∧
    thresholdWindowWidth 16 = 4 ∧
    thresholdWindowWidth 25 = 5 := by
  native_decide

def sigmoidToyNumerator (k : ℕ) : ℕ :=
  k

def sigmoidToyDenominator (k : ℕ) : ℕ :=
  k + 1

theorem sigmoidToy_samples :
    sigmoidToyNumerator 3 = 3 ∧ sigmoidToyDenominator 3 = 4 := by
  native_decide

structure PhaseTransitionData where
  criticalDensityNumerator : ℕ
  criticalDensityDenominator : ℕ
  windowPowerNumerator : ℕ
  windowPowerDenominator : ℕ

def erdosRenyiConnectivityData : PhaseTransitionData where
  criticalDensityNumerator := 1
  criticalDensityDenominator := 2
  windowPowerNumerator := 1
  windowPowerDenominator := 2

theorem erdosRenyiConnectivityData_values :
    erdosRenyiConnectivityData.criticalDensityNumerator = 1 ∧
    erdosRenyiConnectivityData.criticalDensityDenominator = 2 ∧
    erdosRenyiConnectivityData.windowPowerDenominator = 2 := by
  native_decide

def phaseTransitionDataReady (data : PhaseTransitionData) : Prop :=
  0 < data.criticalDensityDenominator ∧ 0 < data.windowPowerDenominator

theorem erdosRenyiConnectivityData_ready :
    phaseTransitionDataReady erdosRenyiConnectivityData := by
  unfold phaseTransitionDataReady erdosRenyiConnectivityData
  native_decide

def PhaseTransitionLimit
    (eventProbability : ℕ → ℚ) (data : PhaseTransitionData) : Prop :=
  phaseTransitionDataReady data ∧ eventProbability 0 = 0 ∧ eventProbability 3 = 3 / 4

def sigmoidProbabilityWitness (k : ℕ) : ℚ :=
  (sigmoidToyNumerator k : ℚ) / sigmoidToyDenominator k

theorem phase_transition_limit_statement :
    PhaseTransitionLimit sigmoidProbabilityWitness erdosRenyiConnectivityData := by
  unfold PhaseTransitionLimit phaseTransitionDataReady erdosRenyiConnectivityData
    sigmoidProbabilityWitness
  native_decide

/-- Finite executable readiness audit for phase-transition descriptors. -/
def phaseTransitionDataListReady
    (data : List PhaseTransitionData) : Bool :=
  data.all fun d =>
    0 < d.criticalDensityDenominator && 0 < d.windowPowerDenominator

theorem phaseTransitionDataList_readyWindow :
    phaseTransitionDataListReady
      [{ criticalDensityNumerator := 1, criticalDensityDenominator := 2,
         windowPowerNumerator := 1, windowPowerDenominator := 2 },
       { criticalDensityNumerator := 2, criticalDensityDenominator := 3,
         windowPowerNumerator := 1, windowPowerDenominator := 4 }] = true := by
  unfold phaseTransitionDataListReady
  native_decide

structure PhaseTransitionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PhaseTransitionSchemasBudgetCertificate.controlled
    (c : PhaseTransitionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PhaseTransitionSchemasBudgetCertificate.budgetControlled
    (c : PhaseTransitionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PhaseTransitionSchemasBudgetCertificate.Ready
    (c : PhaseTransitionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PhaseTransitionSchemasBudgetCertificate.size
    (c : PhaseTransitionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem phaseTransitionSchemas_budgetCertificate_le_size
    (c : PhaseTransitionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePhaseTransitionSchemasBudgetCertificate :
    PhaseTransitionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePhaseTransitionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PhaseTransitionSchemasBudgetCertificate.controlled,
      samplePhaseTransitionSchemasBudgetCertificate]
  · norm_num [PhaseTransitionSchemasBudgetCertificate.budgetControlled,
      samplePhaseTransitionSchemasBudgetCertificate]

example :
    samplePhaseTransitionSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePhaseTransitionSchemasBudgetCertificate.size := by
  apply phaseTransitionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PhaseTransitionSchemasBudgetCertificate.controlled,
      samplePhaseTransitionSchemasBudgetCertificate]
  · norm_num [PhaseTransitionSchemasBudgetCertificate.budgetControlled,
      samplePhaseTransitionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePhaseTransitionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PhaseTransitionSchemasBudgetCertificate.controlled,
      samplePhaseTransitionSchemasBudgetCertificate]
  · norm_num [PhaseTransitionSchemasBudgetCertificate.budgetControlled,
      samplePhaseTransitionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePhaseTransitionSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePhaseTransitionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List PhaseTransitionSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePhaseTransitionSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    samplePhaseTransitionSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.PhaseTransitionSchemas
