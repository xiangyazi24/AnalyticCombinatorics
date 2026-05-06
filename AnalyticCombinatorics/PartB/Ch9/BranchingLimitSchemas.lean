import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Branching Limit Schemas

Finite Galton-Watson offspring models and critical branching descriptors.
-/

namespace AnalyticCombinatorics.PartB.Ch9.BranchingLimitSchemas

structure OffspringLaw where
  weights : List ℚ

def totalMass (law : OffspringLaw) : ℚ :=
  law.weights.foldl (fun s x => s + x) 0

def mean (law : OffspringLaw) : ℚ :=
  (List.range law.weights.length).foldl
    (fun (s : ℚ) (k : ℕ) => s + (k : ℚ) * law.weights.getD k 0) 0

def binaryCriticalLaw : OffspringLaw where
  weights := [1 / 2, 0, 1 / 2]

theorem binaryCriticalLaw_moments :
    totalMass binaryCriticalLaw = 1 ∧ mean binaryCriticalLaw = 1 := by
  native_decide

def pgfCoeff (law : OffspringLaw) (n : ℕ) : ℚ :=
  law.weights.getD n 0

theorem pgfCoeff_binaryCritical :
    (List.range 4).map (pgfCoeff binaryCriticalLaw) = [1 / 2, 0, 1 / 2, 0] := by
  native_decide

structure BranchingLimitData where
  criticalMeanNumerator : ℕ
  criticalMeanDenominator : ℕ
  varianceNumerator : ℕ
  varianceDenominator : ℕ

def binaryBranchingLimitData : BranchingLimitData where
  criticalMeanNumerator := 1
  criticalMeanDenominator := 1
  varianceNumerator := 1
  varianceDenominator := 1

theorem binaryBranchingLimitData_values :
    binaryBranchingLimitData.criticalMeanNumerator = 1 ∧
    binaryBranchingLimitData.criticalMeanDenominator = 1 ∧
    binaryBranchingLimitData.varianceNumerator = 1 := by
  native_decide

def branchingLimitDataReady (data : BranchingLimitData) : Prop :=
  0 < data.criticalMeanDenominator ∧ 0 < data.varianceNumerator ∧
    0 < data.varianceDenominator

theorem binaryBranchingLimitData_ready :
    branchingLimitDataReady binaryBranchingLimitData := by
  unfold branchingLimitDataReady binaryBranchingLimitData
  native_decide

def CriticalBranchingLimit
    (law : OffspringLaw) (data : BranchingLimitData) : Prop :=
  branchingLimitDataReady data ∧ totalMass law = 1 ∧ mean law = 1

theorem critical_branching_limit_statement :
    CriticalBranchingLimit binaryCriticalLaw binaryBranchingLimitData := by
  unfold CriticalBranchingLimit branchingLimitDataReady binaryBranchingLimitData
  native_decide

/-- Finite executable readiness audit for branching limit descriptors. -/
def branchingLimitDataListReady
    (data : List BranchingLimitData) : Bool :=
  data.all fun d =>
    0 < d.criticalMeanDenominator &&
      0 < d.varianceNumerator &&
        0 < d.varianceDenominator

theorem branchingLimitDataList_readyWindow :
    branchingLimitDataListReady
      [{ criticalMeanNumerator := 1, criticalMeanDenominator := 1,
         varianceNumerator := 1, varianceDenominator := 1 },
       { criticalMeanNumerator := 2, criticalMeanDenominator := 2,
         varianceNumerator := 3, varianceDenominator := 4 }] = true := by
  unfold branchingLimitDataListReady
  native_decide

structure BranchingLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BranchingLimitSchemasBudgetCertificate.controlled
    (c : BranchingLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BranchingLimitSchemasBudgetCertificate.budgetControlled
    (c : BranchingLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BranchingLimitSchemasBudgetCertificate.Ready
    (c : BranchingLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BranchingLimitSchemasBudgetCertificate.size
    (c : BranchingLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem branchingLimitSchemas_budgetCertificate_le_size
    (c : BranchingLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBranchingLimitSchemasBudgetCertificate :
    BranchingLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleBranchingLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BranchingLimitSchemasBudgetCertificate.controlled,
      sampleBranchingLimitSchemasBudgetCertificate]
  · norm_num [BranchingLimitSchemasBudgetCertificate.budgetControlled,
      sampleBranchingLimitSchemasBudgetCertificate]

example :
    sampleBranchingLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBranchingLimitSchemasBudgetCertificate.size := by
  apply branchingLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [BranchingLimitSchemasBudgetCertificate.controlled,
      sampleBranchingLimitSchemasBudgetCertificate]
  · norm_num [BranchingLimitSchemasBudgetCertificate.budgetControlled,
      sampleBranchingLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBranchingLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BranchingLimitSchemasBudgetCertificate.controlled,
      sampleBranchingLimitSchemasBudgetCertificate]
  · norm_num [BranchingLimitSchemasBudgetCertificate.budgetControlled,
      sampleBranchingLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBranchingLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBranchingLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List BranchingLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBranchingLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleBranchingLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.BranchingLimitSchemas
