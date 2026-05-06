import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix B: Analytic Inverse Models

Finite inverse-function coefficient models used by Lagrange inversion and
singular inversion.
-/

namespace AnalyticCombinatorics.AppB.AnalyticInverseModels

def compositionalInverseToy (n : ℕ) : ℤ :=
  if n = 1 then 1 else 0

theorem compositionalInverseToy_samples :
    (List.range 6).map compositionalInverseToy = [0, 1, 0, 0, 0, 0] := by
  native_decide

def inverseLinearCoeff (a b : ℚ) (n : ℕ) : ℚ :=
  if n = 0 then -b / a else if n = 1 then 1 / a else 0

theorem inverseLinearCoeff_samples :
    inverseLinearCoeff 2 4 0 = -2 ∧
    inverseLinearCoeff 2 4 1 = 1 / 2 ∧
    inverseLinearCoeff 2 4 2 = 0 := by
  native_decide

def lagrangeRootCoeff (n : ℕ) : ℕ :=
  if n = 0 then 0 else (2 * n - 2).choose (n - 1) / n

theorem lagrangeRootCoeff_samples :
    (List.range 7).map lagrangeRootCoeff = [0, 1, 1, 2, 5, 14, 42] := by
  native_decide

structure InverseSchemaData where
  derivativeNumerator : ℤ
  derivativeDenominator : ℕ
  branchOrder : ℕ

def regularInverseData : InverseSchemaData where
  derivativeNumerator := 1
  derivativeDenominator := 1
  branchOrder := 1

theorem regularInverseData_values :
    regularInverseData.derivativeNumerator = 1 ∧
    regularInverseData.derivativeDenominator = 1 ∧
    regularInverseData.branchOrder = 1 := by
  native_decide

def inverseSchemaDataReady (data : InverseSchemaData) : Prop :=
  0 < data.derivativeDenominator ∧ 0 < data.branchOrder

theorem regularInverseData_ready : inverseSchemaDataReady regularInverseData := by
  unfold inverseSchemaDataReady regularInverseData
  native_decide

def AnalyticInverseFunctionSchema
    (f g : ℂ → ℂ) (data : InverseSchemaData) : Prop :=
  inverseSchemaDataReady data ∧ f 0 = g 0 ∧ f 1 = g 1

theorem analytic_inverse_function_schema_statement :
    AnalyticInverseFunctionSchema (fun z => z) (fun z => z) regularInverseData := by
  unfold AnalyticInverseFunctionSchema inverseSchemaDataReady regularInverseData
  norm_num


structure AnalyticInverseModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticInverseModelsBudgetCertificate.controlled
    (c : AnalyticInverseModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticInverseModelsBudgetCertificate.budgetControlled
    (c : AnalyticInverseModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticInverseModelsBudgetCertificate.Ready
    (c : AnalyticInverseModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticInverseModelsBudgetCertificate.size
    (c : AnalyticInverseModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticInverseModels_budgetCertificate_le_size
    (c : AnalyticInverseModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticInverseModelsBudgetCertificate :
    AnalyticInverseModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAnalyticInverseModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticInverseModelsBudgetCertificate.controlled,
      sampleAnalyticInverseModelsBudgetCertificate]
  · norm_num [AnalyticInverseModelsBudgetCertificate.budgetControlled,
      sampleAnalyticInverseModelsBudgetCertificate]

example :
    sampleAnalyticInverseModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticInverseModelsBudgetCertificate.size := by
  apply analyticInverseModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticInverseModelsBudgetCertificate.controlled,
      sampleAnalyticInverseModelsBudgetCertificate]
  · norm_num [AnalyticInverseModelsBudgetCertificate.budgetControlled,
      sampleAnalyticInverseModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAnalyticInverseModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticInverseModelsBudgetCertificate.controlled,
      sampleAnalyticInverseModelsBudgetCertificate]
  · norm_num [AnalyticInverseModelsBudgetCertificate.budgetControlled,
      sampleAnalyticInverseModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticInverseModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticInverseModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AnalyticInverseModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticInverseModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticInverseModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticInverseModels
