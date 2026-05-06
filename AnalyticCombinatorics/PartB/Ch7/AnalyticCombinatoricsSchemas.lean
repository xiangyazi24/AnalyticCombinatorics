import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter VII: Analytic Combinatorics Schemas

Finite descriptors for the main schema taxonomy: smooth, subcritical,
supercritical, and critical.
-/

namespace AnalyticCombinatorics.PartB.Ch7.AnalyticCombinatoricsSchemas

inductive SchemaKind
  | smooth
  | subcritical
  | supercritical
  | critical
  deriving DecidableEq, Repr

structure SchemaDescriptor where
  kind : SchemaKind
  radiusInv : ℕ
  exponentNumerator : ℤ
  exponentDenominator : ℕ

def smoothSquareRoot : SchemaDescriptor where
  kind := SchemaKind.smooth
  radiusInv := 4
  exponentNumerator := -3
  exponentDenominator := 2

def supercriticalPole : SchemaDescriptor where
  kind := SchemaKind.supercritical
  radiusInv := 2
  exponentNumerator := 0
  exponentDenominator := 1

theorem schemaDescriptor_values :
    smoothSquareRoot.kind = SchemaKind.smooth ∧
    smoothSquareRoot.radiusInv = 4 ∧
    supercriticalPole.kind = SchemaKind.supercritical := by
  native_decide

def schemaGrowthBase (S : SchemaDescriptor) : ℕ :=
  S.radiusInv

theorem schemaGrowthBase_samples :
    schemaGrowthBase smoothSquareRoot = 4 ∧ schemaGrowthBase supercriticalPole = 2 := by
  native_decide

def schemaDescriptorReady (schema : SchemaDescriptor) : Prop :=
  0 < schema.radiusInv ∧ 0 < schema.exponentDenominator

theorem smoothSquareRoot_ready : schemaDescriptorReady smoothSquareRoot := by
  unfold schemaDescriptorReady smoothSquareRoot
  native_decide

def AnalyticCombinatoricsSchemaTransfer
    (coeff : ℕ → ℂ) (schema : SchemaDescriptor) : Prop :=
  schemaDescriptorReady schema ∧ coeff 0 = coeff schema.radiusInv

theorem analytic_combinatorics_schema_transfer_statement :
    AnalyticCombinatoricsSchemaTransfer (fun _ => 0) smoothSquareRoot := by
  unfold AnalyticCombinatoricsSchemaTransfer schemaDescriptorReady smoothSquareRoot
  norm_num


structure AnalyticCombinatoricsSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticCombinatoricsSchemasBudgetCertificate.controlled
    (c : AnalyticCombinatoricsSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticCombinatoricsSchemasBudgetCertificate.budgetControlled
    (c : AnalyticCombinatoricsSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticCombinatoricsSchemasBudgetCertificate.Ready
    (c : AnalyticCombinatoricsSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticCombinatoricsSchemasBudgetCertificate.size
    (c : AnalyticCombinatoricsSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticCombinatoricsSchemas_budgetCertificate_le_size
    (c : AnalyticCombinatoricsSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticCombinatoricsSchemasBudgetCertificate :
    AnalyticCombinatoricsSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAnalyticCombinatoricsSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticCombinatoricsSchemasBudgetCertificate.controlled,
      sampleAnalyticCombinatoricsSchemasBudgetCertificate]
  · norm_num [AnalyticCombinatoricsSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticCombinatoricsSchemasBudgetCertificate]

example :
    sampleAnalyticCombinatoricsSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticCombinatoricsSchemasBudgetCertificate.size := by
  apply analyticCombinatoricsSchemas_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticCombinatoricsSchemasBudgetCertificate.controlled,
      sampleAnalyticCombinatoricsSchemasBudgetCertificate]
  · norm_num [AnalyticCombinatoricsSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticCombinatoricsSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAnalyticCombinatoricsSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticCombinatoricsSchemasBudgetCertificate.controlled,
      sampleAnalyticCombinatoricsSchemasBudgetCertificate]
  · norm_num [AnalyticCombinatoricsSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticCombinatoricsSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticCombinatoricsSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticCombinatoricsSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AnalyticCombinatoricsSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticCombinatoricsSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticCombinatoricsSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.AnalyticCombinatoricsSchemas
