import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Weighted class schemas.

The finite schema tracks object count, total weight, and slack for
weighted symbolic classes.
-/

namespace AnalyticCombinatorics.PartA.Ch1.WeightedClassSchemas

structure WeightedClassData where
  objectCount : ℕ
  totalWeight : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def objectsNonempty (d : WeightedClassData) : Prop :=
  0 < d.objectCount

def weightControlled (d : WeightedClassData) : Prop :=
  d.totalWeight ≤ d.objectCount + d.slack

def weightedClassReady (d : WeightedClassData) : Prop :=
  objectsNonempty d ∧ weightControlled d

def weightedClassBudget (d : WeightedClassData) : ℕ :=
  d.objectCount + d.totalWeight + d.slack

theorem weightedClassReady.objects {d : WeightedClassData}
    (h : weightedClassReady d) :
    objectsNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem totalWeight_le_weightedBudget (d : WeightedClassData) :
    d.totalWeight ≤ weightedClassBudget d := by
  unfold weightedClassBudget
  omega

def sampleWeightedClassData : WeightedClassData :=
  { objectCount := 5, totalWeight := 8, slack := 3 }

example : weightedClassReady sampleWeightedClassData := by
  norm_num [weightedClassReady, objectsNonempty]
  norm_num [weightControlled, sampleWeightedClassData]

example : weightedClassBudget sampleWeightedClassData = 16 := by
  native_decide

structure WeightedClassWindow where
  objectCount : ℕ
  totalWeight : ℕ
  weightSlack : ℕ
  transformBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeightedClassWindow.weightControlled (w : WeightedClassWindow) : Prop :=
  w.totalWeight ≤ w.objectCount + w.weightSlack + w.slack

def WeightedClassWindow.transformControlled (w : WeightedClassWindow) : Prop :=
  w.transformBudget ≤ w.objectCount + w.totalWeight + w.weightSlack + w.slack

def weightedClassWindowReady (w : WeightedClassWindow) : Prop :=
  0 < w.objectCount ∧
    w.weightControlled ∧
    w.transformControlled

def WeightedClassWindow.certificate (w : WeightedClassWindow) : ℕ :=
  w.objectCount + w.totalWeight + w.weightSlack + w.slack

theorem weightedClass_transformBudget_le_certificate {w : WeightedClassWindow}
    (h : weightedClassWindowReady w) :
    w.transformBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransform⟩
  exact htransform

def sampleWeightedClassWindow : WeightedClassWindow :=
  { objectCount := 5, totalWeight := 8, weightSlack := 3, transformBudget := 15, slack := 0 }

example : weightedClassWindowReady sampleWeightedClassWindow := by
  norm_num [weightedClassWindowReady, WeightedClassWindow.weightControlled,
    WeightedClassWindow.transformControlled, sampleWeightedClassWindow]

example : sampleWeightedClassWindow.certificate = 16 := by
  native_decide


structure WeightedClassSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeightedClassSchemasBudgetCertificate.controlled
    (c : WeightedClassSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def WeightedClassSchemasBudgetCertificate.budgetControlled
    (c : WeightedClassSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def WeightedClassSchemasBudgetCertificate.Ready
    (c : WeightedClassSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WeightedClassSchemasBudgetCertificate.size
    (c : WeightedClassSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem weightedClassSchemas_budgetCertificate_le_size
    (c : WeightedClassSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWeightedClassSchemasBudgetCertificate :
    WeightedClassSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleWeightedClassSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [WeightedClassSchemasBudgetCertificate.controlled,
      sampleWeightedClassSchemasBudgetCertificate]
  · norm_num [WeightedClassSchemasBudgetCertificate.budgetControlled,
      sampleWeightedClassSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWeightedClassSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleWeightedClassSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleWeightedClassSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [WeightedClassSchemasBudgetCertificate.controlled,
      sampleWeightedClassSchemasBudgetCertificate]
  · norm_num [WeightedClassSchemasBudgetCertificate.budgetControlled,
      sampleWeightedClassSchemasBudgetCertificate]

example :
    sampleWeightedClassSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleWeightedClassSchemasBudgetCertificate.size := by
  apply weightedClassSchemas_budgetCertificate_le_size
  constructor
  · norm_num [WeightedClassSchemasBudgetCertificate.controlled,
      sampleWeightedClassSchemasBudgetCertificate]
  · norm_num [WeightedClassSchemasBudgetCertificate.budgetControlled,
      sampleWeightedClassSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List WeightedClassSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleWeightedClassSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleWeightedClassSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.WeightedClassSchemas
