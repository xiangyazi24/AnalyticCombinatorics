import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Labelled set schemas.

The finite schema records label count, set component budget, and
selection slack.
-/

namespace AnalyticCombinatorics.PartA.Ch2.LabelledSetSchemas

structure LabelledSetData where
  labelCount : ℕ
  componentBudget : ℕ
  selectionSlack : ℕ
deriving DecidableEq, Repr

def labelCountPositive (d : LabelledSetData) : Prop :=
  0 < d.labelCount

def componentBudgetControlled (d : LabelledSetData) : Prop :=
  d.componentBudget ≤ d.labelCount + d.selectionSlack

def labelledSetReady (d : LabelledSetData) : Prop :=
  labelCountPositive d ∧ componentBudgetControlled d

def labelledSetBudget (d : LabelledSetData) : ℕ :=
  d.labelCount + d.componentBudget + d.selectionSlack

theorem labelledSetReady.labels {d : LabelledSetData}
    (h : labelledSetReady d) :
    labelCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem componentBudget_le_labelledSetBudget (d : LabelledSetData) :
    d.componentBudget ≤ labelledSetBudget d := by
  unfold labelledSetBudget
  omega

def sampleLabelledSetData : LabelledSetData :=
  { labelCount := 6, componentBudget := 8, selectionSlack := 3 }

example : labelledSetReady sampleLabelledSetData := by
  norm_num [labelledSetReady, labelCountPositive]
  norm_num [componentBudgetControlled, sampleLabelledSetData]

example : labelledSetBudget sampleLabelledSetData = 17 := by
  native_decide

structure LabelledSetWindow where
  labelCount : ℕ
  componentBudget : ℕ
  selectionSlack : ℕ
  setBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledSetWindow.componentControlled (w : LabelledSetWindow) : Prop :=
  w.componentBudget ≤ w.labelCount + w.selectionSlack + w.slack

def LabelledSetWindow.setControlled (w : LabelledSetWindow) : Prop :=
  w.setBudget ≤ w.labelCount + w.componentBudget + w.selectionSlack + w.slack

def labelledSetWindowReady (w : LabelledSetWindow) : Prop :=
  0 < w.labelCount ∧
    w.componentControlled ∧
    w.setControlled

def LabelledSetWindow.certificate (w : LabelledSetWindow) : ℕ :=
  w.labelCount + w.componentBudget + w.selectionSlack + w.slack

theorem labelledSet_setBudget_le_certificate {w : LabelledSetWindow}
    (h : labelledSetWindowReady w) :
    w.setBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hset⟩
  exact hset

def sampleLabelledSetWindow : LabelledSetWindow :=
  { labelCount := 6, componentBudget := 8, selectionSlack := 3, setBudget := 16, slack := 0 }

example : labelledSetWindowReady sampleLabelledSetWindow := by
  norm_num [labelledSetWindowReady, LabelledSetWindow.componentControlled,
    LabelledSetWindow.setControlled, sampleLabelledSetWindow]

example : sampleLabelledSetWindow.certificate = 17 := by
  native_decide


structure LabelledSetSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledSetSchemasBudgetCertificate.controlled
    (c : LabelledSetSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LabelledSetSchemasBudgetCertificate.budgetControlled
    (c : LabelledSetSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LabelledSetSchemasBudgetCertificate.Ready
    (c : LabelledSetSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LabelledSetSchemasBudgetCertificate.size
    (c : LabelledSetSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem labelledSetSchemas_budgetCertificate_le_size
    (c : LabelledSetSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLabelledSetSchemasBudgetCertificate :
    LabelledSetSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLabelledSetSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledSetSchemasBudgetCertificate.controlled,
      sampleLabelledSetSchemasBudgetCertificate]
  · norm_num [LabelledSetSchemasBudgetCertificate.budgetControlled,
      sampleLabelledSetSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLabelledSetSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledSetSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLabelledSetSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledSetSchemasBudgetCertificate.controlled,
      sampleLabelledSetSchemasBudgetCertificate]
  · norm_num [LabelledSetSchemasBudgetCertificate.budgetControlled,
      sampleLabelledSetSchemasBudgetCertificate]

example :
    sampleLabelledSetSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledSetSchemasBudgetCertificate.size := by
  apply labelledSetSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LabelledSetSchemasBudgetCertificate.controlled,
      sampleLabelledSetSchemasBudgetCertificate]
  · norm_num [LabelledSetSchemasBudgetCertificate.budgetControlled,
      sampleLabelledSetSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LabelledSetSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLabelledSetSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLabelledSetSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.LabelledSetSchemas
