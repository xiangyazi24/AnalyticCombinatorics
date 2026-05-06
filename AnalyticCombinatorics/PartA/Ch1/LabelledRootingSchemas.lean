import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Labelled rooting schemas.

This module records finite bookkeeping for labelled rooting operations.
-/

namespace AnalyticCombinatorics.PartA.Ch1.LabelledRootingSchemas

structure LabelledRootingData where
  labelSites : ℕ
  rootChoices : ℕ
  rootingSlack : ℕ
deriving DecidableEq, Repr

def hasLabelSites (d : LabelledRootingData) : Prop :=
  0 < d.labelSites

def rootChoicesControlled (d : LabelledRootingData) : Prop :=
  d.rootChoices ≤ d.labelSites + d.rootingSlack

def labelledRootingReady (d : LabelledRootingData) : Prop :=
  hasLabelSites d ∧ rootChoicesControlled d

def labelledRootingBudget (d : LabelledRootingData) : ℕ :=
  d.labelSites + d.rootChoices + d.rootingSlack

theorem labelledRootingReady.hasLabelSites {d : LabelledRootingData}
    (h : labelledRootingReady d) :
    hasLabelSites d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem rootChoices_le_budget (d : LabelledRootingData) :
    d.rootChoices ≤ labelledRootingBudget d := by
  unfold labelledRootingBudget
  omega

def sampleLabelledRootingData : LabelledRootingData :=
  { labelSites := 6, rootChoices := 8, rootingSlack := 3 }

example : labelledRootingReady sampleLabelledRootingData := by
  norm_num [labelledRootingReady, hasLabelSites]
  norm_num [rootChoicesControlled, sampleLabelledRootingData]

example : labelledRootingBudget sampleLabelledRootingData = 17 := by
  native_decide

structure LabelledRootingWindow where
  labelSites : ℕ
  rootChoices : ℕ
  rootingSlack : ℕ
  relabelBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledRootingWindow.rootChoicesControlled (w : LabelledRootingWindow) : Prop :=
  w.rootChoices ≤ w.labelSites + w.rootingSlack + w.slack

def LabelledRootingWindow.relabelControlled (w : LabelledRootingWindow) : Prop :=
  w.relabelBudget ≤ w.labelSites + w.rootChoices + w.rootingSlack + w.slack

def labelledRootingWindowReady (w : LabelledRootingWindow) : Prop :=
  0 < w.labelSites ∧
    w.rootChoicesControlled ∧
    w.relabelControlled

def LabelledRootingWindow.certificate (w : LabelledRootingWindow) : ℕ :=
  w.labelSites + w.rootChoices + w.rootingSlack + w.slack

theorem labelledRooting_relabelBudget_le_certificate {w : LabelledRootingWindow}
    (h : labelledRootingWindowReady w) :
    w.relabelBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hrelabel⟩
  exact hrelabel

def sampleLabelledRootingWindow : LabelledRootingWindow :=
  { labelSites := 6, rootChoices := 8, rootingSlack := 3, relabelBudget := 16, slack := 0 }

example : labelledRootingWindowReady sampleLabelledRootingWindow := by
  norm_num [labelledRootingWindowReady, LabelledRootingWindow.rootChoicesControlled,
    LabelledRootingWindow.relabelControlled, sampleLabelledRootingWindow]

example : sampleLabelledRootingWindow.certificate = 17 := by
  native_decide


structure LabelledRootingSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledRootingSchemasBudgetCertificate.controlled
    (c : LabelledRootingSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LabelledRootingSchemasBudgetCertificate.budgetControlled
    (c : LabelledRootingSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LabelledRootingSchemasBudgetCertificate.Ready
    (c : LabelledRootingSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LabelledRootingSchemasBudgetCertificate.size
    (c : LabelledRootingSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem labelledRootingSchemas_budgetCertificate_le_size
    (c : LabelledRootingSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLabelledRootingSchemasBudgetCertificate :
    LabelledRootingSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLabelledRootingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledRootingSchemasBudgetCertificate.controlled,
      sampleLabelledRootingSchemasBudgetCertificate]
  · norm_num [LabelledRootingSchemasBudgetCertificate.budgetControlled,
      sampleLabelledRootingSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLabelledRootingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledRootingSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLabelledRootingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledRootingSchemasBudgetCertificate.controlled,
      sampleLabelledRootingSchemasBudgetCertificate]
  · norm_num [LabelledRootingSchemasBudgetCertificate.budgetControlled,
      sampleLabelledRootingSchemasBudgetCertificate]

example :
    sampleLabelledRootingSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledRootingSchemasBudgetCertificate.size := by
  apply labelledRootingSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LabelledRootingSchemasBudgetCertificate.controlled,
      sampleLabelledRootingSchemasBudgetCertificate]
  · norm_num [LabelledRootingSchemasBudgetCertificate.budgetControlled,
      sampleLabelledRootingSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LabelledRootingSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLabelledRootingSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLabelledRootingSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.LabelledRootingSchemas
