import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Labelled class schemas.
-/

namespace AnalyticCombinatorics.PartA.Ch2.LabelledClass

structure LabelledClassData where
  labels : ℕ
  structures : ℕ
  labelSlack : ℕ
deriving DecidableEq, Repr

def labelledReady (d : LabelledClassData) : Prop :=
  0 < d.labels ∧ d.structures ≤ d.labels + d.labelSlack

def labelledBudget (d : LabelledClassData) : ℕ :=
  d.labels + d.structures + d.labelSlack

theorem structures_le_budget (d : LabelledClassData) :
    d.structures ≤ labelledBudget d := by
  unfold labelledBudget
  omega

def sampleLabelledClassData : LabelledClassData :=
  { labels := 6, structures := 8, labelSlack := 3 }

example : labelledReady sampleLabelledClassData := by
  norm_num [labelledReady, sampleLabelledClassData]

example : labelledBudget sampleLabelledClassData = 17 := by native_decide

structure LabelledTransportWindow where
  sourceLabels : ℕ
  targetLabels : ℕ
  transportedStructures : ℕ
  relabelSlack : ℕ
deriving DecidableEq, Repr

def LabelledTransportWindow.sameCardinality (w : LabelledTransportWindow) : Prop :=
  w.sourceLabels = w.targetLabels

def LabelledTransportWindow.transportReady (w : LabelledTransportWindow) : Prop :=
  w.sameCardinality ∧ w.transportedStructures ≤ w.sourceLabels.factorial + w.relabelSlack

def LabelledTransportWindow.certificate (w : LabelledTransportWindow) : ℕ :=
  w.sourceLabels + w.targetLabels + w.transportedStructures + w.relabelSlack

theorem transportedStructures_le_certificate (w : LabelledTransportWindow) :
    w.transportedStructures ≤ w.certificate := by
  unfold LabelledTransportWindow.certificate
  omega

def sampleLabelledTransportWindow : LabelledTransportWindow :=
  { sourceLabels := 4, targetLabels := 4, transportedStructures := 18, relabelSlack := 6 }

example : sampleLabelledTransportWindow.transportReady := by
  norm_num [sampleLabelledTransportWindow, LabelledTransportWindow.transportReady,
    LabelledTransportWindow.sameCardinality]

example : sampleLabelledTransportWindow.certificate = 32 := by
  native_decide


structure LabelledClassBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledClassBudgetCertificate.controlled
    (c : LabelledClassBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LabelledClassBudgetCertificate.budgetControlled
    (c : LabelledClassBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LabelledClassBudgetCertificate.Ready
    (c : LabelledClassBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LabelledClassBudgetCertificate.size
    (c : LabelledClassBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem labelledClass_budgetCertificate_le_size
    (c : LabelledClassBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLabelledClassBudgetCertificate :
    LabelledClassBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLabelledClassBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledClassBudgetCertificate.controlled,
      sampleLabelledClassBudgetCertificate]
  · norm_num [LabelledClassBudgetCertificate.budgetControlled,
      sampleLabelledClassBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLabelledClassBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledClassBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLabelledClassBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledClassBudgetCertificate.controlled,
      sampleLabelledClassBudgetCertificate]
  · norm_num [LabelledClassBudgetCertificate.budgetControlled,
      sampleLabelledClassBudgetCertificate]

example :
    sampleLabelledClassBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledClassBudgetCertificate.size := by
  apply labelledClass_budgetCertificate_le_size
  constructor
  · norm_num [LabelledClassBudgetCertificate.controlled,
      sampleLabelledClassBudgetCertificate]
  · norm_num [LabelledClassBudgetCertificate.budgetControlled,
      sampleLabelledClassBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LabelledClassBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLabelledClassBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLabelledClassBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.LabelledClass
