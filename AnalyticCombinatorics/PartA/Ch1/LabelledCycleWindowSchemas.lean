import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Labelled cycle window schemas.

This module records finite bookkeeping for labelled cycle construction windows.
-/

namespace AnalyticCombinatorics.PartA.Ch1.LabelledCycleWindowSchemas

structure LabelledCycleWindowData where
  cycleLabels : ℕ
  rotationWindow : ℕ
  cycleSlack : ℕ
deriving DecidableEq, Repr

def hasCycleLabels (d : LabelledCycleWindowData) : Prop :=
  0 < d.cycleLabels

def rotationWindowControlled (d : LabelledCycleWindowData) : Prop :=
  d.rotationWindow ≤ d.cycleLabels + d.cycleSlack

def labelledCycleReady (d : LabelledCycleWindowData) : Prop :=
  hasCycleLabels d ∧ rotationWindowControlled d

def labelledCycleBudget (d : LabelledCycleWindowData) : ℕ :=
  d.cycleLabels + d.rotationWindow + d.cycleSlack

theorem labelledCycleReady.hasCycleLabels {d : LabelledCycleWindowData}
    (h : labelledCycleReady d) :
    hasCycleLabels d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem rotationWindow_le_budget (d : LabelledCycleWindowData) :
    d.rotationWindow ≤ labelledCycleBudget d := by
  unfold labelledCycleBudget
  omega

def sampleLabelledCycleWindowData : LabelledCycleWindowData :=
  { cycleLabels := 6, rotationWindow := 8, cycleSlack := 3 }

example : labelledCycleReady sampleLabelledCycleWindowData := by
  norm_num [labelledCycleReady, hasCycleLabels]
  norm_num [rotationWindowControlled, sampleLabelledCycleWindowData]

example : labelledCycleBudget sampleLabelledCycleWindowData = 17 := by
  native_decide

structure LabelledCycleCertificateWindow where
  cycleLabels : ℕ
  rotationWindow : ℕ
  cycleSlack : ℕ
  orbitBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledCycleCertificateWindow.rotationControlled
    (w : LabelledCycleCertificateWindow) : Prop :=
  w.rotationWindow ≤ w.cycleLabels + w.cycleSlack + w.slack

def LabelledCycleCertificateWindow.orbitControlled
    (w : LabelledCycleCertificateWindow) : Prop :=
  w.orbitBudget ≤ w.cycleLabels + w.rotationWindow + w.cycleSlack + w.slack

def labelledCycleWindowReady (w : LabelledCycleCertificateWindow) : Prop :=
  0 < w.cycleLabels ∧
    w.rotationControlled ∧
    w.orbitControlled

def LabelledCycleCertificateWindow.certificate (w : LabelledCycleCertificateWindow) : ℕ :=
  w.cycleLabels + w.rotationWindow + w.cycleSlack + w.slack

theorem labelledCycle_orbitBudget_le_certificate {w : LabelledCycleCertificateWindow}
    (h : labelledCycleWindowReady w) :
    w.orbitBudget ≤ w.certificate := by
  rcases h with ⟨_, _, horbit⟩
  exact horbit

def sampleLabelledCycleCertificateWindow : LabelledCycleCertificateWindow :=
  { cycleLabels := 6, rotationWindow := 8, cycleSlack := 3, orbitBudget := 16, slack := 0 }

example : labelledCycleWindowReady sampleLabelledCycleCertificateWindow := by
  norm_num [labelledCycleWindowReady, LabelledCycleCertificateWindow.rotationControlled,
    LabelledCycleCertificateWindow.orbitControlled, sampleLabelledCycleCertificateWindow]

example : sampleLabelledCycleCertificateWindow.certificate = 17 := by
  native_decide


structure LabelledCycleWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledCycleWindowSchemasBudgetCertificate.controlled
    (c : LabelledCycleWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LabelledCycleWindowSchemasBudgetCertificate.budgetControlled
    (c : LabelledCycleWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LabelledCycleWindowSchemasBudgetCertificate.Ready
    (c : LabelledCycleWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LabelledCycleWindowSchemasBudgetCertificate.size
    (c : LabelledCycleWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem labelledCycleWindowSchemas_budgetCertificate_le_size
    (c : LabelledCycleWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLabelledCycleWindowSchemasBudgetCertificate :
    LabelledCycleWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLabelledCycleWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledCycleWindowSchemasBudgetCertificate.controlled,
      sampleLabelledCycleWindowSchemasBudgetCertificate]
  · norm_num [LabelledCycleWindowSchemasBudgetCertificate.budgetControlled,
      sampleLabelledCycleWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLabelledCycleWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledCycleWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLabelledCycleWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledCycleWindowSchemasBudgetCertificate.controlled,
      sampleLabelledCycleWindowSchemasBudgetCertificate]
  · norm_num [LabelledCycleWindowSchemasBudgetCertificate.budgetControlled,
      sampleLabelledCycleWindowSchemasBudgetCertificate]

example :
    sampleLabelledCycleWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledCycleWindowSchemasBudgetCertificate.size := by
  apply labelledCycleWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LabelledCycleWindowSchemasBudgetCertificate.controlled,
      sampleLabelledCycleWindowSchemasBudgetCertificate]
  · norm_num [LabelledCycleWindowSchemasBudgetCertificate.budgetControlled,
      sampleLabelledCycleWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LabelledCycleWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLabelledCycleWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLabelledCycleWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.LabelledCycleWindowSchemas
