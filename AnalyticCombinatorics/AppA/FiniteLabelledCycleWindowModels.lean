import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite labelled cycle window models.

This module records finite bookkeeping for labelled cycle windows.
-/

namespace AnalyticCombinatorics.AppA.FiniteLabelledCycleWindowModels

structure LabelledCycleWindowData where
  labelCycles : ℕ
  rotationWindow : ℕ
  labelSlack : ℕ
deriving DecidableEq, Repr

def hasLabelCycles (d : LabelledCycleWindowData) : Prop :=
  0 < d.labelCycles

def rotationWindowControlled (d : LabelledCycleWindowData) : Prop :=
  d.rotationWindow ≤ d.labelCycles + d.labelSlack

def labelledCycleReady (d : LabelledCycleWindowData) : Prop :=
  hasLabelCycles d ∧ rotationWindowControlled d

def labelledCycleBudget (d : LabelledCycleWindowData) : ℕ :=
  d.labelCycles + d.rotationWindow + d.labelSlack

theorem labelledCycleReady.hasLabelCycles
    {d : LabelledCycleWindowData}
    (h : labelledCycleReady d) :
    hasLabelCycles d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem rotationWindow_le_budget (d : LabelledCycleWindowData) :
    d.rotationWindow ≤ labelledCycleBudget d := by
  unfold labelledCycleBudget
  omega

def sampleLabelledCycleWindowData : LabelledCycleWindowData :=
  { labelCycles := 6, rotationWindow := 8, labelSlack := 3 }

example : labelledCycleReady sampleLabelledCycleWindowData := by
  norm_num [labelledCycleReady, hasLabelCycles]
  norm_num [rotationWindowControlled, sampleLabelledCycleWindowData]

example : labelledCycleBudget sampleLabelledCycleWindowData = 17 := by
  native_decide

structure LabelledCycleCertificateWindow where
  labelCycles : ℕ
  rotationWindow : ℕ
  labelSlack : ℕ
  orbitBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledCycleCertificateWindow.rotationControlled
    (w : LabelledCycleCertificateWindow) : Prop :=
  w.rotationWindow ≤ w.labelCycles + w.labelSlack + w.slack

def LabelledCycleCertificateWindow.orbitControlled
    (w : LabelledCycleCertificateWindow) : Prop :=
  w.orbitBudget ≤ w.labelCycles + w.rotationWindow + w.labelSlack + w.slack

def labelledCycleCertificateReady (w : LabelledCycleCertificateWindow) : Prop :=
  0 < w.labelCycles ∧
    w.rotationControlled ∧
    w.orbitControlled

def LabelledCycleCertificateWindow.certificate (w : LabelledCycleCertificateWindow) : ℕ :=
  w.labelCycles + w.rotationWindow + w.labelSlack + w.slack

theorem labelledCycle_certificate_orbitBudget_le_certificate
    {w : LabelledCycleCertificateWindow}
    (h : labelledCycleCertificateReady w) :
    w.orbitBudget ≤ w.certificate := by
  rcases h with ⟨_, _, horbit⟩
  exact horbit

def sampleLabelledCycleCertificateWindow : LabelledCycleCertificateWindow :=
  { labelCycles := 6, rotationWindow := 8, labelSlack := 3, orbitBudget := 16, slack := 0 }

example : labelledCycleCertificateReady sampleLabelledCycleCertificateWindow := by
  norm_num [labelledCycleCertificateReady, LabelledCycleCertificateWindow.rotationControlled,
    LabelledCycleCertificateWindow.orbitControlled, sampleLabelledCycleCertificateWindow]

example : sampleLabelledCycleCertificateWindow.certificate = 17 := by
  native_decide


structure FiniteLabelledCycleWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteLabelledCycleWindowModelsBudgetCertificate.controlled
    (c : FiniteLabelledCycleWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteLabelledCycleWindowModelsBudgetCertificate.budgetControlled
    (c : FiniteLabelledCycleWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteLabelledCycleWindowModelsBudgetCertificate.Ready
    (c : FiniteLabelledCycleWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteLabelledCycleWindowModelsBudgetCertificate.size
    (c : FiniteLabelledCycleWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteLabelledCycleWindowModels_budgetCertificate_le_size
    (c : FiniteLabelledCycleWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteLabelledCycleWindowModelsBudgetCertificate :
    FiniteLabelledCycleWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteLabelledCycleWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLabelledCycleWindowModelsBudgetCertificate.controlled,
      sampleFiniteLabelledCycleWindowModelsBudgetCertificate]
  · norm_num [FiniteLabelledCycleWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelledCycleWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteLabelledCycleWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLabelledCycleWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteLabelledCycleWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLabelledCycleWindowModelsBudgetCertificate.controlled,
      sampleFiniteLabelledCycleWindowModelsBudgetCertificate]
  · norm_num [FiniteLabelledCycleWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelledCycleWindowModelsBudgetCertificate]

example :
    sampleFiniteLabelledCycleWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLabelledCycleWindowModelsBudgetCertificate.size := by
  apply finiteLabelledCycleWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteLabelledCycleWindowModelsBudgetCertificate.controlled,
      sampleFiniteLabelledCycleWindowModelsBudgetCertificate]
  · norm_num [FiniteLabelledCycleWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelledCycleWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteLabelledCycleWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteLabelledCycleWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteLabelledCycleWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteLabelledCycleWindowModels
