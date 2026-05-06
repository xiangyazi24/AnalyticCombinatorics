import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite labelled sequence window models.

This module records finite bookkeeping for labelled sequence windows.
-/

namespace AnalyticCombinatorics.AppA.FiniteLabelledSequenceWindowModels

structure LabelledSequenceWindowData where
  labelSlots : ℕ
  sequenceWindow : ℕ
  labelSlack : ℕ
deriving DecidableEq, Repr

def hasLabelSlots (d : LabelledSequenceWindowData) : Prop :=
  0 < d.labelSlots

def sequenceWindowControlled (d : LabelledSequenceWindowData) : Prop :=
  d.sequenceWindow ≤ d.labelSlots + d.labelSlack

def labelledSequenceReady (d : LabelledSequenceWindowData) : Prop :=
  hasLabelSlots d ∧ sequenceWindowControlled d

def labelledSequenceBudget (d : LabelledSequenceWindowData) : ℕ :=
  d.labelSlots + d.sequenceWindow + d.labelSlack

theorem labelledSequenceReady.hasLabelSlots
    {d : LabelledSequenceWindowData}
    (h : labelledSequenceReady d) :
    hasLabelSlots d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem sequenceWindow_le_budget (d : LabelledSequenceWindowData) :
    d.sequenceWindow ≤ labelledSequenceBudget d := by
  unfold labelledSequenceBudget
  omega

def sampleLabelledSequenceWindowData : LabelledSequenceWindowData :=
  { labelSlots := 6, sequenceWindow := 8, labelSlack := 3 }

example : labelledSequenceReady sampleLabelledSequenceWindowData := by
  norm_num [labelledSequenceReady, hasLabelSlots]
  norm_num [sequenceWindowControlled, sampleLabelledSequenceWindowData]

example : labelledSequenceBudget sampleLabelledSequenceWindowData = 17 := by
  native_decide

structure LabelledSequenceCertificateWindow where
  labelSlots : ℕ
  sequenceWindow : ℕ
  labelSlack : ℕ
  sequenceBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledSequenceCertificateWindow.windowControlled
    (w : LabelledSequenceCertificateWindow) : Prop :=
  w.sequenceWindow ≤ w.labelSlots + w.labelSlack + w.slack

def LabelledSequenceCertificateWindow.sequenceControlled
    (w : LabelledSequenceCertificateWindow) : Prop :=
  w.sequenceBudget ≤ w.labelSlots + w.sequenceWindow + w.labelSlack + w.slack

def labelledSequenceCertificateReady (w : LabelledSequenceCertificateWindow) : Prop :=
  0 < w.labelSlots ∧
    w.windowControlled ∧
    w.sequenceControlled

def LabelledSequenceCertificateWindow.certificate (w : LabelledSequenceCertificateWindow) : ℕ :=
  w.labelSlots + w.sequenceWindow + w.labelSlack + w.slack

theorem labelledSequence_sequenceBudget_le_certificate {w : LabelledSequenceCertificateWindow}
    (h : labelledSequenceCertificateReady w) :
    w.sequenceBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hsequence⟩
  exact hsequence

def sampleLabelledSequenceCertificateWindow : LabelledSequenceCertificateWindow :=
  { labelSlots := 6, sequenceWindow := 8, labelSlack := 3, sequenceBudget := 16, slack := 0 }

example : labelledSequenceCertificateReady sampleLabelledSequenceCertificateWindow := by
  norm_num [labelledSequenceCertificateReady, LabelledSequenceCertificateWindow.windowControlled,
    LabelledSequenceCertificateWindow.sequenceControlled, sampleLabelledSequenceCertificateWindow]

example : sampleLabelledSequenceCertificateWindow.certificate = 17 := by
  native_decide


structure FiniteLabelledSequenceWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteLabelledSequenceWindowModelsBudgetCertificate.controlled
    (c : FiniteLabelledSequenceWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteLabelledSequenceWindowModelsBudgetCertificate.budgetControlled
    (c : FiniteLabelledSequenceWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteLabelledSequenceWindowModelsBudgetCertificate.Ready
    (c : FiniteLabelledSequenceWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteLabelledSequenceWindowModelsBudgetCertificate.size
    (c : FiniteLabelledSequenceWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteLabelledSequenceWindowModels_budgetCertificate_le_size
    (c : FiniteLabelledSequenceWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteLabelledSequenceWindowModelsBudgetCertificate :
    FiniteLabelledSequenceWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteLabelledSequenceWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLabelledSequenceWindowModelsBudgetCertificate.controlled,
      sampleFiniteLabelledSequenceWindowModelsBudgetCertificate]
  · norm_num [FiniteLabelledSequenceWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelledSequenceWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteLabelledSequenceWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLabelledSequenceWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteLabelledSequenceWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLabelledSequenceWindowModelsBudgetCertificate.controlled,
      sampleFiniteLabelledSequenceWindowModelsBudgetCertificate]
  · norm_num [FiniteLabelledSequenceWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelledSequenceWindowModelsBudgetCertificate]

example :
    sampleFiniteLabelledSequenceWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLabelledSequenceWindowModelsBudgetCertificate.size := by
  apply finiteLabelledSequenceWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteLabelledSequenceWindowModelsBudgetCertificate.controlled,
      sampleFiniteLabelledSequenceWindowModelsBudgetCertificate]
  · norm_num [FiniteLabelledSequenceWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelledSequenceWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteLabelledSequenceWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteLabelledSequenceWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteLabelledSequenceWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteLabelledSequenceWindowModels
