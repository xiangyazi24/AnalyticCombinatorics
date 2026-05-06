import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite marked sequence models.

This module records finite bookkeeping for marked sequence constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteMarkedSequenceModels

structure MarkedSequenceData where
  sequenceLength : ℕ
  markWindow : ℕ
  markingSlack : ℕ
deriving DecidableEq, Repr

def hasSequenceLength (d : MarkedSequenceData) : Prop :=
  0 < d.sequenceLength

def markWindowControlled (d : MarkedSequenceData) : Prop :=
  d.markWindow ≤ d.sequenceLength + d.markingSlack

def markedSequenceReady (d : MarkedSequenceData) : Prop :=
  hasSequenceLength d ∧ markWindowControlled d

def markedSequenceBudget (d : MarkedSequenceData) : ℕ :=
  d.sequenceLength + d.markWindow + d.markingSlack

theorem markedSequenceReady.hasSequenceLength {d : MarkedSequenceData}
    (h : markedSequenceReady d) :
    hasSequenceLength d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem markWindow_le_budget (d : MarkedSequenceData) :
    d.markWindow ≤ markedSequenceBudget d := by
  unfold markedSequenceBudget
  omega

def sampleMarkedSequenceData : MarkedSequenceData :=
  { sequenceLength := 7, markWindow := 9, markingSlack := 3 }

example : markedSequenceReady sampleMarkedSequenceData := by
  norm_num [markedSequenceReady, hasSequenceLength]
  norm_num [markWindowControlled, sampleMarkedSequenceData]

example : markedSequenceBudget sampleMarkedSequenceData = 19 := by
  native_decide

structure MarkedSequenceWindow where
  sequenceLength : ℕ
  markWindow : ℕ
  markingSlack : ℕ
  transferBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MarkedSequenceWindow.markWindowControlled (w : MarkedSequenceWindow) : Prop :=
  w.markWindow ≤ w.sequenceLength + w.markingSlack + w.slack

def MarkedSequenceWindow.transferControlled (w : MarkedSequenceWindow) : Prop :=
  w.transferBudget ≤ w.sequenceLength + w.markWindow + w.markingSlack + w.slack

def markedSequenceWindowReady (w : MarkedSequenceWindow) : Prop :=
  0 < w.sequenceLength ∧
    w.markWindowControlled ∧
    w.transferControlled

def MarkedSequenceWindow.certificate (w : MarkedSequenceWindow) : ℕ :=
  w.sequenceLength + w.markWindow + w.markingSlack + w.slack

theorem markedSequence_transferBudget_le_certificate {w : MarkedSequenceWindow}
    (h : markedSequenceWindowReady w) :
    w.transferBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransfer⟩
  exact htransfer

def sampleMarkedSequenceWindow : MarkedSequenceWindow :=
  { sequenceLength := 7, markWindow := 9, markingSlack := 3, transferBudget := 18, slack := 0 }

example : markedSequenceWindowReady sampleMarkedSequenceWindow := by
  norm_num [markedSequenceWindowReady, MarkedSequenceWindow.markWindowControlled,
    MarkedSequenceWindow.transferControlled, sampleMarkedSequenceWindow]

example : sampleMarkedSequenceWindow.certificate = 19 := by
  native_decide


structure FiniteMarkedSequenceModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteMarkedSequenceModelsBudgetCertificate.controlled
    (c : FiniteMarkedSequenceModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteMarkedSequenceModelsBudgetCertificate.budgetControlled
    (c : FiniteMarkedSequenceModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteMarkedSequenceModelsBudgetCertificate.Ready
    (c : FiniteMarkedSequenceModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteMarkedSequenceModelsBudgetCertificate.size
    (c : FiniteMarkedSequenceModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteMarkedSequenceModels_budgetCertificate_le_size
    (c : FiniteMarkedSequenceModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteMarkedSequenceModelsBudgetCertificate :
    FiniteMarkedSequenceModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteMarkedSequenceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteMarkedSequenceModelsBudgetCertificate.controlled,
      sampleFiniteMarkedSequenceModelsBudgetCertificate]
  · norm_num [FiniteMarkedSequenceModelsBudgetCertificate.budgetControlled,
      sampleFiniteMarkedSequenceModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteMarkedSequenceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteMarkedSequenceModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteMarkedSequenceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteMarkedSequenceModelsBudgetCertificate.controlled,
      sampleFiniteMarkedSequenceModelsBudgetCertificate]
  · norm_num [FiniteMarkedSequenceModelsBudgetCertificate.budgetControlled,
      sampleFiniteMarkedSequenceModelsBudgetCertificate]

example :
    sampleFiniteMarkedSequenceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteMarkedSequenceModelsBudgetCertificate.size := by
  apply finiteMarkedSequenceModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteMarkedSequenceModelsBudgetCertificate.controlled,
      sampleFiniteMarkedSequenceModelsBudgetCertificate]
  · norm_num [FiniteMarkedSequenceModelsBudgetCertificate.budgetControlled,
      sampleFiniteMarkedSequenceModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteMarkedSequenceModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteMarkedSequenceModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteMarkedSequenceModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteMarkedSequenceModels
