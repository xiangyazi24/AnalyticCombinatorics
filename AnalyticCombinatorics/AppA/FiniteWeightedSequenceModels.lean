import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite weighted sequence models.

This module records finite bookkeeping for weighted sequence constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteWeightedSequenceModels

structure WeightedSequenceData where
  sequenceLength : ℕ
  weightWindow : ℕ
  sequenceSlack : ℕ
deriving DecidableEq, Repr

def hasSequenceLength (d : WeightedSequenceData) : Prop :=
  0 < d.sequenceLength

def weightWindowControlled (d : WeightedSequenceData) : Prop :=
  d.weightWindow ≤ d.sequenceLength + d.sequenceSlack

def weightedSequenceReady (d : WeightedSequenceData) : Prop :=
  hasSequenceLength d ∧ weightWindowControlled d

def weightedSequenceBudget (d : WeightedSequenceData) : ℕ :=
  d.sequenceLength + d.weightWindow + d.sequenceSlack

theorem weightedSequenceReady.hasSequenceLength {d : WeightedSequenceData}
    (h : weightedSequenceReady d) :
    hasSequenceLength d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem weightWindow_le_budget (d : WeightedSequenceData) :
    d.weightWindow ≤ weightedSequenceBudget d := by
  unfold weightedSequenceBudget
  omega

def sampleWeightedSequenceData : WeightedSequenceData :=
  { sequenceLength := 7, weightWindow := 9, sequenceSlack := 3 }

example : weightedSequenceReady sampleWeightedSequenceData := by
  norm_num [weightedSequenceReady, hasSequenceLength]
  norm_num [weightWindowControlled, sampleWeightedSequenceData]

example : weightedSequenceBudget sampleWeightedSequenceData = 19 := by
  native_decide

structure WeightedSequenceWindow where
  sequenceLength : ℕ
  weightWindow : ℕ
  sequenceSlack : ℕ
  prefixWeightBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeightedSequenceWindow.weightControlled (w : WeightedSequenceWindow) : Prop :=
  w.weightWindow ≤ w.sequenceLength + w.sequenceSlack + w.slack

def WeightedSequenceWindow.prefixWeightControlled (w : WeightedSequenceWindow) : Prop :=
  w.prefixWeightBudget ≤ w.sequenceLength + w.weightWindow + w.sequenceSlack + w.slack

def weightedSequenceWindowReady (w : WeightedSequenceWindow) : Prop :=
  0 < w.sequenceLength ∧
    w.weightControlled ∧
    w.prefixWeightControlled

def WeightedSequenceWindow.certificate (w : WeightedSequenceWindow) : ℕ :=
  w.sequenceLength + w.weightWindow + w.sequenceSlack + w.slack

theorem weightedSequence_prefixWeightBudget_le_certificate {w : WeightedSequenceWindow}
    (h : weightedSequenceWindowReady w) :
    w.prefixWeightBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hprefix⟩
  exact hprefix

def sampleWeightedSequenceWindow : WeightedSequenceWindow :=
  { sequenceLength := 7, weightWindow := 9, sequenceSlack := 3, prefixWeightBudget := 18,
    slack := 0 }

example : weightedSequenceWindowReady sampleWeightedSequenceWindow := by
  norm_num [weightedSequenceWindowReady, WeightedSequenceWindow.weightControlled,
    WeightedSequenceWindow.prefixWeightControlled, sampleWeightedSequenceWindow]

example : sampleWeightedSequenceWindow.certificate = 19 := by
  native_decide


structure FiniteWeightedSequenceModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteWeightedSequenceModelsBudgetCertificate.controlled
    (c : FiniteWeightedSequenceModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteWeightedSequenceModelsBudgetCertificate.budgetControlled
    (c : FiniteWeightedSequenceModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteWeightedSequenceModelsBudgetCertificate.Ready
    (c : FiniteWeightedSequenceModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteWeightedSequenceModelsBudgetCertificate.size
    (c : FiniteWeightedSequenceModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteWeightedSequenceModels_budgetCertificate_le_size
    (c : FiniteWeightedSequenceModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteWeightedSequenceModelsBudgetCertificate :
    FiniteWeightedSequenceModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteWeightedSequenceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWeightedSequenceModelsBudgetCertificate.controlled,
      sampleFiniteWeightedSequenceModelsBudgetCertificate]
  · norm_num [FiniteWeightedSequenceModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedSequenceModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteWeightedSequenceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWeightedSequenceModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteWeightedSequenceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWeightedSequenceModelsBudgetCertificate.controlled,
      sampleFiniteWeightedSequenceModelsBudgetCertificate]
  · norm_num [FiniteWeightedSequenceModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedSequenceModelsBudgetCertificate]

example :
    sampleFiniteWeightedSequenceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWeightedSequenceModelsBudgetCertificate.size := by
  apply finiteWeightedSequenceModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteWeightedSequenceModelsBudgetCertificate.controlled,
      sampleFiniteWeightedSequenceModelsBudgetCertificate]
  · norm_num [FiniteWeightedSequenceModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedSequenceModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteWeightedSequenceModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteWeightedSequenceModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteWeightedSequenceModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteWeightedSequenceModels
