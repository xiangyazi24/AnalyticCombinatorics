import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite rooted sequence models.

This module records finite bookkeeping for rooted sequence constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteRootedSequenceModels

structure RootedSequenceData where
  sequenceRoots : ℕ
  sequenceWindow : ℕ
  rootingSlack : ℕ
deriving DecidableEq, Repr

def hasSequenceRoots (d : RootedSequenceData) : Prop :=
  0 < d.sequenceRoots

def sequenceWindowControlled (d : RootedSequenceData) : Prop :=
  d.sequenceWindow ≤ d.sequenceRoots + d.rootingSlack

def rootedSequenceReady (d : RootedSequenceData) : Prop :=
  hasSequenceRoots d ∧ sequenceWindowControlled d

def rootedSequenceBudget (d : RootedSequenceData) : ℕ :=
  d.sequenceRoots + d.sequenceWindow + d.rootingSlack

theorem rootedSequenceReady.hasSequenceRoots {d : RootedSequenceData}
    (h : rootedSequenceReady d) :
    hasSequenceRoots d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem sequenceWindow_le_budget (d : RootedSequenceData) :
    d.sequenceWindow ≤ rootedSequenceBudget d := by
  unfold rootedSequenceBudget
  omega

def sampleRootedSequenceData : RootedSequenceData :=
  { sequenceRoots := 7, sequenceWindow := 9, rootingSlack := 3 }

example : rootedSequenceReady sampleRootedSequenceData := by
  norm_num [rootedSequenceReady, hasSequenceRoots]
  norm_num [sequenceWindowControlled, sampleRootedSequenceData]

example : rootedSequenceBudget sampleRootedSequenceData = 19 := by
  native_decide

structure RootedSequenceWindow where
  sequenceRoots : ℕ
  sequenceWindow : ℕ
  rootingSlack : ℕ
  rootedSequenceBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RootedSequenceWindow.sequenceControlled (w : RootedSequenceWindow) : Prop :=
  w.sequenceWindow ≤ w.sequenceRoots + w.rootingSlack + w.slack

def RootedSequenceWindow.rootedControlled (w : RootedSequenceWindow) : Prop :=
  w.rootedSequenceBudget ≤ w.sequenceRoots + w.sequenceWindow + w.rootingSlack + w.slack

def rootedSequenceWindowReady (w : RootedSequenceWindow) : Prop :=
  0 < w.sequenceRoots ∧
    w.sequenceControlled ∧
    w.rootedControlled

def RootedSequenceWindow.certificate (w : RootedSequenceWindow) : ℕ :=
  w.sequenceRoots + w.sequenceWindow + w.rootingSlack + w.slack

theorem rootedSequence_budget_le_certificate {w : RootedSequenceWindow}
    (h : rootedSequenceWindowReady w) :
    w.rootedSequenceBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hrooted⟩
  exact hrooted

def sampleRootedSequenceWindow : RootedSequenceWindow :=
  { sequenceRoots := 7, sequenceWindow := 9, rootingSlack := 3, rootedSequenceBudget := 18,
    slack := 0 }

example : rootedSequenceWindowReady sampleRootedSequenceWindow := by
  norm_num [rootedSequenceWindowReady, RootedSequenceWindow.sequenceControlled,
    RootedSequenceWindow.rootedControlled, sampleRootedSequenceWindow]

example : sampleRootedSequenceWindow.certificate = 19 := by
  native_decide


structure FiniteRootedSequenceModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteRootedSequenceModelsBudgetCertificate.controlled
    (c : FiniteRootedSequenceModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteRootedSequenceModelsBudgetCertificate.budgetControlled
    (c : FiniteRootedSequenceModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteRootedSequenceModelsBudgetCertificate.Ready
    (c : FiniteRootedSequenceModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteRootedSequenceModelsBudgetCertificate.size
    (c : FiniteRootedSequenceModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteRootedSequenceModels_budgetCertificate_le_size
    (c : FiniteRootedSequenceModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteRootedSequenceModelsBudgetCertificate :
    FiniteRootedSequenceModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteRootedSequenceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRootedSequenceModelsBudgetCertificate.controlled,
      sampleFiniteRootedSequenceModelsBudgetCertificate]
  · norm_num [FiniteRootedSequenceModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedSequenceModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteRootedSequenceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRootedSequenceModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteRootedSequenceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRootedSequenceModelsBudgetCertificate.controlled,
      sampleFiniteRootedSequenceModelsBudgetCertificate]
  · norm_num [FiniteRootedSequenceModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedSequenceModelsBudgetCertificate]

example :
    sampleFiniteRootedSequenceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRootedSequenceModelsBudgetCertificate.size := by
  apply finiteRootedSequenceModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteRootedSequenceModelsBudgetCertificate.controlled,
      sampleFiniteRootedSequenceModelsBudgetCertificate]
  · norm_num [FiniteRootedSequenceModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedSequenceModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteRootedSequenceModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteRootedSequenceModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteRootedSequenceModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteRootedSequenceModels
