import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite labelled root models.

This module records finite bookkeeping for labelled rooting constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteLabelledRootModels

structure LabelledRootData where
  labelRoots : ℕ
  rootingWindow : ℕ
  labelSlack : ℕ
deriving DecidableEq, Repr

def hasLabelRoots (d : LabelledRootData) : Prop :=
  0 < d.labelRoots

def rootingWindowControlled (d : LabelledRootData) : Prop :=
  d.rootingWindow ≤ d.labelRoots + d.labelSlack

def labelledRootReady (d : LabelledRootData) : Prop :=
  hasLabelRoots d ∧ rootingWindowControlled d

def labelledRootBudget (d : LabelledRootData) : ℕ :=
  d.labelRoots + d.rootingWindow + d.labelSlack

theorem labelledRootReady.hasLabelRoots {d : LabelledRootData}
    (h : labelledRootReady d) :
    hasLabelRoots d ∧ rootingWindowControlled d ∧
      d.rootingWindow ≤ labelledRootBudget d := by
  rcases h with ⟨hroots, hcontrolled⟩
  refine ⟨hroots, hcontrolled, ?_⟩
  unfold labelledRootBudget
  omega

theorem rootingWindow_le_budget (d : LabelledRootData) :
    d.rootingWindow ≤ labelledRootBudget d := by
  unfold labelledRootBudget
  omega

def sampleLabelledRootData : LabelledRootData :=
  { labelRoots := 6, rootingWindow := 8, labelSlack := 3 }

example : labelledRootReady sampleLabelledRootData := by
  norm_num [labelledRootReady, hasLabelRoots]
  norm_num [rootingWindowControlled, sampleLabelledRootData]

example : labelledRootBudget sampleLabelledRootData = 17 := by
  native_decide

/-- Finite executable readiness audit for labelled-root data. -/
def labelledRootListReady (windows : List LabelledRootData) : Bool :=
  windows.all fun d =>
    0 < d.labelRoots && d.rootingWindow ≤ d.labelRoots + d.labelSlack

theorem labelledRootList_readyWindow :
    labelledRootListReady
      [{ labelRoots := 3, rootingWindow := 4, labelSlack := 1 },
       { labelRoots := 6, rootingWindow := 8, labelSlack := 3 }] = true := by
  unfold labelledRootListReady
  native_decide


structure FiniteLabelledRootModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteLabelledRootModelsBudgetCertificate.controlled
    (c : FiniteLabelledRootModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteLabelledRootModelsBudgetCertificate.budgetControlled
    (c : FiniteLabelledRootModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteLabelledRootModelsBudgetCertificate.Ready
    (c : FiniteLabelledRootModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteLabelledRootModelsBudgetCertificate.size
    (c : FiniteLabelledRootModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteLabelledRootModels_budgetCertificate_le_size
    (c : FiniteLabelledRootModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteLabelledRootModelsBudgetCertificate :
    FiniteLabelledRootModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteLabelledRootModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLabelledRootModelsBudgetCertificate.controlled,
      sampleFiniteLabelledRootModelsBudgetCertificate]
  · norm_num [FiniteLabelledRootModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelledRootModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteLabelledRootModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLabelledRootModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteLabelledRootModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLabelledRootModelsBudgetCertificate.controlled,
      sampleFiniteLabelledRootModelsBudgetCertificate]
  · norm_num [FiniteLabelledRootModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelledRootModelsBudgetCertificate]

example :
    sampleFiniteLabelledRootModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLabelledRootModelsBudgetCertificate.size := by
  apply finiteLabelledRootModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteLabelledRootModelsBudgetCertificate.controlled,
      sampleFiniteLabelledRootModelsBudgetCertificate]
  · norm_num [FiniteLabelledRootModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelledRootModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteLabelledRootModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteLabelledRootModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFiniteLabelledRootModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FiniteLabelledRootModels
