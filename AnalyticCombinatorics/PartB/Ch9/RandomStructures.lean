import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random structure examples.

This module records finite probability-window bookkeeping for random
combinatorial structures.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomStructures

structure RandomStructureWindow where
  sampleSize : ℕ
  limitWindow : ℕ
  fluctuationSlack : ℕ
deriving DecidableEq, Repr

def hasSamples (w : RandomStructureWindow) : Prop :=
  0 < w.sampleSize

def limitWindowControlled (w : RandomStructureWindow) : Prop :=
  w.limitWindow ≤ w.sampleSize + w.fluctuationSlack

def randomStructureReady (w : RandomStructureWindow) : Prop :=
  hasSamples w ∧ limitWindowControlled w

def randomStructureBudget (w : RandomStructureWindow) : ℕ :=
  w.sampleSize + w.limitWindow + w.fluctuationSlack

theorem randomStructureReady.hasSamples
    {w : RandomStructureWindow}
    (h : randomStructureReady w) :
    hasSamples w := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem limitWindow_le_budget (w : RandomStructureWindow) :
    w.limitWindow ≤ randomStructureBudget w := by
  unfold randomStructureBudget
  omega

def sampleRandomStructureWindow : RandomStructureWindow :=
  { sampleSize := 10, limitWindow := 12, fluctuationSlack := 4 }

example : randomStructureReady sampleRandomStructureWindow := by
  norm_num [randomStructureReady, hasSamples]
  norm_num [limitWindowControlled, sampleRandomStructureWindow]

example : randomStructureBudget sampleRandomStructureWindow = 26 := by
  native_decide

structure RandomStructureBudgetCertificate where
  sampleSizeWindow : ℕ
  limitWindow : ℕ
  fluctuationSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomStructureBudgetCertificate.controlled
    (c : RandomStructureBudgetCertificate) : Prop :=
  0 < c.sampleSizeWindow ∧
    c.limitWindow ≤ c.sampleSizeWindow + c.fluctuationSlackWindow + c.slack

def RandomStructureBudgetCertificate.budgetControlled
    (c : RandomStructureBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.sampleSizeWindow + c.limitWindow + c.fluctuationSlackWindow + c.slack

def RandomStructureBudgetCertificate.Ready
    (c : RandomStructureBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomStructureBudgetCertificate.size
    (c : RandomStructureBudgetCertificate) : ℕ :=
  c.sampleSizeWindow + c.limitWindow + c.fluctuationSlackWindow + c.slack

theorem randomStructure_budgetCertificate_le_size
    (c : RandomStructureBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomStructureBudgetCertificate :
    RandomStructureBudgetCertificate :=
  { sampleSizeWindow := 10
    limitWindow := 12
    fluctuationSlackWindow := 4
    certificateBudgetWindow := 27
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomStructureBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomStructureBudgetCertificate.controlled,
      sampleRandomStructureBudgetCertificate]
  · norm_num [RandomStructureBudgetCertificate.budgetControlled,
      sampleRandomStructureBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomStructureBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomStructureBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomStructureBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomStructureBudgetCertificate.controlled,
      sampleRandomStructureBudgetCertificate]
  · norm_num [RandomStructureBudgetCertificate.budgetControlled,
      sampleRandomStructureBudgetCertificate]

example :
    sampleRandomStructureBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomStructureBudgetCertificate.size := by
  apply randomStructure_budgetCertificate_le_size
  constructor
  · norm_num [RandomStructureBudgetCertificate.controlled,
      sampleRandomStructureBudgetCertificate]
  · norm_num [RandomStructureBudgetCertificate.budgetControlled,
      sampleRandomStructureBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RandomStructureBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleRandomStructureBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleRandomStructureBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.RandomStructures
