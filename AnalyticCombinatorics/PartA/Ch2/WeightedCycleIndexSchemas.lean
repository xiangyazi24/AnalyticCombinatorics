import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Weighted cycle index schemas.

This module records finite bookkeeping for weighted cycle-index windows:
a positive cycle-index size controls the weight window with index slack.
-/

namespace AnalyticCombinatorics.PartA.Ch2.WeightedCycleIndexSchemas

structure WeightedCycleIndexData where
  cycleIndexSize : ℕ
  weightWindow : ℕ
  indexSlack : ℕ
deriving DecidableEq, Repr

def hasCycleIndexSize (d : WeightedCycleIndexData) : Prop :=
  0 < d.cycleIndexSize

def weightWindowControlled (d : WeightedCycleIndexData) : Prop :=
  d.weightWindow ≤ d.cycleIndexSize + d.indexSlack

def weightedCycleIndexReady (d : WeightedCycleIndexData) : Prop :=
  hasCycleIndexSize d ∧ weightWindowControlled d

def weightedCycleIndexBudget (d : WeightedCycleIndexData) : ℕ :=
  d.cycleIndexSize + d.weightWindow + d.indexSlack

theorem weightedCycleIndexReady.hasCycleIndexSize
    {d : WeightedCycleIndexData}
    (h : weightedCycleIndexReady d) :
    hasCycleIndexSize d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem weightWindow_le_budget (d : WeightedCycleIndexData) :
    d.weightWindow ≤ weightedCycleIndexBudget d := by
  unfold weightedCycleIndexBudget
  omega

def sampleWeightedCycleIndexData : WeightedCycleIndexData :=
  { cycleIndexSize := 6, weightWindow := 8, indexSlack := 3 }

example : weightedCycleIndexReady sampleWeightedCycleIndexData := by
  norm_num [weightedCycleIndexReady, hasCycleIndexSize]
  norm_num [weightWindowControlled, sampleWeightedCycleIndexData]

example : weightedCycleIndexBudget sampleWeightedCycleIndexData = 17 := by
  native_decide

structure WeightedCycleIndexBudgetCertificate where
  cycleIndexSizeWindow : ℕ
  weightWindow : ℕ
  indexSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeightedCycleIndexBudgetCertificate.controlled
    (c : WeightedCycleIndexBudgetCertificate) : Prop :=
  0 < c.cycleIndexSizeWindow ∧
    c.weightWindow ≤ c.cycleIndexSizeWindow + c.indexSlackWindow + c.slack

def WeightedCycleIndexBudgetCertificate.budgetControlled
    (c : WeightedCycleIndexBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.cycleIndexSizeWindow + c.weightWindow + c.indexSlackWindow + c.slack

def WeightedCycleIndexBudgetCertificate.Ready
    (c : WeightedCycleIndexBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WeightedCycleIndexBudgetCertificate.size
    (c : WeightedCycleIndexBudgetCertificate) : ℕ :=
  c.cycleIndexSizeWindow + c.weightWindow + c.indexSlackWindow + c.slack

theorem weightedCycleIndex_budgetCertificate_le_size
    (c : WeightedCycleIndexBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWeightedCycleIndexBudgetCertificate :
    WeightedCycleIndexBudgetCertificate :=
  { cycleIndexSizeWindow := 6
    weightWindow := 8
    indexSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleWeightedCycleIndexBudgetCertificate.Ready := by
  constructor
  · norm_num [WeightedCycleIndexBudgetCertificate.controlled,
      sampleWeightedCycleIndexBudgetCertificate]
  · norm_num [WeightedCycleIndexBudgetCertificate.budgetControlled,
      sampleWeightedCycleIndexBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWeightedCycleIndexBudgetCertificate.certificateBudgetWindow ≤
      sampleWeightedCycleIndexBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleWeightedCycleIndexBudgetCertificate.Ready := by
  constructor
  · norm_num [WeightedCycleIndexBudgetCertificate.controlled,
      sampleWeightedCycleIndexBudgetCertificate]
  · norm_num [WeightedCycleIndexBudgetCertificate.budgetControlled,
      sampleWeightedCycleIndexBudgetCertificate]

example :
    sampleWeightedCycleIndexBudgetCertificate.certificateBudgetWindow ≤
      sampleWeightedCycleIndexBudgetCertificate.size := by
  apply weightedCycleIndex_budgetCertificate_le_size
  constructor
  · norm_num [WeightedCycleIndexBudgetCertificate.controlled,
      sampleWeightedCycleIndexBudgetCertificate]
  · norm_num [WeightedCycleIndexBudgetCertificate.budgetControlled,
      sampleWeightedCycleIndexBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List WeightedCycleIndexBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleWeightedCycleIndexBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleWeightedCycleIndexBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.WeightedCycleIndexSchemas
