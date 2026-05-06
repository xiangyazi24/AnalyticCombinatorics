import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite weighted partition models.

This module records finite bookkeeping for weighted partition constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteWeightedPartitionModels

structure WeightedPartitionData where
  blockCount : ℕ
  weightWindow : ℕ
  partitionSlack : ℕ
deriving DecidableEq, Repr

def hasBlockCount (d : WeightedPartitionData) : Prop :=
  0 < d.blockCount

def weightWindowControlled (d : WeightedPartitionData) : Prop :=
  d.weightWindow ≤ d.blockCount + d.partitionSlack

def weightedPartitionReady (d : WeightedPartitionData) : Prop :=
  hasBlockCount d ∧ weightWindowControlled d

def weightedPartitionBudget (d : WeightedPartitionData) : ℕ :=
  d.blockCount + d.weightWindow + d.partitionSlack

theorem weightedPartitionReady.hasBlockCount {d : WeightedPartitionData}
    (h : weightedPartitionReady d) :
    hasBlockCount d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem weightWindow_le_budget (d : WeightedPartitionData) :
    d.weightWindow ≤ weightedPartitionBudget d := by
  unfold weightedPartitionBudget
  omega

def sampleWeightedPartitionData : WeightedPartitionData :=
  { blockCount := 7, weightWindow := 9, partitionSlack := 3 }

example : weightedPartitionReady sampleWeightedPartitionData := by
  norm_num [weightedPartitionReady, hasBlockCount]
  norm_num [weightWindowControlled, sampleWeightedPartitionData]

example : weightedPartitionBudget sampleWeightedPartitionData = 19 := by
  native_decide

structure WeightedPartitionWindow where
  blockCount : ℕ
  weightWindow : ℕ
  partitionSlack : ℕ
  blockWeightBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeightedPartitionWindow.weightControlled (w : WeightedPartitionWindow) : Prop :=
  w.weightWindow ≤ w.blockCount + w.partitionSlack + w.slack

def WeightedPartitionWindow.blockWeightControlled (w : WeightedPartitionWindow) : Prop :=
  w.blockWeightBudget ≤ w.blockCount + w.weightWindow + w.partitionSlack + w.slack

def weightedPartitionWindowReady (w : WeightedPartitionWindow) : Prop :=
  0 < w.blockCount ∧
    w.weightControlled ∧
    w.blockWeightControlled

def WeightedPartitionWindow.certificate (w : WeightedPartitionWindow) : ℕ :=
  w.blockCount + w.weightWindow + w.partitionSlack + w.slack

theorem weightedPartition_blockWeightBudget_le_certificate {w : WeightedPartitionWindow}
    (h : weightedPartitionWindowReady w) :
    w.blockWeightBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hblock⟩
  exact hblock

def sampleWeightedPartitionWindow : WeightedPartitionWindow :=
  { blockCount := 7, weightWindow := 9, partitionSlack := 3, blockWeightBudget := 18, slack := 0 }

example : weightedPartitionWindowReady sampleWeightedPartitionWindow := by
  norm_num [weightedPartitionWindowReady, WeightedPartitionWindow.weightControlled,
    WeightedPartitionWindow.blockWeightControlled, sampleWeightedPartitionWindow]

example : sampleWeightedPartitionWindow.certificate = 19 := by
  native_decide


structure FiniteWeightedPartitionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteWeightedPartitionModelsBudgetCertificate.controlled
    (c : FiniteWeightedPartitionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteWeightedPartitionModelsBudgetCertificate.budgetControlled
    (c : FiniteWeightedPartitionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteWeightedPartitionModelsBudgetCertificate.Ready
    (c : FiniteWeightedPartitionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteWeightedPartitionModelsBudgetCertificate.size
    (c : FiniteWeightedPartitionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteWeightedPartitionModels_budgetCertificate_le_size
    (c : FiniteWeightedPartitionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteWeightedPartitionModelsBudgetCertificate :
    FiniteWeightedPartitionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteWeightedPartitionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWeightedPartitionModelsBudgetCertificate.controlled,
      sampleFiniteWeightedPartitionModelsBudgetCertificate]
  · norm_num [FiniteWeightedPartitionModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedPartitionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteWeightedPartitionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWeightedPartitionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteWeightedPartitionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWeightedPartitionModelsBudgetCertificate.controlled,
      sampleFiniteWeightedPartitionModelsBudgetCertificate]
  · norm_num [FiniteWeightedPartitionModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedPartitionModelsBudgetCertificate]

example :
    sampleFiniteWeightedPartitionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWeightedPartitionModelsBudgetCertificate.size := by
  apply finiteWeightedPartitionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteWeightedPartitionModelsBudgetCertificate.controlled,
      sampleFiniteWeightedPartitionModelsBudgetCertificate]
  · norm_num [FiniteWeightedPartitionModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedPartitionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteWeightedPartitionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteWeightedPartitionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteWeightedPartitionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteWeightedPartitionModels
