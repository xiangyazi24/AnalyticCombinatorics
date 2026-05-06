import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite weighted set models.

This module records finite bookkeeping for weighted set constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteWeightedSetModels

structure WeightedSetData where
  setBlocks : ℕ
  totalWeight : ℕ
  weightSlack : ℕ
deriving DecidableEq, Repr

def hasSetBlocks (d : WeightedSetData) : Prop :=
  0 < d.setBlocks

def totalWeightControlled (d : WeightedSetData) : Prop :=
  d.totalWeight ≤ d.setBlocks + d.weightSlack

def weightedSetReady (d : WeightedSetData) : Prop :=
  hasSetBlocks d ∧ totalWeightControlled d

def weightedSetBudget (d : WeightedSetData) : ℕ :=
  d.setBlocks + d.totalWeight + d.weightSlack

theorem weightedSetReady.hasSetBlocks {d : WeightedSetData}
    (h : weightedSetReady d) :
    hasSetBlocks d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem totalWeight_le_budget (d : WeightedSetData) :
    d.totalWeight ≤ weightedSetBudget d := by
  unfold weightedSetBudget
  omega

def sampleWeightedSetData : WeightedSetData :=
  { setBlocks := 6, totalWeight := 8, weightSlack := 3 }

example : weightedSetReady sampleWeightedSetData := by
  norm_num [weightedSetReady, hasSetBlocks]
  norm_num [totalWeightControlled, sampleWeightedSetData]

example : weightedSetBudget sampleWeightedSetData = 17 := by
  native_decide

structure WeightedSetWindow where
  setBlocks : ℕ
  totalWeight : ℕ
  weightSlack : ℕ
  subsetWeightBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeightedSetWindow.totalWeightControlled (w : WeightedSetWindow) : Prop :=
  w.totalWeight ≤ w.setBlocks + w.weightSlack + w.slack

def WeightedSetWindow.subsetWeightControlled (w : WeightedSetWindow) : Prop :=
  w.subsetWeightBudget ≤ w.setBlocks + w.totalWeight + w.weightSlack + w.slack

def weightedSetWindowReady (w : WeightedSetWindow) : Prop :=
  0 < w.setBlocks ∧
    w.totalWeightControlled ∧
    w.subsetWeightControlled

def WeightedSetWindow.certificate (w : WeightedSetWindow) : ℕ :=
  w.setBlocks + w.totalWeight + w.weightSlack + w.slack

theorem weightedSet_subsetWeightBudget_le_certificate {w : WeightedSetWindow}
    (h : weightedSetWindowReady w) :
    w.subsetWeightBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hsubset⟩
  exact hsubset

def sampleWeightedSetWindow : WeightedSetWindow :=
  { setBlocks := 6, totalWeight := 8, weightSlack := 3, subsetWeightBudget := 16, slack := 0 }

example : weightedSetWindowReady sampleWeightedSetWindow := by
  norm_num [weightedSetWindowReady, WeightedSetWindow.totalWeightControlled,
    WeightedSetWindow.subsetWeightControlled, sampleWeightedSetWindow]

example : sampleWeightedSetWindow.certificate = 17 := by
  native_decide


structure FiniteWeightedSetModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteWeightedSetModelsBudgetCertificate.controlled
    (c : FiniteWeightedSetModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteWeightedSetModelsBudgetCertificate.budgetControlled
    (c : FiniteWeightedSetModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteWeightedSetModelsBudgetCertificate.Ready
    (c : FiniteWeightedSetModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteWeightedSetModelsBudgetCertificate.size
    (c : FiniteWeightedSetModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteWeightedSetModels_budgetCertificate_le_size
    (c : FiniteWeightedSetModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteWeightedSetModelsBudgetCertificate :
    FiniteWeightedSetModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteWeightedSetModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWeightedSetModelsBudgetCertificate.controlled,
      sampleFiniteWeightedSetModelsBudgetCertificate]
  · norm_num [FiniteWeightedSetModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedSetModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteWeightedSetModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWeightedSetModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteWeightedSetModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWeightedSetModelsBudgetCertificate.controlled,
      sampleFiniteWeightedSetModelsBudgetCertificate]
  · norm_num [FiniteWeightedSetModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedSetModelsBudgetCertificate]

example :
    sampleFiniteWeightedSetModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWeightedSetModelsBudgetCertificate.size := by
  apply finiteWeightedSetModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteWeightedSetModelsBudgetCertificate.controlled,
      sampleFiniteWeightedSetModelsBudgetCertificate]
  · norm_num [FiniteWeightedSetModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedSetModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteWeightedSetModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteWeightedSetModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteWeightedSetModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteWeightedSetModels
