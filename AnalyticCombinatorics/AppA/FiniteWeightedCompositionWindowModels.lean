import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite weighted composition window models.

This module records finite bookkeeping for weighted composition windows.
-/

namespace AnalyticCombinatorics.AppA.FiniteWeightedCompositionWindowModels

structure WeightedCompositionWindowData where
  componentWeights : ℕ
  compositionWindow : ℕ
  weightSlack : ℕ
deriving DecidableEq, Repr

def hasComponentWeights (d : WeightedCompositionWindowData) : Prop :=
  0 < d.componentWeights

def compositionWindowControlled
    (d : WeightedCompositionWindowData) : Prop :=
  d.compositionWindow ≤ d.componentWeights + d.weightSlack

def weightedCompositionWindowReady
    (d : WeightedCompositionWindowData) : Prop :=
  hasComponentWeights d ∧ compositionWindowControlled d

def weightedCompositionWindowBudget
    (d : WeightedCompositionWindowData) : ℕ :=
  d.componentWeights + d.compositionWindow + d.weightSlack

theorem weightedCompositionWindowReady.hasComponentWeights
    {d : WeightedCompositionWindowData}
    (h : weightedCompositionWindowReady d) :
    hasComponentWeights d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem compositionWindow_le_budget
    (d : WeightedCompositionWindowData) :
    d.compositionWindow ≤ weightedCompositionWindowBudget d := by
  unfold weightedCompositionWindowBudget
  omega

def sampleWeightedCompositionWindowData :
    WeightedCompositionWindowData :=
  { componentWeights := 7, compositionWindow := 9, weightSlack := 3 }

example : weightedCompositionWindowReady
    sampleWeightedCompositionWindowData := by
  norm_num [weightedCompositionWindowReady, hasComponentWeights]
  norm_num [compositionWindowControlled, sampleWeightedCompositionWindowData]

example :
    weightedCompositionWindowBudget sampleWeightedCompositionWindowData = 19 := by
  native_decide


structure FiniteWeightedCompositionWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteWeightedCompositionWindowModelsBudgetCertificate.controlled
    (c : FiniteWeightedCompositionWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteWeightedCompositionWindowModelsBudgetCertificate.budgetControlled
    (c : FiniteWeightedCompositionWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteWeightedCompositionWindowModelsBudgetCertificate.Ready
    (c : FiniteWeightedCompositionWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteWeightedCompositionWindowModelsBudgetCertificate.size
    (c : FiniteWeightedCompositionWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteWeightedCompositionWindowModels_budgetCertificate_le_size
    (c : FiniteWeightedCompositionWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteWeightedCompositionWindowModelsBudgetCertificate :
    FiniteWeightedCompositionWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteWeightedCompositionWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWeightedCompositionWindowModelsBudgetCertificate.controlled,
      sampleFiniteWeightedCompositionWindowModelsBudgetCertificate]
  · norm_num [FiniteWeightedCompositionWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedCompositionWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteWeightedCompositionWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWeightedCompositionWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteWeightedCompositionWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWeightedCompositionWindowModelsBudgetCertificate.controlled,
      sampleFiniteWeightedCompositionWindowModelsBudgetCertificate]
  · norm_num [FiniteWeightedCompositionWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedCompositionWindowModelsBudgetCertificate]

example :
    sampleFiniteWeightedCompositionWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWeightedCompositionWindowModelsBudgetCertificate.size := by
  apply finiteWeightedCompositionWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteWeightedCompositionWindowModelsBudgetCertificate.controlled,
      sampleFiniteWeightedCompositionWindowModelsBudgetCertificate]
  · norm_num [FiniteWeightedCompositionWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedCompositionWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteWeightedCompositionWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteWeightedCompositionWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteWeightedCompositionWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteWeightedCompositionWindowModels

