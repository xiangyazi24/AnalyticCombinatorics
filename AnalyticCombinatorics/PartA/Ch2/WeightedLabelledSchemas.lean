import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Weighted labelled schemas.

The finite record stores labels, weights, and construction slack for
weighted labelled classes.
-/

namespace AnalyticCombinatorics.PartA.Ch2.WeightedLabelledSchemas

structure WeightedLabelledData where
  labelCount : ℕ
  weightBudget : ℕ
  constructionSlack : ℕ
deriving DecidableEq, Repr

def labelCountPositive (d : WeightedLabelledData) : Prop :=
  0 < d.labelCount

def weightControlled (d : WeightedLabelledData) : Prop :=
  d.weightBudget ≤ d.labelCount + d.constructionSlack

def weightedLabelledReady (d : WeightedLabelledData) : Prop :=
  labelCountPositive d ∧ weightControlled d

def weightedLabelledBudget (d : WeightedLabelledData) : ℕ :=
  d.labelCount + d.weightBudget + d.constructionSlack

theorem weightedLabelledReady.labels {d : WeightedLabelledData}
    (h : weightedLabelledReady d) :
    labelCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem weightBudget_le_weightedLabelledBudget (d : WeightedLabelledData) :
    d.weightBudget ≤ weightedLabelledBudget d := by
  unfold weightedLabelledBudget
  omega

def sampleWeightedLabelledData : WeightedLabelledData :=
  { labelCount := 6, weightBudget := 8, constructionSlack := 3 }

example : weightedLabelledReady sampleWeightedLabelledData := by
  norm_num [weightedLabelledReady, labelCountPositive]
  norm_num [weightControlled, sampleWeightedLabelledData]

example : weightedLabelledBudget sampleWeightedLabelledData = 17 := by
  native_decide

structure WeightedLabelledWindow where
  labelCount : ℕ
  weightBudget : ℕ
  constructionSlack : ℕ
  transportBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeightedLabelledWindow.weightControlled (w : WeightedLabelledWindow) : Prop :=
  w.weightBudget ≤ w.labelCount + w.constructionSlack + w.slack

def WeightedLabelledWindow.transportControlled (w : WeightedLabelledWindow) : Prop :=
  w.transportBudget ≤ w.labelCount + w.weightBudget + w.constructionSlack + w.slack

def weightedLabelledWindowReady (w : WeightedLabelledWindow) : Prop :=
  0 < w.labelCount ∧
    w.weightControlled ∧
    w.transportControlled

def WeightedLabelledWindow.certificate (w : WeightedLabelledWindow) : ℕ :=
  w.labelCount + w.weightBudget + w.constructionSlack + w.slack

theorem weightedLabelled_transportBudget_le_certificate {w : WeightedLabelledWindow}
    (h : weightedLabelledWindowReady w) :
    w.transportBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransport⟩
  exact htransport

def sampleWeightedLabelledWindow : WeightedLabelledWindow :=
  { labelCount := 6, weightBudget := 8, constructionSlack := 3, transportBudget := 16,
    slack := 0 }

example : weightedLabelledWindowReady sampleWeightedLabelledWindow := by
  norm_num [weightedLabelledWindowReady, WeightedLabelledWindow.weightControlled,
    WeightedLabelledWindow.transportControlled, sampleWeightedLabelledWindow]

example : sampleWeightedLabelledWindow.certificate = 17 := by
  native_decide


structure WeightedLabelledSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeightedLabelledSchemasBudgetCertificate.controlled
    (c : WeightedLabelledSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def WeightedLabelledSchemasBudgetCertificate.budgetControlled
    (c : WeightedLabelledSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def WeightedLabelledSchemasBudgetCertificate.Ready
    (c : WeightedLabelledSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WeightedLabelledSchemasBudgetCertificate.size
    (c : WeightedLabelledSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem weightedLabelledSchemas_budgetCertificate_le_size
    (c : WeightedLabelledSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWeightedLabelledSchemasBudgetCertificate :
    WeightedLabelledSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleWeightedLabelledSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [WeightedLabelledSchemasBudgetCertificate.controlled,
      sampleWeightedLabelledSchemasBudgetCertificate]
  · norm_num [WeightedLabelledSchemasBudgetCertificate.budgetControlled,
      sampleWeightedLabelledSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWeightedLabelledSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleWeightedLabelledSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleWeightedLabelledSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [WeightedLabelledSchemasBudgetCertificate.controlled,
      sampleWeightedLabelledSchemasBudgetCertificate]
  · norm_num [WeightedLabelledSchemasBudgetCertificate.budgetControlled,
      sampleWeightedLabelledSchemasBudgetCertificate]

example :
    sampleWeightedLabelledSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleWeightedLabelledSchemasBudgetCertificate.size := by
  apply weightedLabelledSchemas_budgetCertificate_le_size
  constructor
  · norm_num [WeightedLabelledSchemasBudgetCertificate.controlled,
      sampleWeightedLabelledSchemasBudgetCertificate]
  · norm_num [WeightedLabelledSchemasBudgetCertificate.budgetControlled,
      sampleWeightedLabelledSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List WeightedLabelledSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleWeightedLabelledSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleWeightedLabelledSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.WeightedLabelledSchemas
