import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Weighted substitution schemas.

This module records finite bookkeeping for weighted substitutions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.WeightedSubstitutionSchemas

structure WeightedSubstitutionData where
  substitutionSites : ℕ
  insertedWeight : ℕ
  substitutionSlack : ℕ
deriving DecidableEq, Repr

def hasSubstitutionSites (d : WeightedSubstitutionData) : Prop :=
  0 < d.substitutionSites

def insertedWeightControlled (d : WeightedSubstitutionData) : Prop :=
  d.insertedWeight ≤ d.substitutionSites + d.substitutionSlack

def weightedSubstitutionReady (d : WeightedSubstitutionData) : Prop :=
  hasSubstitutionSites d ∧ insertedWeightControlled d

def weightedSubstitutionBudget (d : WeightedSubstitutionData) : ℕ :=
  d.substitutionSites + d.insertedWeight + d.substitutionSlack

theorem weightedSubstitutionReady.hasSubstitutionSites
    {d : WeightedSubstitutionData}
    (h : weightedSubstitutionReady d) :
    hasSubstitutionSites d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem insertedWeight_le_budget (d : WeightedSubstitutionData) :
    d.insertedWeight ≤ weightedSubstitutionBudget d := by
  unfold weightedSubstitutionBudget
  omega

def sampleWeightedSubstitutionData : WeightedSubstitutionData :=
  { substitutionSites := 7, insertedWeight := 9, substitutionSlack := 3 }

example : weightedSubstitutionReady sampleWeightedSubstitutionData := by
  norm_num [weightedSubstitutionReady, hasSubstitutionSites]
  norm_num [insertedWeightControlled, sampleWeightedSubstitutionData]

example : weightedSubstitutionBudget sampleWeightedSubstitutionData = 19 := by
  native_decide

structure WeightedSubstitutionBudgetCertificate where
  siteWindow : ℕ
  insertedWeightWindow : ℕ
  substitutionSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeightedSubstitutionBudgetCertificate.controlled
    (c : WeightedSubstitutionBudgetCertificate) : Prop :=
  0 < c.siteWindow ∧
    c.insertedWeightWindow ≤ c.siteWindow + c.substitutionSlackWindow + c.slack

def WeightedSubstitutionBudgetCertificate.budgetControlled
    (c : WeightedSubstitutionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.siteWindow + c.insertedWeightWindow + c.substitutionSlackWindow + c.slack

def WeightedSubstitutionBudgetCertificate.Ready
    (c : WeightedSubstitutionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WeightedSubstitutionBudgetCertificate.size
    (c : WeightedSubstitutionBudgetCertificate) : ℕ :=
  c.siteWindow + c.insertedWeightWindow + c.substitutionSlackWindow + c.slack

theorem weightedSubstitution_budgetCertificate_le_size
    (c : WeightedSubstitutionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWeightedSubstitutionBudgetCertificate :
    WeightedSubstitutionBudgetCertificate :=
  { siteWindow := 7
    insertedWeightWindow := 9
    substitutionSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleWeightedSubstitutionBudgetCertificate.Ready := by
  constructor
  · norm_num [WeightedSubstitutionBudgetCertificate.controlled,
      sampleWeightedSubstitutionBudgetCertificate]
  · norm_num [WeightedSubstitutionBudgetCertificate.budgetControlled,
      sampleWeightedSubstitutionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWeightedSubstitutionBudgetCertificate.certificateBudgetWindow ≤
      sampleWeightedSubstitutionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleWeightedSubstitutionBudgetCertificate.Ready := by
  constructor
  · norm_num [WeightedSubstitutionBudgetCertificate.controlled,
      sampleWeightedSubstitutionBudgetCertificate]
  · norm_num [WeightedSubstitutionBudgetCertificate.budgetControlled,
      sampleWeightedSubstitutionBudgetCertificate]

example :
    sampleWeightedSubstitutionBudgetCertificate.certificateBudgetWindow ≤
      sampleWeightedSubstitutionBudgetCertificate.size := by
  apply weightedSubstitution_budgetCertificate_le_size
  constructor
  · norm_num [WeightedSubstitutionBudgetCertificate.controlled,
      sampleWeightedSubstitutionBudgetCertificate]
  · norm_num [WeightedSubstitutionBudgetCertificate.budgetControlled,
      sampleWeightedSubstitutionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List WeightedSubstitutionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleWeightedSubstitutionBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleWeightedSubstitutionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.WeightedSubstitutionSchemas
