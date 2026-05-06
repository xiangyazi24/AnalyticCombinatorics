import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Confluent singularity window schemas.

This module records finite bookkeeping for confluent singularity windows.
-/

namespace AnalyticCombinatorics.PartB.Ch6.ConfluentSingularityWindowSchemas

structure ConfluentSingularityWindowData where
  singularOrders : ℕ
  confluenceWindow : ℕ
  singularSlack : ℕ
deriving DecidableEq, Repr

def hasSingularOrders (d : ConfluentSingularityWindowData) : Prop :=
  0 < d.singularOrders

def confluenceWindowControlled
    (d : ConfluentSingularityWindowData) : Prop :=
  d.confluenceWindow ≤ d.singularOrders + d.singularSlack

def confluentSingularityReady
    (d : ConfluentSingularityWindowData) : Prop :=
  hasSingularOrders d ∧ confluenceWindowControlled d

def confluentSingularityBudget
    (d : ConfluentSingularityWindowData) : ℕ :=
  d.singularOrders + d.confluenceWindow + d.singularSlack

theorem confluentSingularityReady.hasSingularOrders
    {d : ConfluentSingularityWindowData}
    (h : confluentSingularityReady d) :
    hasSingularOrders d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem confluenceWindow_le_budget
    (d : ConfluentSingularityWindowData) :
    d.confluenceWindow ≤ confluentSingularityBudget d := by
  unfold confluentSingularityBudget
  omega

def sampleConfluentSingularityWindowData :
    ConfluentSingularityWindowData :=
  { singularOrders := 6, confluenceWindow := 8, singularSlack := 3 }

example : confluentSingularityReady
    sampleConfluentSingularityWindowData := by
  norm_num [confluentSingularityReady, hasSingularOrders]
  norm_num [confluenceWindowControlled, sampleConfluentSingularityWindowData]

example :
    confluentSingularityBudget sampleConfluentSingularityWindowData = 17 := by
  native_decide


structure ConfluentSingularityWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConfluentSingularityWindowSchemasBudgetCertificate.controlled
    (c : ConfluentSingularityWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ConfluentSingularityWindowSchemasBudgetCertificate.budgetControlled
    (c : ConfluentSingularityWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ConfluentSingularityWindowSchemasBudgetCertificate.Ready
    (c : ConfluentSingularityWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ConfluentSingularityWindowSchemasBudgetCertificate.size
    (c : ConfluentSingularityWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem confluentSingularityWindowSchemas_budgetCertificate_le_size
    (c : ConfluentSingularityWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleConfluentSingularityWindowSchemasBudgetCertificate :
    ConfluentSingularityWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleConfluentSingularityWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ConfluentSingularityWindowSchemasBudgetCertificate.controlled,
      sampleConfluentSingularityWindowSchemasBudgetCertificate]
  · norm_num [ConfluentSingularityWindowSchemasBudgetCertificate.budgetControlled,
      sampleConfluentSingularityWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleConfluentSingularityWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleConfluentSingularityWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleConfluentSingularityWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ConfluentSingularityWindowSchemasBudgetCertificate.controlled,
      sampleConfluentSingularityWindowSchemasBudgetCertificate]
  · norm_num [ConfluentSingularityWindowSchemasBudgetCertificate.budgetControlled,
      sampleConfluentSingularityWindowSchemasBudgetCertificate]

example :
    sampleConfluentSingularityWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleConfluentSingularityWindowSchemasBudgetCertificate.size := by
  apply confluentSingularityWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ConfluentSingularityWindowSchemasBudgetCertificate.controlled,
      sampleConfluentSingularityWindowSchemasBudgetCertificate]
  · norm_num [ConfluentSingularityWindowSchemasBudgetCertificate.budgetControlled,
      sampleConfluentSingularityWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List ConfluentSingularityWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleConfluentSingularityWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleConfluentSingularityWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.ConfluentSingularityWindowSchemas

