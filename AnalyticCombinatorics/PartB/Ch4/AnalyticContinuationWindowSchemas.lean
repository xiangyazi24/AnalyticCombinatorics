import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic continuation window schemas.

This module records finite bookkeeping for continuation windows in Chapter 4.
-/

namespace AnalyticCombinatorics.PartB.Ch4.AnalyticContinuationWindowSchemas

structure AnalyticContinuationWindowData where
  continuationSteps : ℕ
  domainWindow : ℕ
  continuationSlack : ℕ
deriving DecidableEq, Repr

def hasContinuationSteps (d : AnalyticContinuationWindowData) : Prop :=
  0 < d.continuationSteps

def domainWindowControlled (d : AnalyticContinuationWindowData) : Prop :=
  d.domainWindow ≤ d.continuationSteps + d.continuationSlack

def analyticContinuationWindowReady
    (d : AnalyticContinuationWindowData) : Prop :=
  hasContinuationSteps d ∧ domainWindowControlled d

def analyticContinuationWindowBudget
    (d : AnalyticContinuationWindowData) : ℕ :=
  d.continuationSteps + d.domainWindow + d.continuationSlack

theorem analyticContinuationWindowReady.hasContinuationSteps
    {d : AnalyticContinuationWindowData}
    (h : analyticContinuationWindowReady d) :
    hasContinuationSteps d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem domainWindow_le_budget (d : AnalyticContinuationWindowData) :
    d.domainWindow ≤ analyticContinuationWindowBudget d := by
  unfold analyticContinuationWindowBudget
  omega

def sampleAnalyticContinuationWindowData :
    AnalyticContinuationWindowData :=
  { continuationSteps := 6, domainWindow := 8, continuationSlack := 3 }

example : analyticContinuationWindowReady
    sampleAnalyticContinuationWindowData := by
  norm_num [analyticContinuationWindowReady, hasContinuationSteps]
  norm_num [domainWindowControlled, sampleAnalyticContinuationWindowData]

example :
    analyticContinuationWindowBudget
      sampleAnalyticContinuationWindowData = 17 := by
  native_decide


structure AnalyticContinuationWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticContinuationWindowSchemasBudgetCertificate.controlled
    (c : AnalyticContinuationWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticContinuationWindowSchemasBudgetCertificate.budgetControlled
    (c : AnalyticContinuationWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticContinuationWindowSchemasBudgetCertificate.Ready
    (c : AnalyticContinuationWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticContinuationWindowSchemasBudgetCertificate.size
    (c : AnalyticContinuationWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticContinuationWindowSchemas_budgetCertificate_le_size
    (c : AnalyticContinuationWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticContinuationWindowSchemasBudgetCertificate :
    AnalyticContinuationWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticContinuationWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticContinuationWindowSchemasBudgetCertificate.controlled,
      sampleAnalyticContinuationWindowSchemasBudgetCertificate]
  · norm_num [AnalyticContinuationWindowSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticContinuationWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticContinuationWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticContinuationWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticContinuationWindowSchemasBudgetCertificate.controlled,
      sampleAnalyticContinuationWindowSchemasBudgetCertificate]
  · norm_num [AnalyticContinuationWindowSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationWindowSchemasBudgetCertificate]

example :
    sampleAnalyticContinuationWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticContinuationWindowSchemasBudgetCertificate.size := by
  apply analyticContinuationWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticContinuationWindowSchemasBudgetCertificate.controlled,
      sampleAnalyticContinuationWindowSchemasBudgetCertificate]
  · norm_num [AnalyticContinuationWindowSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticContinuationWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticContinuationWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticContinuationWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.AnalyticContinuationWindowSchemas
