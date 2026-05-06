import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Polylog singularity window schemas.

This module records finite bookkeeping for polylog singularity windows.
-/

namespace AnalyticCombinatorics.PartB.Ch6.PolylogSingularityWindowSchemas

structure PolylogSingularityWindowData where
  singularOrders : ℕ
  polylogWindow : ℕ
  singularSlack : ℕ
deriving DecidableEq, Repr

def hasSingularOrders (d : PolylogSingularityWindowData) : Prop :=
  0 < d.singularOrders

def polylogWindowControlled
    (d : PolylogSingularityWindowData) : Prop :=
  d.polylogWindow ≤ d.singularOrders + d.singularSlack

def polylogSingularityWindowReady
    (d : PolylogSingularityWindowData) : Prop :=
  hasSingularOrders d ∧ polylogWindowControlled d

def polylogSingularityWindowBudget
    (d : PolylogSingularityWindowData) : ℕ :=
  d.singularOrders + d.polylogWindow + d.singularSlack

theorem polylogSingularityWindowReady.hasSingularOrders
    {d : PolylogSingularityWindowData}
    (h : polylogSingularityWindowReady d) :
    hasSingularOrders d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem polylogWindow_le_budget
    (d : PolylogSingularityWindowData) :
    d.polylogWindow ≤ polylogSingularityWindowBudget d := by
  unfold polylogSingularityWindowBudget
  omega

def samplePolylogSingularityWindowData :
    PolylogSingularityWindowData :=
  { singularOrders := 7, polylogWindow := 9, singularSlack := 3 }

example : polylogSingularityWindowReady
    samplePolylogSingularityWindowData := by
  norm_num [polylogSingularityWindowReady, hasSingularOrders]
  norm_num [polylogWindowControlled, samplePolylogSingularityWindowData]

example :
    polylogSingularityWindowBudget samplePolylogSingularityWindowData = 19 := by
  native_decide


structure PolylogSingularityWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PolylogSingularityWindowSchemasBudgetCertificate.controlled
    (c : PolylogSingularityWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PolylogSingularityWindowSchemasBudgetCertificate.budgetControlled
    (c : PolylogSingularityWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PolylogSingularityWindowSchemasBudgetCertificate.Ready
    (c : PolylogSingularityWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PolylogSingularityWindowSchemasBudgetCertificate.size
    (c : PolylogSingularityWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem polylogSingularityWindowSchemas_budgetCertificate_le_size
    (c : PolylogSingularityWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePolylogSingularityWindowSchemasBudgetCertificate :
    PolylogSingularityWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePolylogSingularityWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PolylogSingularityWindowSchemasBudgetCertificate.controlled,
      samplePolylogSingularityWindowSchemasBudgetCertificate]
  · norm_num [PolylogSingularityWindowSchemasBudgetCertificate.budgetControlled,
      samplePolylogSingularityWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePolylogSingularityWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePolylogSingularityWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePolylogSingularityWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PolylogSingularityWindowSchemasBudgetCertificate.controlled,
      samplePolylogSingularityWindowSchemasBudgetCertificate]
  · norm_num [PolylogSingularityWindowSchemasBudgetCertificate.budgetControlled,
      samplePolylogSingularityWindowSchemasBudgetCertificate]

example :
    samplePolylogSingularityWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePolylogSingularityWindowSchemasBudgetCertificate.size := by
  apply polylogSingularityWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PolylogSingularityWindowSchemasBudgetCertificate.controlled,
      samplePolylogSingularityWindowSchemasBudgetCertificate]
  · norm_num [PolylogSingularityWindowSchemasBudgetCertificate.budgetControlled,
      samplePolylogSingularityWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List PolylogSingularityWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePolylogSingularityWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePolylogSingularityWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.PolylogSingularityWindowSchemas
