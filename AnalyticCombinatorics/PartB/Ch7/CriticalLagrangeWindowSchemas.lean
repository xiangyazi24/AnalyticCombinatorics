import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Critical Lagrange window schemas.

This module records finite bookkeeping for critical Lagrange windows.
-/

namespace AnalyticCombinatorics.PartB.Ch7.CriticalLagrangeWindowSchemas

structure CriticalLagrangeWindowData where
  criticalOrder : ℕ
  lagrangeWindow : ℕ
  criticalSlack : ℕ
deriving DecidableEq, Repr

def hasCriticalOrder (d : CriticalLagrangeWindowData) : Prop :=
  0 < d.criticalOrder

def lagrangeWindowControlled (d : CriticalLagrangeWindowData) : Prop :=
  d.lagrangeWindow ≤ d.criticalOrder + d.criticalSlack

def criticalLagrangeWindowReady
    (d : CriticalLagrangeWindowData) : Prop :=
  hasCriticalOrder d ∧ lagrangeWindowControlled d

def criticalLagrangeWindowBudget
    (d : CriticalLagrangeWindowData) : ℕ :=
  d.criticalOrder + d.lagrangeWindow + d.criticalSlack

theorem criticalLagrangeWindowReady.hasCriticalOrder
    {d : CriticalLagrangeWindowData}
    (h : criticalLagrangeWindowReady d) :
    hasCriticalOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem lagrangeWindow_le_budget (d : CriticalLagrangeWindowData) :
    d.lagrangeWindow ≤ criticalLagrangeWindowBudget d := by
  unfold criticalLagrangeWindowBudget
  omega

def sampleCriticalLagrangeWindowData : CriticalLagrangeWindowData :=
  { criticalOrder := 6, lagrangeWindow := 8, criticalSlack := 3 }

example : criticalLagrangeWindowReady sampleCriticalLagrangeWindowData := by
  norm_num [criticalLagrangeWindowReady, hasCriticalOrder]
  norm_num [lagrangeWindowControlled, sampleCriticalLagrangeWindowData]

example : criticalLagrangeWindowBudget sampleCriticalLagrangeWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for critical Lagrange windows. -/
def criticalLagrangeWindowListReady
    (windows : List CriticalLagrangeWindowData) : Bool :=
  windows.all fun d =>
    0 < d.criticalOrder && d.lagrangeWindow ≤ d.criticalOrder + d.criticalSlack

theorem criticalLagrangeWindowList_readyWindow :
    criticalLagrangeWindowListReady
      [{ criticalOrder := 4, lagrangeWindow := 5, criticalSlack := 1 },
       { criticalOrder := 6, lagrangeWindow := 8, criticalSlack := 3 }] = true := by
  unfold criticalLagrangeWindowListReady
  native_decide

structure CriticalLagrangeWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CriticalLagrangeWindowSchemasBudgetCertificate.controlled
    (c : CriticalLagrangeWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CriticalLagrangeWindowSchemasBudgetCertificate.budgetControlled
    (c : CriticalLagrangeWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CriticalLagrangeWindowSchemasBudgetCertificate.Ready
    (c : CriticalLagrangeWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CriticalLagrangeWindowSchemasBudgetCertificate.size
    (c : CriticalLagrangeWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem criticalLagrangeWindowSchemas_budgetCertificate_le_size
    (c : CriticalLagrangeWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCriticalLagrangeWindowSchemasBudgetCertificate :
    CriticalLagrangeWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCriticalLagrangeWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CriticalLagrangeWindowSchemasBudgetCertificate.controlled,
      sampleCriticalLagrangeWindowSchemasBudgetCertificate]
  · norm_num [CriticalLagrangeWindowSchemasBudgetCertificate.budgetControlled,
      sampleCriticalLagrangeWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCriticalLagrangeWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalLagrangeWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCriticalLagrangeWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CriticalLagrangeWindowSchemasBudgetCertificate.controlled,
      sampleCriticalLagrangeWindowSchemasBudgetCertificate]
  · norm_num [CriticalLagrangeWindowSchemasBudgetCertificate.budgetControlled,
      sampleCriticalLagrangeWindowSchemasBudgetCertificate]

example :
    sampleCriticalLagrangeWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalLagrangeWindowSchemasBudgetCertificate.size := by
  apply criticalLagrangeWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CriticalLagrangeWindowSchemasBudgetCertificate.controlled,
      sampleCriticalLagrangeWindowSchemasBudgetCertificate]
  · norm_num [CriticalLagrangeWindowSchemasBudgetCertificate.budgetControlled,
      sampleCriticalLagrangeWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List CriticalLagrangeWindowSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCriticalLagrangeWindowSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCriticalLagrangeWindowSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch7.CriticalLagrangeWindowSchemas
