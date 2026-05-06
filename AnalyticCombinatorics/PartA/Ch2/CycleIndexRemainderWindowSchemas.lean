import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cycle index remainder window schemas.

This module records finite bookkeeping for cycle index remainder windows.
-/

namespace AnalyticCombinatorics.PartA.Ch2.CycleIndexRemainderWindowSchemas

structure CycleIndexRemainderWindowData where
  indexTerms : ℕ
  remainderWindow : ℕ
  indexSlack : ℕ
deriving DecidableEq, Repr

def hasIndexTerms (d : CycleIndexRemainderWindowData) : Prop :=
  0 < d.indexTerms

def remainderWindowControlled
    (d : CycleIndexRemainderWindowData) : Prop :=
  d.remainderWindow ≤ d.indexTerms + d.indexSlack

def cycleIndexRemainderReady
    (d : CycleIndexRemainderWindowData) : Prop :=
  hasIndexTerms d ∧ remainderWindowControlled d

def cycleIndexRemainderBudget
    (d : CycleIndexRemainderWindowData) : ℕ :=
  d.indexTerms + d.remainderWindow + d.indexSlack

theorem cycleIndexRemainderReady.hasIndexTerms
    {d : CycleIndexRemainderWindowData}
    (h : cycleIndexRemainderReady d) :
    hasIndexTerms d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget
    (d : CycleIndexRemainderWindowData) :
    d.remainderWindow ≤ cycleIndexRemainderBudget d := by
  unfold cycleIndexRemainderBudget
  omega

def sampleCycleIndexRemainderWindowData :
    CycleIndexRemainderWindowData :=
  { indexTerms := 5, remainderWindow := 7, indexSlack := 2 }

example : cycleIndexRemainderReady
    sampleCycleIndexRemainderWindowData := by
  norm_num [cycleIndexRemainderReady, hasIndexTerms]
  norm_num [remainderWindowControlled, sampleCycleIndexRemainderWindowData]

example :
    cycleIndexRemainderBudget sampleCycleIndexRemainderWindowData = 14 := by
  native_decide


structure CycleIndexRemainderWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CycleIndexRemainderWindowSchemasBudgetCertificate.controlled
    (c : CycleIndexRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CycleIndexRemainderWindowSchemasBudgetCertificate.budgetControlled
    (c : CycleIndexRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CycleIndexRemainderWindowSchemasBudgetCertificate.Ready
    (c : CycleIndexRemainderWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CycleIndexRemainderWindowSchemasBudgetCertificate.size
    (c : CycleIndexRemainderWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cycleIndexRemainderWindowSchemas_budgetCertificate_le_size
    (c : CycleIndexRemainderWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCycleIndexRemainderWindowSchemasBudgetCertificate :
    CycleIndexRemainderWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCycleIndexRemainderWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CycleIndexRemainderWindowSchemasBudgetCertificate.controlled,
      sampleCycleIndexRemainderWindowSchemasBudgetCertificate]
  · norm_num [CycleIndexRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleCycleIndexRemainderWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCycleIndexRemainderWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCycleIndexRemainderWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCycleIndexRemainderWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CycleIndexRemainderWindowSchemasBudgetCertificate.controlled,
      sampleCycleIndexRemainderWindowSchemasBudgetCertificate]
  · norm_num [CycleIndexRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleCycleIndexRemainderWindowSchemasBudgetCertificate]

example :
    sampleCycleIndexRemainderWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCycleIndexRemainderWindowSchemasBudgetCertificate.size := by
  apply cycleIndexRemainderWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CycleIndexRemainderWindowSchemasBudgetCertificate.controlled,
      sampleCycleIndexRemainderWindowSchemasBudgetCertificate]
  · norm_num [CycleIndexRemainderWindowSchemasBudgetCertificate.budgetControlled,
      sampleCycleIndexRemainderWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List CycleIndexRemainderWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCycleIndexRemainderWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCycleIndexRemainderWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.CycleIndexRemainderWindowSchemas
