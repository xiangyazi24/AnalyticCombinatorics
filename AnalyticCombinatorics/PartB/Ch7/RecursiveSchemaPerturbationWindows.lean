import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Recursive schema perturbation windows.

This module records finite bookkeeping for recursive schema perturbations.
-/

namespace AnalyticCombinatorics.PartB.Ch7.RecursiveSchemaPerturbationWindows

structure RecursivePerturbationData where
  schemaDepth : ℕ
  perturbationOrder : ℕ
  stabilitySlack : ℕ
deriving DecidableEq, Repr

def hasSchemaDepth (d : RecursivePerturbationData) : Prop :=
  0 < d.schemaDepth

def perturbationOrderControlled (d : RecursivePerturbationData) : Prop :=
  d.perturbationOrder ≤ d.schemaDepth + d.stabilitySlack

def recursivePerturbationReady (d : RecursivePerturbationData) : Prop :=
  hasSchemaDepth d ∧ perturbationOrderControlled d

def recursivePerturbationBudget (d : RecursivePerturbationData) : ℕ :=
  d.schemaDepth + d.perturbationOrder + d.stabilitySlack

theorem recursivePerturbationReady.hasSchemaDepth
    {d : RecursivePerturbationData}
    (h : recursivePerturbationReady d) :
    hasSchemaDepth d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem perturbationOrder_le_budget (d : RecursivePerturbationData) :
    d.perturbationOrder ≤ recursivePerturbationBudget d := by
  unfold recursivePerturbationBudget
  omega

def sampleRecursivePerturbationData : RecursivePerturbationData :=
  { schemaDepth := 6, perturbationOrder := 8, stabilitySlack := 3 }

example : recursivePerturbationReady sampleRecursivePerturbationData := by
  norm_num [recursivePerturbationReady, hasSchemaDepth]
  norm_num [perturbationOrderControlled, sampleRecursivePerturbationData]

example : recursivePerturbationBudget sampleRecursivePerturbationData = 17 := by
  native_decide

structure RecursivePerturbationBudgetCertificate where
  schemaDepthWindow : ℕ
  perturbationOrderWindow : ℕ
  stabilitySlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RecursivePerturbationBudgetCertificate.controlled
    (c : RecursivePerturbationBudgetCertificate) : Prop :=
  0 < c.schemaDepthWindow ∧
    c.perturbationOrderWindow ≤
      c.schemaDepthWindow + c.stabilitySlackWindow + c.slack

def RecursivePerturbationBudgetCertificate.budgetControlled
    (c : RecursivePerturbationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.schemaDepthWindow + c.perturbationOrderWindow + c.stabilitySlackWindow +
      c.slack

def RecursivePerturbationBudgetCertificate.Ready
    (c : RecursivePerturbationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RecursivePerturbationBudgetCertificate.size
    (c : RecursivePerturbationBudgetCertificate) : ℕ :=
  c.schemaDepthWindow + c.perturbationOrderWindow + c.stabilitySlackWindow +
    c.slack

theorem recursivePerturbation_budgetCertificate_le_size
    (c : RecursivePerturbationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRecursivePerturbationBudgetCertificate :
    RecursivePerturbationBudgetCertificate :=
  { schemaDepthWindow := 6
    perturbationOrderWindow := 8
    stabilitySlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRecursivePerturbationBudgetCertificate.Ready := by
  constructor
  · norm_num [RecursivePerturbationBudgetCertificate.controlled,
      sampleRecursivePerturbationBudgetCertificate]
  · norm_num [RecursivePerturbationBudgetCertificate.budgetControlled,
      sampleRecursivePerturbationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRecursivePerturbationBudgetCertificate.certificateBudgetWindow ≤
      sampleRecursivePerturbationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRecursivePerturbationBudgetCertificate.Ready := by
  constructor
  · norm_num [RecursivePerturbationBudgetCertificate.controlled,
      sampleRecursivePerturbationBudgetCertificate]
  · norm_num [RecursivePerturbationBudgetCertificate.budgetControlled,
      sampleRecursivePerturbationBudgetCertificate]

example :
    sampleRecursivePerturbationBudgetCertificate.certificateBudgetWindow ≤
      sampleRecursivePerturbationBudgetCertificate.size := by
  apply recursivePerturbation_budgetCertificate_le_size
  constructor
  · norm_num [RecursivePerturbationBudgetCertificate.controlled,
      sampleRecursivePerturbationBudgetCertificate]
  · norm_num [RecursivePerturbationBudgetCertificate.budgetControlled,
      sampleRecursivePerturbationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RecursivePerturbationBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleRecursivePerturbationBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleRecursivePerturbationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.RecursiveSchemaPerturbationWindows
