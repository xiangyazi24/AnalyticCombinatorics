import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Weighted assembly window schemas.

This module records finite bookkeeping for weighted assembly windows.
-/

namespace AnalyticCombinatorics.PartA.Ch2.WeightedAssemblyWindowSchemas

structure WeightedAssemblyWindowData where
  assemblyBlocks : ℕ
  weightWindow : ℕ
  assemblySlack : ℕ
deriving DecidableEq, Repr

def hasAssemblyBlocks (d : WeightedAssemblyWindowData) : Prop :=
  0 < d.assemblyBlocks

def weightWindowControlled (d : WeightedAssemblyWindowData) : Prop :=
  d.weightWindow ≤ d.assemblyBlocks + d.assemblySlack

def weightedAssemblyReady (d : WeightedAssemblyWindowData) : Prop :=
  hasAssemblyBlocks d ∧ weightWindowControlled d

def weightedAssemblyBudget (d : WeightedAssemblyWindowData) : ℕ :=
  d.assemblyBlocks + d.weightWindow + d.assemblySlack

theorem weightedAssemblyReady.hasAssemblyBlocks
    {d : WeightedAssemblyWindowData}
    (h : weightedAssemblyReady d) :
    hasAssemblyBlocks d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem weightWindow_le_budget (d : WeightedAssemblyWindowData) :
    d.weightWindow ≤ weightedAssemblyBudget d := by
  unfold weightedAssemblyBudget
  omega

def sampleWeightedAssemblyWindowData : WeightedAssemblyWindowData :=
  { assemblyBlocks := 6, weightWindow := 8, assemblySlack := 3 }

example : weightedAssemblyReady sampleWeightedAssemblyWindowData := by
  norm_num [weightedAssemblyReady, hasAssemblyBlocks]
  norm_num [weightWindowControlled, sampleWeightedAssemblyWindowData]

example : weightedAssemblyBudget sampleWeightedAssemblyWindowData = 17 := by
  native_decide

structure WeightedAssemblyBudgetCertificate where
  assemblyWindow : ℕ
  weightWindow : ℕ
  assemblySlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeightedAssemblyBudgetCertificate.controlled
    (c : WeightedAssemblyBudgetCertificate) : Prop :=
  0 < c.assemblyWindow ∧
    c.weightWindow ≤ c.assemblyWindow + c.assemblySlackWindow + c.slack

def WeightedAssemblyBudgetCertificate.budgetControlled
    (c : WeightedAssemblyBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.assemblyWindow + c.weightWindow + c.assemblySlackWindow + c.slack

def WeightedAssemblyBudgetCertificate.Ready
    (c : WeightedAssemblyBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WeightedAssemblyBudgetCertificate.size
    (c : WeightedAssemblyBudgetCertificate) : ℕ :=
  c.assemblyWindow + c.weightWindow + c.assemblySlackWindow + c.slack

theorem weightedAssembly_budgetCertificate_le_size
    (c : WeightedAssemblyBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWeightedAssemblyBudgetCertificate :
    WeightedAssemblyBudgetCertificate :=
  { assemblyWindow := 6
    weightWindow := 8
    assemblySlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleWeightedAssemblyBudgetCertificate.Ready := by
  constructor
  · norm_num [WeightedAssemblyBudgetCertificate.controlled,
      sampleWeightedAssemblyBudgetCertificate]
  · norm_num [WeightedAssemblyBudgetCertificate.budgetControlled,
      sampleWeightedAssemblyBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWeightedAssemblyBudgetCertificate.certificateBudgetWindow ≤
      sampleWeightedAssemblyBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleWeightedAssemblyBudgetCertificate.Ready := by
  constructor
  · norm_num [WeightedAssemblyBudgetCertificate.controlled,
      sampleWeightedAssemblyBudgetCertificate]
  · norm_num [WeightedAssemblyBudgetCertificate.budgetControlled,
      sampleWeightedAssemblyBudgetCertificate]

example :
    sampleWeightedAssemblyBudgetCertificate.certificateBudgetWindow ≤
      sampleWeightedAssemblyBudgetCertificate.size := by
  apply weightedAssembly_budgetCertificate_le_size
  constructor
  · norm_num [WeightedAssemblyBudgetCertificate.controlled,
      sampleWeightedAssemblyBudgetCertificate]
  · norm_num [WeightedAssemblyBudgetCertificate.budgetControlled,
      sampleWeightedAssemblyBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List WeightedAssemblyBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleWeightedAssemblyBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleWeightedAssemblyBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.WeightedAssemblyWindowSchemas
