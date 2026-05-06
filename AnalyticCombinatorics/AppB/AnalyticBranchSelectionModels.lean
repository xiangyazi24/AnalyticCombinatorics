import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic branch selection models.

This module records finite bookkeeping for branch selections: a positive
branch domain controls selected cuts with a continuation slack.
-/

namespace AnalyticCombinatorics.AppB.AnalyticBranchSelectionModels

structure BranchSelectionData where
  branchDomains : ℕ
  selectedCuts : ℕ
  continuationSlack : ℕ
deriving DecidableEq, Repr

def hasBranchDomain (d : BranchSelectionData) : Prop :=
  0 < d.branchDomains

def selectedCutsControlled (d : BranchSelectionData) : Prop :=
  d.selectedCuts ≤ d.branchDomains + d.continuationSlack

def branchSelectionReady (d : BranchSelectionData) : Prop :=
  hasBranchDomain d ∧ selectedCutsControlled d

def branchSelectionBudget (d : BranchSelectionData) : ℕ :=
  d.branchDomains + d.selectedCuts + d.continuationSlack

theorem branchSelectionReady.hasBranchDomain {d : BranchSelectionData}
    (h : branchSelectionReady d) :
    hasBranchDomain d ∧ selectedCutsControlled d ∧
      d.selectedCuts ≤ branchSelectionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold branchSelectionBudget
  omega

theorem selectedCuts_le_budget (d : BranchSelectionData) :
    d.selectedCuts ≤ branchSelectionBudget d := by
  unfold branchSelectionBudget
  omega

def sampleBranchSelectionData : BranchSelectionData :=
  { branchDomains := 5, selectedCuts := 7, continuationSlack := 3 }

example : branchSelectionReady sampleBranchSelectionData := by
  norm_num [branchSelectionReady, hasBranchDomain]
  norm_num [selectedCutsControlled, sampleBranchSelectionData]

example : branchSelectionBudget sampleBranchSelectionData = 15 := by
  native_decide

/-- Finite executable readiness audit for branch-selection data. -/
def branchSelectionListReady (windows : List BranchSelectionData) : Bool :=
  windows.all fun d =>
    0 < d.branchDomains && d.selectedCuts ≤ d.branchDomains + d.continuationSlack

theorem branchSelectionList_readyWindow :
    branchSelectionListReady
      [{ branchDomains := 3, selectedCuts := 4, continuationSlack := 1 },
       { branchDomains := 5, selectedCuts := 7, continuationSlack := 3 }] = true := by
  unfold branchSelectionListReady
  native_decide


structure AnalyticBranchSelectionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticBranchSelectionModelsBudgetCertificate.controlled
    (c : AnalyticBranchSelectionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticBranchSelectionModelsBudgetCertificate.budgetControlled
    (c : AnalyticBranchSelectionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticBranchSelectionModelsBudgetCertificate.Ready
    (c : AnalyticBranchSelectionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticBranchSelectionModelsBudgetCertificate.size
    (c : AnalyticBranchSelectionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticBranchSelectionModels_budgetCertificate_le_size
    (c : AnalyticBranchSelectionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticBranchSelectionModelsBudgetCertificate :
    AnalyticBranchSelectionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticBranchSelectionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticBranchSelectionModelsBudgetCertificate.controlled,
      sampleAnalyticBranchSelectionModelsBudgetCertificate]
  · norm_num [AnalyticBranchSelectionModelsBudgetCertificate.budgetControlled,
      sampleAnalyticBranchSelectionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticBranchSelectionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticBranchSelectionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticBranchSelectionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticBranchSelectionModelsBudgetCertificate.controlled,
      sampleAnalyticBranchSelectionModelsBudgetCertificate]
  · norm_num [AnalyticBranchSelectionModelsBudgetCertificate.budgetControlled,
      sampleAnalyticBranchSelectionModelsBudgetCertificate]

example :
    sampleAnalyticBranchSelectionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticBranchSelectionModelsBudgetCertificate.size := by
  apply analyticBranchSelectionModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticBranchSelectionModelsBudgetCertificate.controlled,
      sampleAnalyticBranchSelectionModelsBudgetCertificate]
  · norm_num [AnalyticBranchSelectionModelsBudgetCertificate.budgetControlled,
      sampleAnalyticBranchSelectionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticBranchSelectionModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticBranchSelectionModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticBranchSelectionModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.AnalyticBranchSelectionModels
