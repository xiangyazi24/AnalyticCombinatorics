import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic Dirichlet boundary models.

This module records finite bookkeeping for Dirichlet boundary windows.
-/

namespace AnalyticCombinatorics.AppB.AnalyticDirichletBoundaryModels

structure DirichletBoundaryData where
  boundaryPieces : ℕ
  dirichletWindow : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def hasBoundaryPieces (d : DirichletBoundaryData) : Prop :=
  0 < d.boundaryPieces

def dirichletWindowControlled (d : DirichletBoundaryData) : Prop :=
  d.dirichletWindow ≤ d.boundaryPieces + d.boundarySlack

def dirichletBoundaryReady (d : DirichletBoundaryData) : Prop :=
  hasBoundaryPieces d ∧ dirichletWindowControlled d

def dirichletBoundaryBudget (d : DirichletBoundaryData) : ℕ :=
  d.boundaryPieces + d.dirichletWindow + d.boundarySlack

theorem dirichletBoundaryReady.hasBoundaryPieces
    {d : DirichletBoundaryData}
    (h : dirichletBoundaryReady d) :
    hasBoundaryPieces d ∧ dirichletWindowControlled d ∧
      d.dirichletWindow ≤ dirichletBoundaryBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold dirichletBoundaryBudget
  omega

theorem dirichletWindow_le_budget (d : DirichletBoundaryData) :
    d.dirichletWindow ≤ dirichletBoundaryBudget d := by
  unfold dirichletBoundaryBudget
  omega

def sampleDirichletBoundaryData : DirichletBoundaryData :=
  { boundaryPieces := 6, dirichletWindow := 8, boundarySlack := 3 }

example : dirichletBoundaryReady sampleDirichletBoundaryData := by
  norm_num [dirichletBoundaryReady, hasBoundaryPieces]
  norm_num [dirichletWindowControlled, sampleDirichletBoundaryData]

example : dirichletBoundaryBudget sampleDirichletBoundaryData = 17 := by
  native_decide

/-- Finite executable readiness audit for Dirichlet-boundary windows. -/
def dirichletBoundaryListReady (windows : List DirichletBoundaryData) : Bool :=
  windows.all fun d =>
    0 < d.boundaryPieces &&
      d.dirichletWindow ≤ d.boundaryPieces + d.boundarySlack

theorem dirichletBoundaryList_readyWindow :
    dirichletBoundaryListReady
      [{ boundaryPieces := 4, dirichletWindow := 5, boundarySlack := 1 },
       { boundaryPieces := 6, dirichletWindow := 8, boundarySlack := 3 }] = true := by
  unfold dirichletBoundaryListReady
  native_decide


structure AnalyticDirichletBoundaryModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticDirichletBoundaryModelsBudgetCertificate.controlled
    (c : AnalyticDirichletBoundaryModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticDirichletBoundaryModelsBudgetCertificate.budgetControlled
    (c : AnalyticDirichletBoundaryModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticDirichletBoundaryModelsBudgetCertificate.Ready
    (c : AnalyticDirichletBoundaryModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticDirichletBoundaryModelsBudgetCertificate.size
    (c : AnalyticDirichletBoundaryModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticDirichletBoundaryModels_budgetCertificate_le_size
    (c : AnalyticDirichletBoundaryModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticDirichletBoundaryModelsBudgetCertificate :
    AnalyticDirichletBoundaryModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticDirichletBoundaryModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticDirichletBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticDirichletBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticDirichletBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticDirichletBoundaryModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticDirichletBoundaryModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticDirichletBoundaryModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticDirichletBoundaryModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticDirichletBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticDirichletBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticDirichletBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticDirichletBoundaryModelsBudgetCertificate]

example :
    sampleAnalyticDirichletBoundaryModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticDirichletBoundaryModelsBudgetCertificate.size := by
  apply analyticDirichletBoundaryModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticDirichletBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticDirichletBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticDirichletBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticDirichletBoundaryModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticDirichletBoundaryModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticDirichletBoundaryModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticDirichletBoundaryModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.AnalyticDirichletBoundaryModels
