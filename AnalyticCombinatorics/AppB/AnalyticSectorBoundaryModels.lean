import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic sector boundary models.

This module records finite bookkeeping for sector boundary controls.
-/

namespace AnalyticCombinatorics.AppB.AnalyticSectorBoundaryModels

structure SectorBoundaryData where
  sectorBoundaryCount : ℕ
  boundaryWindow : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def hasSectorBoundaryCount (d : SectorBoundaryData) : Prop :=
  0 < d.sectorBoundaryCount

def boundaryWindowControlled (d : SectorBoundaryData) : Prop :=
  d.boundaryWindow ≤ d.sectorBoundaryCount + d.boundarySlack

def sectorBoundaryReady (d : SectorBoundaryData) : Prop :=
  hasSectorBoundaryCount d ∧ boundaryWindowControlled d

def sectorBoundaryBudget (d : SectorBoundaryData) : ℕ :=
  d.sectorBoundaryCount + d.boundaryWindow + d.boundarySlack

theorem sectorBoundaryReady.hasSectorBoundaryCount
    {d : SectorBoundaryData}
    (h : sectorBoundaryReady d) :
    hasSectorBoundaryCount d ∧ boundaryWindowControlled d ∧
      d.boundaryWindow ≤ sectorBoundaryBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold sectorBoundaryBudget
  omega

theorem boundaryWindow_le_budget (d : SectorBoundaryData) :
    d.boundaryWindow ≤ sectorBoundaryBudget d := by
  unfold sectorBoundaryBudget
  omega

def sampleSectorBoundaryData : SectorBoundaryData :=
  { sectorBoundaryCount := 6, boundaryWindow := 8, boundarySlack := 3 }

example : sectorBoundaryReady sampleSectorBoundaryData := by
  norm_num [sectorBoundaryReady, hasSectorBoundaryCount]
  norm_num [boundaryWindowControlled, sampleSectorBoundaryData]

example : sectorBoundaryBudget sampleSectorBoundaryData = 17 := by
  native_decide

/-- Finite executable readiness audit for sector-boundary windows. -/
def sectorBoundaryListReady (windows : List SectorBoundaryData) : Bool :=
  windows.all fun d =>
    0 < d.sectorBoundaryCount &&
      d.boundaryWindow ≤ d.sectorBoundaryCount + d.boundarySlack

theorem sectorBoundaryList_readyWindow :
    sectorBoundaryListReady
      [{ sectorBoundaryCount := 4, boundaryWindow := 5, boundarySlack := 1 },
       { sectorBoundaryCount := 6, boundaryWindow := 8, boundarySlack := 3 }] = true := by
  unfold sectorBoundaryListReady
  native_decide


structure AnalyticSectorBoundaryModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticSectorBoundaryModelsBudgetCertificate.controlled
    (c : AnalyticSectorBoundaryModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticSectorBoundaryModelsBudgetCertificate.budgetControlled
    (c : AnalyticSectorBoundaryModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticSectorBoundaryModelsBudgetCertificate.Ready
    (c : AnalyticSectorBoundaryModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticSectorBoundaryModelsBudgetCertificate.size
    (c : AnalyticSectorBoundaryModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticSectorBoundaryModels_budgetCertificate_le_size
    (c : AnalyticSectorBoundaryModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticSectorBoundaryModelsBudgetCertificate :
    AnalyticSectorBoundaryModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticSectorBoundaryModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticSectorBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticSectorBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticSectorBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSectorBoundaryModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticSectorBoundaryModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticSectorBoundaryModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticSectorBoundaryModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticSectorBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticSectorBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticSectorBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSectorBoundaryModelsBudgetCertificate]

example :
    sampleAnalyticSectorBoundaryModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticSectorBoundaryModelsBudgetCertificate.size := by
  apply analyticSectorBoundaryModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticSectorBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticSectorBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticSectorBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSectorBoundaryModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticSectorBoundaryModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticSectorBoundaryModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticSectorBoundaryModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.AnalyticSectorBoundaryModels
