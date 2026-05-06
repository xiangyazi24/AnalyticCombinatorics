import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic sector refinement models.

This module records finite bookkeeping for sector refinements.
-/

namespace AnalyticCombinatorics.AppB.AnalyticSectorRefinementModels

structure SectorRefinementData where
  sectorCount : ℕ
  refinedSectors : ℕ
  angularSlack : ℕ
deriving DecidableEq, Repr

def hasSectorCount (d : SectorRefinementData) : Prop :=
  0 < d.sectorCount

def refinedSectorsControlled (d : SectorRefinementData) : Prop :=
  d.refinedSectors ≤ d.sectorCount + d.angularSlack

def sectorRefinementReady (d : SectorRefinementData) : Prop :=
  hasSectorCount d ∧ refinedSectorsControlled d

def sectorRefinementBudget (d : SectorRefinementData) : ℕ :=
  d.sectorCount + d.refinedSectors + d.angularSlack

theorem sectorRefinementReady.hasSectorCount {d : SectorRefinementData}
    (h : sectorRefinementReady d) :
    hasSectorCount d ∧ refinedSectorsControlled d ∧
      d.refinedSectors ≤ sectorRefinementBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold sectorRefinementBudget
  omega

theorem refinedSectors_le_budget (d : SectorRefinementData) :
    d.refinedSectors ≤ sectorRefinementBudget d := by
  unfold sectorRefinementBudget
  omega

def sampleSectorRefinementData : SectorRefinementData :=
  { sectorCount := 6, refinedSectors := 8, angularSlack := 3 }

example : sectorRefinementReady sampleSectorRefinementData := by
  norm_num [sectorRefinementReady, hasSectorCount]
  norm_num [refinedSectorsControlled, sampleSectorRefinementData]

example : sectorRefinementBudget sampleSectorRefinementData = 17 := by
  native_decide

structure SectorRefinementWindow where
  sectorWindow : ℕ
  refinedWindow : ℕ
  angularSlack : ℕ
  refinementBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SectorRefinementWindow.refinementControlled (w : SectorRefinementWindow) : Prop :=
  w.refinedWindow ≤ w.sectorWindow + w.angularSlack + w.slack

def sectorRefinementWindowReady (w : SectorRefinementWindow) : Prop :=
  0 < w.sectorWindow ∧ w.refinementControlled ∧
    w.refinementBudget ≤ w.sectorWindow + w.refinedWindow + w.slack

def SectorRefinementWindow.certificate (w : SectorRefinementWindow) : ℕ :=
  w.sectorWindow + w.refinedWindow + w.angularSlack + w.refinementBudget + w.slack

theorem sectorRefinement_refinementBudget_le_certificate (w : SectorRefinementWindow) :
    w.refinementBudget ≤ w.certificate := by
  unfold SectorRefinementWindow.certificate
  omega

def sampleSectorRefinementWindow : SectorRefinementWindow :=
  { sectorWindow := 5, refinedWindow := 7, angularSlack := 2,
    refinementBudget := 14, slack := 2 }

example : sectorRefinementWindowReady sampleSectorRefinementWindow := by
  norm_num [sectorRefinementWindowReady, SectorRefinementWindow.refinementControlled,
    sampleSectorRefinementWindow]


structure AnalyticSectorRefinementModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticSectorRefinementModelsBudgetCertificate.controlled
    (c : AnalyticSectorRefinementModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticSectorRefinementModelsBudgetCertificate.budgetControlled
    (c : AnalyticSectorRefinementModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticSectorRefinementModelsBudgetCertificate.Ready
    (c : AnalyticSectorRefinementModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticSectorRefinementModelsBudgetCertificate.size
    (c : AnalyticSectorRefinementModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticSectorRefinementModels_budgetCertificate_le_size
    (c : AnalyticSectorRefinementModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticSectorRefinementModelsBudgetCertificate :
    AnalyticSectorRefinementModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticSectorRefinementModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticSectorRefinementModelsBudgetCertificate.controlled,
      sampleAnalyticSectorRefinementModelsBudgetCertificate]
  · norm_num [AnalyticSectorRefinementModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSectorRefinementModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticSectorRefinementModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticSectorRefinementModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticSectorRefinementModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticSectorRefinementModelsBudgetCertificate.controlled,
      sampleAnalyticSectorRefinementModelsBudgetCertificate]
  · norm_num [AnalyticSectorRefinementModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSectorRefinementModelsBudgetCertificate]

example :
    sampleAnalyticSectorRefinementModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticSectorRefinementModelsBudgetCertificate.size := by
  apply analyticSectorRefinementModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticSectorRefinementModelsBudgetCertificate.controlled,
      sampleAnalyticSectorRefinementModelsBudgetCertificate]
  · norm_num [AnalyticSectorRefinementModelsBudgetCertificate.budgetControlled,
      sampleAnalyticSectorRefinementModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticSectorRefinementModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticSectorRefinementModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticSectorRefinementModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticSectorRefinementModels
