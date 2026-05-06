import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Phragmen-Lindelof style sector-growth bookkeeping.

The sector geometry and boundary domination hypotheses are represented by
finite natural-number budgets.
-/

namespace AnalyticCombinatorics.AppB.PhragmenLindelofModels

structure SectorGrowth where
  openingNumerator : ℕ
  openingDenominator : ℕ
  boundaryBound : ℕ
  interiorGrowth : ℕ
deriving DecidableEq, Repr

def validSector (s : SectorGrowth) : Prop :=
  0 < s.openingDenominator ∧ s.openingNumerator ≤ s.openingDenominator

def sectorDominated (s : SectorGrowth) : Prop :=
  validSector s ∧ s.interiorGrowth ≤ s.boundaryBound

def growthSlack (s : SectorGrowth) : ℕ :=
  s.boundaryBound - s.interiorGrowth

theorem sectorDominated.valid {s : SectorGrowth}
    (h : sectorDominated s) :
    validSector s ∧ s.interiorGrowth ≤ s.boundaryBound := by
  refine ⟨h.1, h.2⟩

theorem sectorDominated.interior_le {s : SectorGrowth}
    (h : sectorDominated s) :
    validSector s ∧ s.interiorGrowth ≤ s.boundaryBound := by
  refine ⟨h.1, h.2⟩

def sampleSector : SectorGrowth :=
  { openingNumerator := 1, openingDenominator := 3, boundaryBound := 8, interiorGrowth := 5 }

example : sectorDominated sampleSector := by
  norm_num [sectorDominated, validSector, sampleSector]

example : growthSlack sampleSector = 3 := by
  native_decide

structure PhragmenLindelofWindow where
  openingNumerator : ℕ
  openingDenominator : ℕ
  boundaryBound : ℕ
  interiorBound : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PhragmenLindelofWindow.sectorReady (w : PhragmenLindelofWindow) : Prop :=
  0 < w.openingDenominator ∧ w.openingNumerator ≤ w.openingDenominator

def PhragmenLindelofWindow.growthControlled (w : PhragmenLindelofWindow) : Prop :=
  w.interiorBound ≤ w.boundaryBound + w.slack

def PhragmenLindelofWindow.ready (w : PhragmenLindelofWindow) : Prop :=
  w.sectorReady ∧ w.growthControlled

def PhragmenLindelofWindow.certificate (w : PhragmenLindelofWindow) : ℕ :=
  w.openingNumerator + w.openingDenominator + w.boundaryBound + w.interiorBound + w.slack

theorem interiorBound_le_certificate (w : PhragmenLindelofWindow) :
    w.interiorBound ≤ w.certificate := by
  unfold PhragmenLindelofWindow.certificate
  omega

def samplePhragmenLindelofWindow : PhragmenLindelofWindow :=
  { openingNumerator := 1, openingDenominator := 3, boundaryBound := 8,
    interiorBound := 5, slack := 0 }

example : samplePhragmenLindelofWindow.ready := by
  norm_num [samplePhragmenLindelofWindow, PhragmenLindelofWindow.ready,
    PhragmenLindelofWindow.sectorReady, PhragmenLindelofWindow.growthControlled]


structure PhragmenLindelofModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PhragmenLindelofModelsBudgetCertificate.controlled
    (c : PhragmenLindelofModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PhragmenLindelofModelsBudgetCertificate.budgetControlled
    (c : PhragmenLindelofModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PhragmenLindelofModelsBudgetCertificate.Ready
    (c : PhragmenLindelofModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PhragmenLindelofModelsBudgetCertificate.size
    (c : PhragmenLindelofModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem phragmenLindelofModels_budgetCertificate_le_size
    (c : PhragmenLindelofModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePhragmenLindelofModelsBudgetCertificate :
    PhragmenLindelofModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePhragmenLindelofModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [PhragmenLindelofModelsBudgetCertificate.controlled,
      samplePhragmenLindelofModelsBudgetCertificate]
  · norm_num [PhragmenLindelofModelsBudgetCertificate.budgetControlled,
      samplePhragmenLindelofModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePhragmenLindelofModelsBudgetCertificate.certificateBudgetWindow ≤
      samplePhragmenLindelofModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePhragmenLindelofModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [PhragmenLindelofModelsBudgetCertificate.controlled,
      samplePhragmenLindelofModelsBudgetCertificate]
  · norm_num [PhragmenLindelofModelsBudgetCertificate.budgetControlled,
      samplePhragmenLindelofModelsBudgetCertificate]

example :
    samplePhragmenLindelofModelsBudgetCertificate.certificateBudgetWindow ≤
      samplePhragmenLindelofModelsBudgetCertificate.size := by
  apply phragmenLindelofModels_budgetCertificate_le_size
  constructor
  · norm_num [PhragmenLindelofModelsBudgetCertificate.controlled,
      samplePhragmenLindelofModelsBudgetCertificate]
  · norm_num [PhragmenLindelofModelsBudgetCertificate.budgetControlled,
      samplePhragmenLindelofModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PhragmenLindelofModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePhragmenLindelofModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePhragmenLindelofModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.PhragmenLindelofModels
