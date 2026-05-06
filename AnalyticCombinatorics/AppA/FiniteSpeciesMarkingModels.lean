import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite species marking models.

This module records finite bookkeeping for marked species constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteSpeciesMarkingModels

structure SpeciesMarkingData where
  speciesSize : ℕ
  markCount : ℕ
  markingSlack : ℕ
deriving DecidableEq, Repr

def hasSpeciesSize (d : SpeciesMarkingData) : Prop :=
  0 < d.speciesSize

def markCountControlled (d : SpeciesMarkingData) : Prop :=
  d.markCount ≤ d.speciesSize + d.markingSlack

def speciesMarkingReady (d : SpeciesMarkingData) : Prop :=
  hasSpeciesSize d ∧ markCountControlled d

def speciesMarkingBudget (d : SpeciesMarkingData) : ℕ :=
  d.speciesSize + d.markCount + d.markingSlack

theorem speciesMarkingReady.hasSpeciesSize {d : SpeciesMarkingData}
    (h : speciesMarkingReady d) :
    hasSpeciesSize d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem markCount_le_budget (d : SpeciesMarkingData) :
    d.markCount ≤ speciesMarkingBudget d := by
  unfold speciesMarkingBudget
  omega

def sampleSpeciesMarkingData : SpeciesMarkingData :=
  { speciesSize := 6, markCount := 8, markingSlack := 3 }

example : speciesMarkingReady sampleSpeciesMarkingData := by
  norm_num [speciesMarkingReady, hasSpeciesSize]
  norm_num [markCountControlled, sampleSpeciesMarkingData]

example : speciesMarkingBudget sampleSpeciesMarkingData = 17 := by
  native_decide

structure SpeciesMarkingWindow where
  speciesSize : ℕ
  markCount : ℕ
  markingSlack : ℕ
  markedTransportBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SpeciesMarkingWindow.markCountControlled (w : SpeciesMarkingWindow) : Prop :=
  w.markCount ≤ w.speciesSize + w.markingSlack + w.slack

def SpeciesMarkingWindow.transportControlled (w : SpeciesMarkingWindow) : Prop :=
  w.markedTransportBudget ≤ w.speciesSize + w.markCount + w.markingSlack + w.slack

def speciesMarkingWindowReady (w : SpeciesMarkingWindow) : Prop :=
  0 < w.speciesSize ∧
    w.markCountControlled ∧
    w.transportControlled

def SpeciesMarkingWindow.certificate (w : SpeciesMarkingWindow) : ℕ :=
  w.speciesSize + w.markCount + w.markingSlack + w.slack

theorem speciesMarking_transportBudget_le_certificate {w : SpeciesMarkingWindow}
    (h : speciesMarkingWindowReady w) :
    w.markedTransportBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransport⟩
  exact htransport

def sampleSpeciesMarkingWindow : SpeciesMarkingWindow :=
  { speciesSize := 6, markCount := 8, markingSlack := 3, markedTransportBudget := 16,
    slack := 0 }

example : speciesMarkingWindowReady sampleSpeciesMarkingWindow := by
  norm_num [speciesMarkingWindowReady, SpeciesMarkingWindow.markCountControlled,
    SpeciesMarkingWindow.transportControlled, sampleSpeciesMarkingWindow]

example : sampleSpeciesMarkingWindow.certificate = 17 := by
  native_decide


structure FiniteSpeciesMarkingModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSpeciesMarkingModelsBudgetCertificate.controlled
    (c : FiniteSpeciesMarkingModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSpeciesMarkingModelsBudgetCertificate.budgetControlled
    (c : FiniteSpeciesMarkingModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSpeciesMarkingModelsBudgetCertificate.Ready
    (c : FiniteSpeciesMarkingModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSpeciesMarkingModelsBudgetCertificate.size
    (c : FiniteSpeciesMarkingModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSpeciesMarkingModels_budgetCertificate_le_size
    (c : FiniteSpeciesMarkingModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSpeciesMarkingModelsBudgetCertificate :
    FiniteSpeciesMarkingModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSpeciesMarkingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesMarkingModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesMarkingModelsBudgetCertificate]
  · norm_num [FiniteSpeciesMarkingModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesMarkingModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSpeciesMarkingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesMarkingModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSpeciesMarkingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesMarkingModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesMarkingModelsBudgetCertificate]
  · norm_num [FiniteSpeciesMarkingModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesMarkingModelsBudgetCertificate]

example :
    sampleFiniteSpeciesMarkingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesMarkingModelsBudgetCertificate.size := by
  apply finiteSpeciesMarkingModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSpeciesMarkingModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesMarkingModelsBudgetCertificate]
  · norm_num [FiniteSpeciesMarkingModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesMarkingModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteSpeciesMarkingModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSpeciesMarkingModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSpeciesMarkingModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSpeciesMarkingModels
