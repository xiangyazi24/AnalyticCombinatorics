import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite species restriction models.

This module records finite bookkeeping for species restriction windows.
-/

namespace AnalyticCombinatorics.AppA.FiniteSpeciesRestrictionModels

structure SpeciesRestrictionData where
  restrictionBase : ℕ
  retainedLabels : ℕ
  restrictionSlack : ℕ
deriving DecidableEq, Repr

def hasRestrictionBase (d : SpeciesRestrictionData) : Prop :=
  0 < d.restrictionBase

def retainedLabelsControlled (d : SpeciesRestrictionData) : Prop :=
  d.retainedLabels ≤ d.restrictionBase + d.restrictionSlack

def speciesRestrictionReady (d : SpeciesRestrictionData) : Prop :=
  hasRestrictionBase d ∧ retainedLabelsControlled d

def speciesRestrictionBudget (d : SpeciesRestrictionData) : ℕ :=
  d.restrictionBase + d.retainedLabels + d.restrictionSlack

theorem speciesRestrictionReady.hasRestrictionBase
    {d : SpeciesRestrictionData}
    (h : speciesRestrictionReady d) :
    hasRestrictionBase d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem retainedLabels_le_budget (d : SpeciesRestrictionData) :
    d.retainedLabels ≤ speciesRestrictionBudget d := by
  unfold speciesRestrictionBudget
  omega

def sampleSpeciesRestrictionData : SpeciesRestrictionData :=
  { restrictionBase := 5, retainedLabels := 7, restrictionSlack := 3 }

example : speciesRestrictionReady sampleSpeciesRestrictionData := by
  norm_num [speciesRestrictionReady, hasRestrictionBase]
  norm_num [retainedLabelsControlled, sampleSpeciesRestrictionData]

example : speciesRestrictionBudget sampleSpeciesRestrictionData = 15 := by
  native_decide

structure SpeciesRestrictionWindow where
  restrictionBase : ℕ
  retainedLabels : ℕ
  restrictionSlack : ℕ
  inducedBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SpeciesRestrictionWindow.retainedControlled (w : SpeciesRestrictionWindow) : Prop :=
  w.retainedLabels ≤ w.restrictionBase + w.restrictionSlack + w.slack

def SpeciesRestrictionWindow.inducedControlled (w : SpeciesRestrictionWindow) : Prop :=
  w.inducedBudget ≤ w.restrictionBase + w.retainedLabels + w.restrictionSlack + w.slack

def speciesRestrictionWindowReady (w : SpeciesRestrictionWindow) : Prop :=
  0 < w.restrictionBase ∧
    w.retainedControlled ∧
    w.inducedControlled

def SpeciesRestrictionWindow.certificate (w : SpeciesRestrictionWindow) : ℕ :=
  w.restrictionBase + w.retainedLabels + w.restrictionSlack + w.slack

theorem speciesRestriction_inducedBudget_le_certificate {w : SpeciesRestrictionWindow}
    (h : speciesRestrictionWindowReady w) :
    w.inducedBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hinduced⟩
  exact hinduced

def sampleSpeciesRestrictionWindow : SpeciesRestrictionWindow :=
  { restrictionBase := 5, retainedLabels := 7, restrictionSlack := 3, inducedBudget := 14,
    slack := 0 }

example : speciesRestrictionWindowReady sampleSpeciesRestrictionWindow := by
  norm_num [speciesRestrictionWindowReady, SpeciesRestrictionWindow.retainedControlled,
    SpeciesRestrictionWindow.inducedControlled, sampleSpeciesRestrictionWindow]

example : sampleSpeciesRestrictionWindow.certificate = 15 := by
  native_decide


structure FiniteSpeciesRestrictionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSpeciesRestrictionModelsBudgetCertificate.controlled
    (c : FiniteSpeciesRestrictionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSpeciesRestrictionModelsBudgetCertificate.budgetControlled
    (c : FiniteSpeciesRestrictionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSpeciesRestrictionModelsBudgetCertificate.Ready
    (c : FiniteSpeciesRestrictionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSpeciesRestrictionModelsBudgetCertificate.size
    (c : FiniteSpeciesRestrictionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSpeciesRestrictionModels_budgetCertificate_le_size
    (c : FiniteSpeciesRestrictionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSpeciesRestrictionModelsBudgetCertificate :
    FiniteSpeciesRestrictionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSpeciesRestrictionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesRestrictionModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesRestrictionModelsBudgetCertificate]
  · norm_num [FiniteSpeciesRestrictionModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesRestrictionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSpeciesRestrictionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesRestrictionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSpeciesRestrictionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesRestrictionModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesRestrictionModelsBudgetCertificate]
  · norm_num [FiniteSpeciesRestrictionModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesRestrictionModelsBudgetCertificate]

example :
    sampleFiniteSpeciesRestrictionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesRestrictionModelsBudgetCertificate.size := by
  apply finiteSpeciesRestrictionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSpeciesRestrictionModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesRestrictionModelsBudgetCertificate]
  · norm_num [FiniteSpeciesRestrictionModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesRestrictionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteSpeciesRestrictionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSpeciesRestrictionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSpeciesRestrictionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSpeciesRestrictionModels
