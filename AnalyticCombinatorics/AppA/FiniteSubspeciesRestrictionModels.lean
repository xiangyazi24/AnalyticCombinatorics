import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite subspecies restriction models.

This module records finite bookkeeping for subspecies restrictions.
-/

namespace AnalyticCombinatorics.AppA.FiniteSubspeciesRestrictionModels

structure SubspeciesRestrictionData where
  ambientSpecies : ℕ
  selectedSubspecies : ℕ
  restrictionSlack : ℕ
deriving DecidableEq, Repr

def hasAmbientSpecies (d : SubspeciesRestrictionData) : Prop :=
  0 < d.ambientSpecies

def selectedSubspeciesControlled (d : SubspeciesRestrictionData) : Prop :=
  d.selectedSubspecies ≤ d.ambientSpecies + d.restrictionSlack

def subspeciesRestrictionReady (d : SubspeciesRestrictionData) : Prop :=
  hasAmbientSpecies d ∧ selectedSubspeciesControlled d

def subspeciesRestrictionBudget (d : SubspeciesRestrictionData) : ℕ :=
  d.ambientSpecies + d.selectedSubspecies + d.restrictionSlack

theorem subspeciesRestrictionReady.hasAmbientSpecies
    {d : SubspeciesRestrictionData}
    (h : subspeciesRestrictionReady d) :
    hasAmbientSpecies d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem selectedSubspecies_le_budget (d : SubspeciesRestrictionData) :
    d.selectedSubspecies ≤ subspeciesRestrictionBudget d := by
  unfold subspeciesRestrictionBudget
  omega

def sampleSubspeciesRestrictionData : SubspeciesRestrictionData :=
  { ambientSpecies := 7, selectedSubspecies := 9, restrictionSlack := 3 }

example : subspeciesRestrictionReady sampleSubspeciesRestrictionData := by
  norm_num [subspeciesRestrictionReady, hasAmbientSpecies]
  norm_num [selectedSubspeciesControlled, sampleSubspeciesRestrictionData]

example : subspeciesRestrictionBudget sampleSubspeciesRestrictionData = 19 := by
  native_decide

structure SubspeciesRestrictionWindow where
  ambientSpecies : ℕ
  selectedSubspecies : ℕ
  restrictionSlack : ℕ
  inclusionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubspeciesRestrictionWindow.selectedControlled
    (w : SubspeciesRestrictionWindow) : Prop :=
  w.selectedSubspecies ≤ w.ambientSpecies + w.restrictionSlack + w.slack

def SubspeciesRestrictionWindow.inclusionControlled
    (w : SubspeciesRestrictionWindow) : Prop :=
  w.inclusionBudget ≤ w.ambientSpecies + w.selectedSubspecies + w.restrictionSlack + w.slack

def subspeciesRestrictionWindowReady (w : SubspeciesRestrictionWindow) : Prop :=
  0 < w.ambientSpecies ∧
    w.selectedControlled ∧
    w.inclusionControlled

def SubspeciesRestrictionWindow.certificate (w : SubspeciesRestrictionWindow) : ℕ :=
  w.ambientSpecies + w.selectedSubspecies + w.restrictionSlack + w.slack

theorem subspeciesRestriction_inclusionBudget_le_certificate
    {w : SubspeciesRestrictionWindow}
    (h : subspeciesRestrictionWindowReady w) :
    w.inclusionBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hinclusion⟩
  exact hinclusion

def sampleSubspeciesRestrictionWindow : SubspeciesRestrictionWindow :=
  { ambientSpecies := 7, selectedSubspecies := 9, restrictionSlack := 3, inclusionBudget := 18,
    slack := 0 }

example : subspeciesRestrictionWindowReady sampleSubspeciesRestrictionWindow := by
  norm_num [subspeciesRestrictionWindowReady, SubspeciesRestrictionWindow.selectedControlled,
    SubspeciesRestrictionWindow.inclusionControlled, sampleSubspeciesRestrictionWindow]

example : sampleSubspeciesRestrictionWindow.certificate = 19 := by
  native_decide


structure FiniteSubspeciesRestrictionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSubspeciesRestrictionModelsBudgetCertificate.controlled
    (c : FiniteSubspeciesRestrictionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSubspeciesRestrictionModelsBudgetCertificate.budgetControlled
    (c : FiniteSubspeciesRestrictionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSubspeciesRestrictionModelsBudgetCertificate.Ready
    (c : FiniteSubspeciesRestrictionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSubspeciesRestrictionModelsBudgetCertificate.size
    (c : FiniteSubspeciesRestrictionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSubspeciesRestrictionModels_budgetCertificate_le_size
    (c : FiniteSubspeciesRestrictionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSubspeciesRestrictionModelsBudgetCertificate :
    FiniteSubspeciesRestrictionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSubspeciesRestrictionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSubspeciesRestrictionModelsBudgetCertificate.controlled,
      sampleFiniteSubspeciesRestrictionModelsBudgetCertificate]
  · norm_num [FiniteSubspeciesRestrictionModelsBudgetCertificate.budgetControlled,
      sampleFiniteSubspeciesRestrictionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSubspeciesRestrictionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSubspeciesRestrictionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSubspeciesRestrictionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSubspeciesRestrictionModelsBudgetCertificate.controlled,
      sampleFiniteSubspeciesRestrictionModelsBudgetCertificate]
  · norm_num [FiniteSubspeciesRestrictionModelsBudgetCertificate.budgetControlled,
      sampleFiniteSubspeciesRestrictionModelsBudgetCertificate]

example :
    sampleFiniteSubspeciesRestrictionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSubspeciesRestrictionModelsBudgetCertificate.size := by
  apply finiteSubspeciesRestrictionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSubspeciesRestrictionModelsBudgetCertificate.controlled,
      sampleFiniteSubspeciesRestrictionModelsBudgetCertificate]
  · norm_num [FiniteSubspeciesRestrictionModelsBudgetCertificate.budgetControlled,
      sampleFiniteSubspeciesRestrictionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteSubspeciesRestrictionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSubspeciesRestrictionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSubspeciesRestrictionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSubspeciesRestrictionModels
