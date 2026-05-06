import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite species cycle index window models.

This module records finite bookkeeping for species cycle index windows.
-/

namespace AnalyticCombinatorics.AppA.FiniteSpeciesCycleIndexWindowModels

structure SpeciesCycleIndexWindowData where
  speciesAtoms : ℕ
  cycleIndexWindow : ℕ
  speciesSlack : ℕ
deriving DecidableEq, Repr

def hasSpeciesAtoms (d : SpeciesCycleIndexWindowData) : Prop :=
  0 < d.speciesAtoms

def cycleIndexWindowControlled
    (d : SpeciesCycleIndexWindowData) : Prop :=
  d.cycleIndexWindow ≤ d.speciesAtoms + d.speciesSlack

def speciesCycleIndexWindowReady
    (d : SpeciesCycleIndexWindowData) : Prop :=
  hasSpeciesAtoms d ∧ cycleIndexWindowControlled d

def speciesCycleIndexWindowBudget
    (d : SpeciesCycleIndexWindowData) : ℕ :=
  d.speciesAtoms + d.cycleIndexWindow + d.speciesSlack

theorem speciesCycleIndexWindowReady.hasSpeciesAtoms
    {d : SpeciesCycleIndexWindowData}
    (h : speciesCycleIndexWindowReady d) :
    hasSpeciesAtoms d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem cycleIndexWindow_le_budget
    (d : SpeciesCycleIndexWindowData) :
    d.cycleIndexWindow ≤ speciesCycleIndexWindowBudget d := by
  unfold speciesCycleIndexWindowBudget
  omega

def sampleSpeciesCycleIndexWindowData :
    SpeciesCycleIndexWindowData :=
  { speciesAtoms := 7, cycleIndexWindow := 9, speciesSlack := 3 }

example : speciesCycleIndexWindowReady
    sampleSpeciesCycleIndexWindowData := by
  norm_num [speciesCycleIndexWindowReady, hasSpeciesAtoms]
  norm_num [cycleIndexWindowControlled, sampleSpeciesCycleIndexWindowData]

example :
    speciesCycleIndexWindowBudget sampleSpeciesCycleIndexWindowData = 19 := by
  native_decide


structure FiniteSpeciesCycleIndexWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSpeciesCycleIndexWindowModelsBudgetCertificate.controlled
    (c : FiniteSpeciesCycleIndexWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSpeciesCycleIndexWindowModelsBudgetCertificate.budgetControlled
    (c : FiniteSpeciesCycleIndexWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSpeciesCycleIndexWindowModelsBudgetCertificate.Ready
    (c : FiniteSpeciesCycleIndexWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSpeciesCycleIndexWindowModelsBudgetCertificate.size
    (c : FiniteSpeciesCycleIndexWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSpeciesCycleIndexWindowModels_budgetCertificate_le_size
    (c : FiniteSpeciesCycleIndexWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate :
    FiniteSpeciesCycleIndexWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesCycleIndexWindowModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate]
  · norm_num [FiniteSpeciesCycleIndexWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesCycleIndexWindowModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate]
  · norm_num [FiniteSpeciesCycleIndexWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate]

example :
    sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate.size := by
  apply finiteSpeciesCycleIndexWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSpeciesCycleIndexWindowModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate]
  · norm_num [FiniteSpeciesCycleIndexWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteSpeciesCycleIndexWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSpeciesCycleIndexWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSpeciesCycleIndexWindowModels
