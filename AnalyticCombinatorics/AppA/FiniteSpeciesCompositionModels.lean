import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite species composition models.

This module records finite bookkeeping for species composition: a positive
outer species count controls the inner substitution count with composition
slack.
-/

namespace AnalyticCombinatorics.AppA.FiniteSpeciesCompositionModels

structure SpeciesCompositionData where
  outerSpecies : ℕ
  innerSubstitutions : ℕ
  compositionSlack : ℕ
deriving DecidableEq, Repr

def hasOuterSpecies (d : SpeciesCompositionData) : Prop :=
  0 < d.outerSpecies

def substitutionsControlled (d : SpeciesCompositionData) : Prop :=
  d.innerSubstitutions ≤ d.outerSpecies + d.compositionSlack

def speciesCompositionReady (d : SpeciesCompositionData) : Prop :=
  hasOuterSpecies d ∧ substitutionsControlled d

def speciesCompositionBudget (d : SpeciesCompositionData) : ℕ :=
  d.outerSpecies + d.innerSubstitutions + d.compositionSlack

theorem speciesCompositionReady.hasOuterSpecies
    {d : SpeciesCompositionData}
    (h : speciesCompositionReady d) :
    hasOuterSpecies d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem innerSubstitutions_le_budget (d : SpeciesCompositionData) :
    d.innerSubstitutions ≤ speciesCompositionBudget d := by
  unfold speciesCompositionBudget
  omega

def sampleSpeciesCompositionData : SpeciesCompositionData :=
  { outerSpecies := 6, innerSubstitutions := 8, compositionSlack := 3 }

example : speciesCompositionReady sampleSpeciesCompositionData := by
  norm_num [speciesCompositionReady, hasOuterSpecies]
  norm_num [substitutionsControlled, sampleSpeciesCompositionData]

example : speciesCompositionBudget sampleSpeciesCompositionData = 17 := by
  native_decide


structure FiniteSpeciesCompositionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSpeciesCompositionModelsBudgetCertificate.controlled
    (c : FiniteSpeciesCompositionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSpeciesCompositionModelsBudgetCertificate.budgetControlled
    (c : FiniteSpeciesCompositionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSpeciesCompositionModelsBudgetCertificate.Ready
    (c : FiniteSpeciesCompositionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSpeciesCompositionModelsBudgetCertificate.size
    (c : FiniteSpeciesCompositionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSpeciesCompositionModels_budgetCertificate_le_size
    (c : FiniteSpeciesCompositionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSpeciesCompositionModelsBudgetCertificate :
    FiniteSpeciesCompositionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSpeciesCompositionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesCompositionModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesCompositionModelsBudgetCertificate]
  · norm_num [FiniteSpeciesCompositionModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesCompositionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSpeciesCompositionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesCompositionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSpeciesCompositionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesCompositionModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesCompositionModelsBudgetCertificate]
  · norm_num [FiniteSpeciesCompositionModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesCompositionModelsBudgetCertificate]

example :
    sampleFiniteSpeciesCompositionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesCompositionModelsBudgetCertificate.size := by
  apply finiteSpeciesCompositionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSpeciesCompositionModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesCompositionModelsBudgetCertificate]
  · norm_num [FiniteSpeciesCompositionModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesCompositionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteSpeciesCompositionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSpeciesCompositionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSpeciesCompositionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSpeciesCompositionModels

