import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite decorated species models.

This module records finite bookkeeping for decorated species models.
-/

namespace AnalyticCombinatorics.AppA.FiniteDecoratedSpeciesModels

structure DecoratedSpeciesData where
  baseSpecies : ℕ
  decorationCount : ℕ
  decorSlack : ℕ
deriving DecidableEq, Repr

def hasBaseSpecies (d : DecoratedSpeciesData) : Prop :=
  0 < d.baseSpecies

def decorationsControlled (d : DecoratedSpeciesData) : Prop :=
  d.decorationCount ≤ d.baseSpecies + d.decorSlack

def decoratedSpeciesReady (d : DecoratedSpeciesData) : Prop :=
  hasBaseSpecies d ∧ decorationsControlled d

def decoratedSpeciesBudget (d : DecoratedSpeciesData) : ℕ :=
  d.baseSpecies + d.decorationCount + d.decorSlack

theorem decoratedSpeciesReady.hasBaseSpecies {d : DecoratedSpeciesData}
    (h : decoratedSpeciesReady d) :
    hasBaseSpecies d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem decorationCount_le_budget (d : DecoratedSpeciesData) :
    d.decorationCount ≤ decoratedSpeciesBudget d := by
  unfold decoratedSpeciesBudget
  omega

def sampleDecoratedSpeciesData : DecoratedSpeciesData :=
  { baseSpecies := 6, decorationCount := 8, decorSlack := 3 }

example : decoratedSpeciesReady sampleDecoratedSpeciesData := by
  norm_num [decoratedSpeciesReady, hasBaseSpecies]
  norm_num [decorationsControlled, sampleDecoratedSpeciesData]

example : decoratedSpeciesBudget sampleDecoratedSpeciesData = 17 := by
  native_decide

structure DecoratedSpeciesWindow where
  baseSpecies : ℕ
  decorationCount : ℕ
  decorSlack : ℕ
  transportBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DecoratedSpeciesWindow.decorationsControlled (w : DecoratedSpeciesWindow) : Prop :=
  w.decorationCount ≤ w.baseSpecies + w.decorSlack + w.slack

def DecoratedSpeciesWindow.transportControlled (w : DecoratedSpeciesWindow) : Prop :=
  w.transportBudget ≤ w.baseSpecies + w.decorationCount + w.decorSlack + w.slack

def decoratedSpeciesWindowReady (w : DecoratedSpeciesWindow) : Prop :=
  0 < w.baseSpecies ∧
    w.decorationsControlled ∧
    w.transportControlled

def DecoratedSpeciesWindow.certificate (w : DecoratedSpeciesWindow) : ℕ :=
  w.baseSpecies + w.decorationCount + w.decorSlack + w.slack

theorem decoratedSpecies_transportBudget_le_certificate {w : DecoratedSpeciesWindow}
    (h : decoratedSpeciesWindowReady w) :
    w.transportBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransport⟩
  exact htransport

def sampleDecoratedSpeciesWindow : DecoratedSpeciesWindow :=
  { baseSpecies := 6, decorationCount := 8, decorSlack := 3, transportBudget := 16, slack := 0 }

example : decoratedSpeciesWindowReady sampleDecoratedSpeciesWindow := by
  norm_num [decoratedSpeciesWindowReady, DecoratedSpeciesWindow.decorationsControlled,
    DecoratedSpeciesWindow.transportControlled, sampleDecoratedSpeciesWindow]

example : sampleDecoratedSpeciesWindow.certificate = 17 := by
  native_decide


structure FiniteDecoratedSpeciesModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteDecoratedSpeciesModelsBudgetCertificate.controlled
    (c : FiniteDecoratedSpeciesModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteDecoratedSpeciesModelsBudgetCertificate.budgetControlled
    (c : FiniteDecoratedSpeciesModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteDecoratedSpeciesModelsBudgetCertificate.Ready
    (c : FiniteDecoratedSpeciesModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteDecoratedSpeciesModelsBudgetCertificate.size
    (c : FiniteDecoratedSpeciesModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteDecoratedSpeciesModels_budgetCertificate_le_size
    (c : FiniteDecoratedSpeciesModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteDecoratedSpeciesModelsBudgetCertificate :
    FiniteDecoratedSpeciesModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteDecoratedSpeciesModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteDecoratedSpeciesModelsBudgetCertificate.controlled,
      sampleFiniteDecoratedSpeciesModelsBudgetCertificate]
  · norm_num [FiniteDecoratedSpeciesModelsBudgetCertificate.budgetControlled,
      sampleFiniteDecoratedSpeciesModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteDecoratedSpeciesModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteDecoratedSpeciesModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteDecoratedSpeciesModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteDecoratedSpeciesModelsBudgetCertificate.controlled,
      sampleFiniteDecoratedSpeciesModelsBudgetCertificate]
  · norm_num [FiniteDecoratedSpeciesModelsBudgetCertificate.budgetControlled,
      sampleFiniteDecoratedSpeciesModelsBudgetCertificate]

example :
    sampleFiniteDecoratedSpeciesModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteDecoratedSpeciesModelsBudgetCertificate.size := by
  apply finiteDecoratedSpeciesModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteDecoratedSpeciesModelsBudgetCertificate.controlled,
      sampleFiniteDecoratedSpeciesModelsBudgetCertificate]
  · norm_num [FiniteDecoratedSpeciesModelsBudgetCertificate.budgetControlled,
      sampleFiniteDecoratedSpeciesModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteDecoratedSpeciesModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteDecoratedSpeciesModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteDecoratedSpeciesModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteDecoratedSpeciesModels
