import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite species quotient models.

This module records finite bookkeeping for quotient species models.
-/

namespace AnalyticCombinatorics.AppA.FiniteSpeciesQuotientModels

structure SpeciesQuotientData where
  orbitCount : ℕ
  quotientClasses : ℕ
  quotientSlack : ℕ
deriving DecidableEq, Repr

def hasOrbitCount (d : SpeciesQuotientData) : Prop :=
  0 < d.orbitCount

def quotientClassesControlled (d : SpeciesQuotientData) : Prop :=
  d.quotientClasses ≤ d.orbitCount + d.quotientSlack

def speciesQuotientReady (d : SpeciesQuotientData) : Prop :=
  hasOrbitCount d ∧ quotientClassesControlled d

def speciesQuotientBudget (d : SpeciesQuotientData) : ℕ :=
  d.orbitCount + d.quotientClasses + d.quotientSlack

theorem speciesQuotientReady.hasOrbitCount {d : SpeciesQuotientData}
    (h : speciesQuotientReady d) :
    hasOrbitCount d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem quotientClasses_le_budget (d : SpeciesQuotientData) :
    d.quotientClasses ≤ speciesQuotientBudget d := by
  unfold speciesQuotientBudget
  omega

def sampleSpeciesQuotientData : SpeciesQuotientData :=
  { orbitCount := 6, quotientClasses := 8, quotientSlack := 3 }

example : speciesQuotientReady sampleSpeciesQuotientData := by
  norm_num [speciesQuotientReady, hasOrbitCount]
  norm_num [quotientClassesControlled, sampleSpeciesQuotientData]

example : speciesQuotientBudget sampleSpeciesQuotientData = 17 := by
  native_decide

structure SpeciesQuotientWindow where
  orbitCount : ℕ
  quotientClasses : ℕ
  quotientSlack : ℕ
  quotientMapBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SpeciesQuotientWindow.classesControlled (w : SpeciesQuotientWindow) : Prop :=
  w.quotientClasses ≤ w.orbitCount + w.quotientSlack + w.slack

def SpeciesQuotientWindow.mapControlled (w : SpeciesQuotientWindow) : Prop :=
  w.quotientMapBudget ≤ w.orbitCount + w.quotientClasses + w.quotientSlack + w.slack

def speciesQuotientWindowReady (w : SpeciesQuotientWindow) : Prop :=
  0 < w.orbitCount ∧
    w.classesControlled ∧
    w.mapControlled

def SpeciesQuotientWindow.certificate (w : SpeciesQuotientWindow) : ℕ :=
  w.orbitCount + w.quotientClasses + w.quotientSlack + w.slack

theorem speciesQuotient_mapBudget_le_certificate {w : SpeciesQuotientWindow}
    (h : speciesQuotientWindowReady w) :
    w.quotientMapBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hmap⟩
  exact hmap

def sampleSpeciesQuotientWindow : SpeciesQuotientWindow :=
  { orbitCount := 6, quotientClasses := 8, quotientSlack := 3, quotientMapBudget := 16,
    slack := 0 }

example : speciesQuotientWindowReady sampleSpeciesQuotientWindow := by
  norm_num [speciesQuotientWindowReady, SpeciesQuotientWindow.classesControlled,
    SpeciesQuotientWindow.mapControlled, sampleSpeciesQuotientWindow]

example : sampleSpeciesQuotientWindow.certificate = 17 := by
  native_decide


structure FiniteSpeciesQuotientModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSpeciesQuotientModelsBudgetCertificate.controlled
    (c : FiniteSpeciesQuotientModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSpeciesQuotientModelsBudgetCertificate.budgetControlled
    (c : FiniteSpeciesQuotientModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSpeciesQuotientModelsBudgetCertificate.Ready
    (c : FiniteSpeciesQuotientModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSpeciesQuotientModelsBudgetCertificate.size
    (c : FiniteSpeciesQuotientModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSpeciesQuotientModels_budgetCertificate_le_size
    (c : FiniteSpeciesQuotientModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSpeciesQuotientModelsBudgetCertificate :
    FiniteSpeciesQuotientModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSpeciesQuotientModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesQuotientModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesQuotientModelsBudgetCertificate]
  · norm_num [FiniteSpeciesQuotientModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesQuotientModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSpeciesQuotientModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesQuotientModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSpeciesQuotientModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesQuotientModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesQuotientModelsBudgetCertificate]
  · norm_num [FiniteSpeciesQuotientModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesQuotientModelsBudgetCertificate]

example :
    sampleFiniteSpeciesQuotientModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesQuotientModelsBudgetCertificate.size := by
  apply finiteSpeciesQuotientModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSpeciesQuotientModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesQuotientModelsBudgetCertificate]
  · norm_num [FiniteSpeciesQuotientModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesQuotientModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteSpeciesQuotientModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSpeciesQuotientModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSpeciesQuotientModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSpeciesQuotientModels
