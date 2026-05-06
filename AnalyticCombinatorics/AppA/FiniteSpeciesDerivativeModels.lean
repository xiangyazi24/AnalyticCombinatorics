import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite species derivative models.

The finite schema records base labels, derivative choices, and residual
slack for species derivative bookkeeping.
-/

namespace AnalyticCombinatorics.AppA.FiniteSpeciesDerivativeModels

structure SpeciesDerivativeData where
  baseLabels : ℕ
  derivativeChoices : ℕ
  residualSlack : ℕ
deriving DecidableEq, Repr

def baseLabelsPositive (d : SpeciesDerivativeData) : Prop :=
  0 < d.baseLabels

def derivativeChoicesControlled (d : SpeciesDerivativeData) : Prop :=
  d.derivativeChoices ≤ d.baseLabels + d.residualSlack

def speciesDerivativeReady (d : SpeciesDerivativeData) : Prop :=
  baseLabelsPositive d ∧ derivativeChoicesControlled d

def speciesDerivativeBudget (d : SpeciesDerivativeData) : ℕ :=
  d.baseLabels + d.derivativeChoices + d.residualSlack

theorem speciesDerivativeReady.base {d : SpeciesDerivativeData}
    (h : speciesDerivativeReady d) :
    baseLabelsPositive d ∧ derivativeChoicesControlled d ∧
      d.derivativeChoices ≤ speciesDerivativeBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold speciesDerivativeBudget
  omega

theorem derivativeChoices_le_speciesDerivativeBudget
    (d : SpeciesDerivativeData) :
    d.derivativeChoices ≤ speciesDerivativeBudget d := by
  unfold speciesDerivativeBudget
  omega

def sampleSpeciesDerivativeData : SpeciesDerivativeData :=
  { baseLabels := 7, derivativeChoices := 9, residualSlack := 3 }

example : speciesDerivativeReady sampleSpeciesDerivativeData := by
  norm_num [speciesDerivativeReady, baseLabelsPositive]
  norm_num [derivativeChoicesControlled, sampleSpeciesDerivativeData]

example : speciesDerivativeBudget sampleSpeciesDerivativeData = 19 := by
  native_decide


structure FiniteSpeciesDerivativeModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSpeciesDerivativeModelsBudgetCertificate.controlled
    (c : FiniteSpeciesDerivativeModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSpeciesDerivativeModelsBudgetCertificate.budgetControlled
    (c : FiniteSpeciesDerivativeModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSpeciesDerivativeModelsBudgetCertificate.Ready
    (c : FiniteSpeciesDerivativeModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSpeciesDerivativeModelsBudgetCertificate.size
    (c : FiniteSpeciesDerivativeModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSpeciesDerivativeModels_budgetCertificate_le_size
    (c : FiniteSpeciesDerivativeModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSpeciesDerivativeModelsBudgetCertificate :
    FiniteSpeciesDerivativeModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSpeciesDerivativeModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesDerivativeModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesDerivativeModelsBudgetCertificate]
  · norm_num [FiniteSpeciesDerivativeModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesDerivativeModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSpeciesDerivativeModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesDerivativeModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSpeciesDerivativeModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSpeciesDerivativeModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesDerivativeModelsBudgetCertificate]
  · norm_num [FiniteSpeciesDerivativeModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesDerivativeModelsBudgetCertificate]

example :
    sampleFiniteSpeciesDerivativeModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSpeciesDerivativeModelsBudgetCertificate.size := by
  apply finiteSpeciesDerivativeModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSpeciesDerivativeModelsBudgetCertificate.controlled,
      sampleFiniteSpeciesDerivativeModelsBudgetCertificate]
  · norm_num [FiniteSpeciesDerivativeModelsBudgetCertificate.budgetControlled,
      sampleFiniteSpeciesDerivativeModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteSpeciesDerivativeModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSpeciesDerivativeModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSpeciesDerivativeModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSpeciesDerivativeModels
