import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Perturbation Schemas

Finite perturbation models for moving singularities, parameter marking, and
quasi-powers.
-/

namespace AnalyticCombinatorics.Asymptotics.Perturbation

def linearPerturb (base slope n : ℚ) : ℚ :=
  base + slope * n

theorem linearPerturb_samples :
    linearPerturb 1 (1 / 10) 0 = 1 ∧
    linearPerturb 1 (1 / 10) 2 = 6 / 5 ∧
    linearPerturb 3 (2 / 5) 5 = 5 := by
  native_decide

def perturbedRadiusInv (rhoInv epsilonNumerator epsilonDenominator n : ℕ) : ℚ :=
  (rhoInv : ℚ) + (epsilonNumerator : ℚ) * (n : ℚ) / (epsilonDenominator : ℚ)

theorem perturbedRadiusInv_samples :
    perturbedRadiusInv 4 1 10 0 = 4 ∧
    perturbedRadiusInv 4 1 10 2 = 21 / 5 ∧
    perturbedRadiusInv 3 2 5 5 = 5 := by
  native_decide

def exponentialPerturbModel (base shift n : ℕ) : ℕ :=
  (base + shift) ^ n

theorem exponentialPerturbModel_samples :
    exponentialPerturbModel 2 0 5 = 32 ∧
    exponentialPerturbModel 2 1 4 = 81 ∧
    exponentialPerturbModel 3 2 3 = 125 := by
  native_decide

structure PerturbationData where
  baseRadiusInv : ℕ
  derivativeNumerator : ℤ
  derivativeDenominator : ℕ

def quasiPowerPerturbationData : PerturbationData where
  baseRadiusInv := 2
  derivativeNumerator := 1
  derivativeDenominator := 2

theorem quasiPowerPerturbationData_values :
    quasiPowerPerturbationData.baseRadiusInv = 2 ∧
    quasiPowerPerturbationData.derivativeNumerator = 1 ∧
    quasiPowerPerturbationData.derivativeDenominator = 2 := by
  native_decide

def perturbationDataReady (data : PerturbationData) : Prop :=
  0 < data.baseRadiusInv ∧ 0 < data.derivativeDenominator

theorem quasiPowerPerturbationData_ready :
    perturbationDataReady quasiPowerPerturbationData := by
  unfold perturbationDataReady quasiPowerPerturbationData
  native_decide

/-- Finite executable readiness audit for perturbation data. -/
def perturbationDataListReady (data : List PerturbationData) : Bool :=
  data.all fun d => 0 < d.baseRadiusInv && 0 < d.derivativeDenominator

theorem perturbationDataList_readyWindow :
    perturbationDataListReady
      [{ baseRadiusInv := 1, derivativeNumerator := -1, derivativeDenominator := 1 },
       { baseRadiusInv := 2, derivativeNumerator := 1, derivativeDenominator := 2 }] =
      true := by
  unfold perturbationDataListReady
  native_decide

def AnalyticPerturbationSchema
    (coeff : ℕ → ℂ) (data : PerturbationData) : Prop :=
  perturbationDataReady data ∧ coeff 0 = 1 ∧ coeff 4 = 81

def perturbationCoeffWitness (n : ℕ) : ℂ :=
  exponentialPerturbModel 2 1 n

theorem analytic_perturbation_schema_statement :
    AnalyticPerturbationSchema perturbationCoeffWitness quasiPowerPerturbationData := by
  unfold AnalyticPerturbationSchema perturbationDataReady quasiPowerPerturbationData
    perturbationCoeffWitness exponentialPerturbModel
  norm_num

/-- A finite certificate for analytic perturbation schema data. -/
structure AnalyticPerturbationCertificate where
  radiusWindow : ℕ
  derivativeDenominatorWindow : ℕ
  coefficientBudget : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Perturbation certificates keep radius and derivative denominator positive. -/
def analyticPerturbationCertificateControlled
    (w : AnalyticPerturbationCertificate) : Prop :=
  0 < w.radiusWindow ∧ 0 < w.derivativeDenominatorWindow

/-- Readiness for an analytic perturbation certificate. -/
def analyticPerturbationCertificateReady
    (w : AnalyticPerturbationCertificate) : Prop :=
  analyticPerturbationCertificateControlled w ∧
    w.certificateBudget ≤
      w.radiusWindow + w.derivativeDenominatorWindow + w.coefficientBudget + w.slack

/-- Total size of an analytic perturbation certificate. -/
def analyticPerturbationCertificateSize
    (w : AnalyticPerturbationCertificate) : ℕ :=
  w.radiusWindow + w.derivativeDenominatorWindow + w.coefficientBudget +
    w.certificateBudget + w.slack

theorem analyticPerturbationCertificate_budget_le_size
    (w : AnalyticPerturbationCertificate)
    (h : analyticPerturbationCertificateReady w) :
    w.certificateBudget ≤ analyticPerturbationCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold analyticPerturbationCertificateSize
  omega

def sampleAnalyticPerturbationCertificate :
    AnalyticPerturbationCertificate where
  radiusWindow := 2
  derivativeDenominatorWindow := 2
  coefficientBudget := 4
  certificateBudget := 8
  slack := 1

example :
    analyticPerturbationCertificateReady
      sampleAnalyticPerturbationCertificate := by
  norm_num [analyticPerturbationCertificateReady,
    analyticPerturbationCertificateControlled,
    sampleAnalyticPerturbationCertificate]

example :
    sampleAnalyticPerturbationCertificate.certificateBudget ≤
      analyticPerturbationCertificateSize
        sampleAnalyticPerturbationCertificate := by
  apply analyticPerturbationCertificate_budget_le_size
  norm_num [analyticPerturbationCertificateReady,
    analyticPerturbationCertificateControlled,
    sampleAnalyticPerturbationCertificate]

/-- A refinement certificate with the perturbation budget separated from size. -/
structure AnalyticPerturbationRefinementCertificate where
  radiusWindow : ℕ
  derivativeDenominatorWindow : ℕ
  coefficientBudget : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def AnalyticPerturbationRefinementCertificate.parametersControlled
    (cert : AnalyticPerturbationRefinementCertificate) : Prop :=
  0 < cert.radiusWindow ∧ 0 < cert.derivativeDenominatorWindow

def AnalyticPerturbationRefinementCertificate.budgetControlled
    (cert : AnalyticPerturbationRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.radiusWindow + cert.derivativeDenominatorWindow +
      cert.coefficientBudget + cert.slack

def analyticPerturbationRefinementReady
    (cert : AnalyticPerturbationRefinementCertificate) : Prop :=
  cert.parametersControlled ∧ cert.budgetControlled

def AnalyticPerturbationRefinementCertificate.size
    (cert : AnalyticPerturbationRefinementCertificate) : ℕ :=
  cert.radiusWindow + cert.derivativeDenominatorWindow +
    cert.coefficientBudget + cert.slack

theorem analyticPerturbation_certificateBudgetWindow_le_size
    (cert : AnalyticPerturbationRefinementCertificate)
    (h : analyticPerturbationRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticPerturbationRefinementCertificate :
    AnalyticPerturbationRefinementCertificate where
  radiusWindow := 2
  derivativeDenominatorWindow := 2
  coefficientBudget := 4
  certificateBudgetWindow := 9
  slack := 1

example :
    analyticPerturbationRefinementReady
      sampleAnalyticPerturbationRefinementCertificate := by
  norm_num [analyticPerturbationRefinementReady,
    AnalyticPerturbationRefinementCertificate.parametersControlled,
    AnalyticPerturbationRefinementCertificate.budgetControlled,
    sampleAnalyticPerturbationRefinementCertificate]

example :
    sampleAnalyticPerturbationRefinementCertificate.certificateBudgetWindow ≤
      sampleAnalyticPerturbationRefinementCertificate.size := by
  apply analyticPerturbation_certificateBudgetWindow_le_size
  norm_num [analyticPerturbationRefinementReady,
    AnalyticPerturbationRefinementCertificate.parametersControlled,
    AnalyticPerturbationRefinementCertificate.budgetControlled,
    sampleAnalyticPerturbationRefinementCertificate]


structure PerturbationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PerturbationBudgetCertificate.controlled
    (c : PerturbationBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def PerturbationBudgetCertificate.budgetControlled
    (c : PerturbationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PerturbationBudgetCertificate.Ready
    (c : PerturbationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PerturbationBudgetCertificate.size
    (c : PerturbationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem perturbation_budgetCertificate_le_size
    (c : PerturbationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePerturbationBudgetCertificate :
    PerturbationBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : samplePerturbationBudgetCertificate.Ready := by
  constructor
  · norm_num [PerturbationBudgetCertificate.controlled,
      samplePerturbationBudgetCertificate]
  · norm_num [PerturbationBudgetCertificate.budgetControlled,
      samplePerturbationBudgetCertificate]

example :
    samplePerturbationBudgetCertificate.certificateBudgetWindow ≤
      samplePerturbationBudgetCertificate.size := by
  apply perturbation_budgetCertificate_le_size
  constructor
  · norm_num [PerturbationBudgetCertificate.controlled,
      samplePerturbationBudgetCertificate]
  · norm_num [PerturbationBudgetCertificate.budgetControlled,
      samplePerturbationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePerturbationBudgetCertificate.Ready := by
  constructor
  · norm_num [PerturbationBudgetCertificate.controlled,
      samplePerturbationBudgetCertificate]
  · norm_num [PerturbationBudgetCertificate.budgetControlled,
      samplePerturbationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePerturbationBudgetCertificate.certificateBudgetWindow ≤
      samplePerturbationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List PerturbationBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePerturbationBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    samplePerturbationBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.Perturbation
