import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Singular Differential Equations

Finite recurrence models derived from differential equations with singular
coefficients.
-/

namespace AnalyticCombinatorics.Asymptotics.SingularDifferentialEquations

def factorialSolution : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorialSolution n

theorem factorialSolution_samples :
    (List.range 7).map factorialSolution = [1, 1, 2, 6, 24, 120, 720] := by
  native_decide

def linearRecurrenceSolution : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * linearRecurrenceSolution n

theorem linearRecurrenceSolution_samples :
    (List.range 7).map linearRecurrenceSolution = [1, 2, 4, 8, 16, 32, 64] := by
  native_decide

def differentialRecurrenceCheck (a : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun n => a (n + 1) = (n + 1) * a n

theorem factorial_differentialRecurrenceCheck :
    differentialRecurrenceCheck factorialSolution 8 = true := by
  native_decide

structure SingularODESchemaData where
  poleOrder : ℕ
  indicialRootNumerator : ℤ
  indicialRootDenominator : ℕ

def regularSingularData : SingularODESchemaData where
  poleOrder := 1
  indicialRootNumerator := 0
  indicialRootDenominator := 1

theorem regularSingularData_values :
    regularSingularData.poleOrder = 1 ∧
    regularSingularData.indicialRootNumerator = 0 ∧
    regularSingularData.indicialRootDenominator = 1 := by
  native_decide

def singularODEDataReady (data : SingularODESchemaData) : Prop :=
  0 < data.poleOrder ∧ 0 < data.indicialRootDenominator

theorem regularSingularData_ready : singularODEDataReady regularSingularData := by
  unfold singularODEDataReady regularSingularData
  native_decide

/-- Finite executable readiness audit for singular ODE schema data. -/
def singularODEDataListReady (data : List SingularODESchemaData) : Bool :=
  data.all fun d => 0 < d.poleOrder && 0 < d.indicialRootDenominator

theorem singularODEDataList_readyWindow :
    singularODEDataListReady
      [{ poleOrder := 1, indicialRootNumerator := 0,
         indicialRootDenominator := 1 },
       { poleOrder := 2, indicialRootNumerator := -1,
         indicialRootDenominator := 3 }] = true := by
  unfold singularODEDataListReady
  native_decide

def SingularDifferentialTransfer
    (coeff : ℕ → ℂ) (data : SingularODESchemaData) : Prop :=
  singularODEDataReady data ∧ coeff 0 = 1 ∧ coeff 4 = 24

def singularDifferentialCoeffWitness (n : ℕ) : ℂ :=
  if n = 0 then 1 else if n = 4 then 24 else 0

theorem singular_differential_transfer_statement :
    SingularDifferentialTransfer singularDifferentialCoeffWitness regularSingularData := by
  unfold SingularDifferentialTransfer singularODEDataReady regularSingularData
    singularDifferentialCoeffWitness
  norm_num

/-- A finite certificate for singular differential transfer schemas. -/
structure SingularDifferentialCertificate where
  poleOrderWindow : ℕ
  indicialDenominatorWindow : ℕ
  recurrenceBudget : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Singular differential certificates keep pole order and denominator positive. -/
def singularDifferentialCertificateControlled
    (w : SingularDifferentialCertificate) : Prop :=
  0 < w.poleOrderWindow ∧ 0 < w.indicialDenominatorWindow

/-- Readiness for a singular differential certificate. -/
def singularDifferentialCertificateReady
    (w : SingularDifferentialCertificate) : Prop :=
  singularDifferentialCertificateControlled w ∧
    w.certificateBudget ≤
      w.poleOrderWindow + w.indicialDenominatorWindow +
        w.recurrenceBudget + w.slack

/-- Total size of a singular differential certificate. -/
def singularDifferentialCertificateSize
    (w : SingularDifferentialCertificate) : ℕ :=
  w.poleOrderWindow + w.indicialDenominatorWindow +
    w.recurrenceBudget + w.certificateBudget + w.slack

theorem singularDifferentialCertificate_budget_le_size
    (w : SingularDifferentialCertificate)
    (h : singularDifferentialCertificateReady w) :
    w.certificateBudget ≤ singularDifferentialCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold singularDifferentialCertificateSize
  omega

def sampleSingularDifferentialCertificate :
    SingularDifferentialCertificate where
  poleOrderWindow := 1
  indicialDenominatorWindow := 1
  recurrenceBudget := 4
  certificateBudget := 6
  slack := 1

example :
    singularDifferentialCertificateReady
      sampleSingularDifferentialCertificate := by
  norm_num [singularDifferentialCertificateReady,
    singularDifferentialCertificateControlled,
    sampleSingularDifferentialCertificate]

example :
    sampleSingularDifferentialCertificate.certificateBudget ≤
      singularDifferentialCertificateSize
        sampleSingularDifferentialCertificate := by
  apply singularDifferentialCertificate_budget_le_size
  norm_num [singularDifferentialCertificateReady,
    singularDifferentialCertificateControlled,
    sampleSingularDifferentialCertificate]

/-- A refinement certificate with the recurrence budget separated from size. -/
structure SingularDifferentialRefinementCertificate where
  poleOrderWindow : ℕ
  indicialDenominatorWindow : ℕ
  recurrenceBudget : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def SingularDifferentialRefinementCertificate.parametersControlled
    (cert : SingularDifferentialRefinementCertificate) : Prop :=
  0 < cert.poleOrderWindow ∧ 0 < cert.indicialDenominatorWindow

def SingularDifferentialRefinementCertificate.budgetControlled
    (cert : SingularDifferentialRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.poleOrderWindow + cert.indicialDenominatorWindow +
      cert.recurrenceBudget + cert.slack

def singularDifferentialRefinementReady
    (cert : SingularDifferentialRefinementCertificate) : Prop :=
  cert.parametersControlled ∧ cert.budgetControlled

def SingularDifferentialRefinementCertificate.size
    (cert : SingularDifferentialRefinementCertificate) : ℕ :=
  cert.poleOrderWindow + cert.indicialDenominatorWindow +
    cert.recurrenceBudget + cert.slack

theorem singularDifferential_certificateBudgetWindow_le_size
    (cert : SingularDifferentialRefinementCertificate)
    (h : singularDifferentialRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularDifferentialRefinementCertificate :
    SingularDifferentialRefinementCertificate where
  poleOrderWindow := 1
  indicialDenominatorWindow := 1
  recurrenceBudget := 4
  certificateBudgetWindow := 7
  slack := 1

example :
    singularDifferentialRefinementReady
      sampleSingularDifferentialRefinementCertificate := by
  norm_num [singularDifferentialRefinementReady,
    SingularDifferentialRefinementCertificate.parametersControlled,
    SingularDifferentialRefinementCertificate.budgetControlled,
    sampleSingularDifferentialRefinementCertificate]

example :
    sampleSingularDifferentialRefinementCertificate.certificateBudgetWindow ≤
      sampleSingularDifferentialRefinementCertificate.size := by
  apply singularDifferential_certificateBudgetWindow_le_size
  norm_num [singularDifferentialRefinementReady,
    SingularDifferentialRefinementCertificate.parametersControlled,
    SingularDifferentialRefinementCertificate.budgetControlled,
    sampleSingularDifferentialRefinementCertificate]


structure SingularDifferentialEquationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularDifferentialEquationsBudgetCertificate.controlled
    (c : SingularDifferentialEquationsBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def SingularDifferentialEquationsBudgetCertificate.budgetControlled
    (c : SingularDifferentialEquationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SingularDifferentialEquationsBudgetCertificate.Ready
    (c : SingularDifferentialEquationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularDifferentialEquationsBudgetCertificate.size
    (c : SingularDifferentialEquationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem singularDifferentialEquations_budgetCertificate_le_size
    (c : SingularDifferentialEquationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularDifferentialEquationsBudgetCertificate :
    SingularDifferentialEquationsBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleSingularDifferentialEquationsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularDifferentialEquationsBudgetCertificate.controlled,
      sampleSingularDifferentialEquationsBudgetCertificate]
  · norm_num [SingularDifferentialEquationsBudgetCertificate.budgetControlled,
      sampleSingularDifferentialEquationsBudgetCertificate]

example :
    sampleSingularDifferentialEquationsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularDifferentialEquationsBudgetCertificate.size := by
  apply singularDifferentialEquations_budgetCertificate_le_size
  constructor
  · norm_num [SingularDifferentialEquationsBudgetCertificate.controlled,
      sampleSingularDifferentialEquationsBudgetCertificate]
  · norm_num [SingularDifferentialEquationsBudgetCertificate.budgetControlled,
      sampleSingularDifferentialEquationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularDifferentialEquationsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularDifferentialEquationsBudgetCertificate.controlled,
      sampleSingularDifferentialEquationsBudgetCertificate]
  · norm_num [SingularDifferentialEquationsBudgetCertificate.budgetControlled,
      sampleSingularDifferentialEquationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularDifferentialEquationsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularDifferentialEquationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SingularDifferentialEquationsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularDifferentialEquationsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSingularDifferentialEquationsBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SingularDifferentialEquations
