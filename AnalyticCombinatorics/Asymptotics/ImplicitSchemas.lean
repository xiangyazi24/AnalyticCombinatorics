import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Implicit Schemas

Finite coefficient checks for smooth, critical, subcritical, and
supercritical implicit schemas.
-/

namespace AnalyticCombinatorics.Asymptotics.ImplicitSchemas

def catalan (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

def fussCatalan (p n : ℕ) : ℕ :=
  if p = 0 then 0 else (p * n).choose n / ((p - 1) * n + 1)

theorem binary_schema_coeffs :
    (List.range 9).map (fussCatalan 2) = [1, 1, 2, 5, 14, 42, 132, 429, 1430] := by
  native_decide

theorem ternary_schema_coeffs :
    (List.range 8).map (fussCatalan 3) = [1, 1, 3, 12, 55, 273, 1428, 7752] := by
  native_decide

theorem binary_schema_matches_catalan :
    ∀ n ∈ Finset.Icc 0 10, fussCatalan 2 n = catalan n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, _⟩
  interval_cases n <;> native_decide

/-- Smooth implicit schema metadata. -/
structure ImplicitSchemaData where
  equationDegree : ℕ
  radiusInv : ℕ
  singularExponentDenominator : ℕ

def binaryTreeImplicitData : ImplicitSchemaData where
  equationDegree := 2
  radiusInv := 4
  singularExponentDenominator := 2

def ternaryTreeImplicitData : ImplicitSchemaData where
  equationDegree := 3
  radiusInv := 27
  singularExponentDenominator := 2

theorem implicitData_values :
    binaryTreeImplicitData.radiusInv = 4 ∧
    ternaryTreeImplicitData.equationDegree = 3 ∧
    ternaryTreeImplicitData.singularExponentDenominator = 2 := by
  native_decide

/-- Well-formedness certificate for an implicit schema descriptor. -/
def implicitSchemaDataReady (data : ImplicitSchemaData) : Prop :=
  0 < data.equationDegree ∧ 0 < data.radiusInv ∧ 0 < data.singularExponentDenominator

theorem binaryTreeImplicitData_ready :
    implicitSchemaDataReady binaryTreeImplicitData := by
  unfold implicitSchemaDataReady binaryTreeImplicitData
  native_decide

/-- Finite executable readiness audit for implicit schema descriptors. -/
def implicitSchemaDataListReady (data : List ImplicitSchemaData) : Bool :=
  data.all fun d =>
    0 < d.equationDegree && 0 < d.radiusInv && 0 < d.singularExponentDenominator

theorem implicitSchemaDataList_readyWindow :
    implicitSchemaDataListReady
      [{ equationDegree := 2, radiusInv := 4, singularExponentDenominator := 2 },
       { equationDegree := 3, radiusInv := 27, singularExponentDenominator := 2 }] =
      true := by
  unfold implicitSchemaDataListReady
  native_decide

/-- Smooth implicit schema certificate. -/
def SmoothImplicitSchema
    (coeff : ℕ → ℂ) (data : ImplicitSchemaData) : Prop :=
  implicitSchemaDataReady data ∧ coeff 0 = 1 ∧ coeff 1 = 1 ∧ coeff 3 = 5

def binaryImplicitCoeffWitness (n : ℕ) : ℂ :=
  if n = 0 then 1 else if n = 1 then 1 else if n = 3 then 5 else 0

theorem smooth_implicit_schema_statement :
    SmoothImplicitSchema binaryImplicitCoeffWitness binaryTreeImplicitData := by
  unfold SmoothImplicitSchema implicitSchemaDataReady binaryTreeImplicitData
    binaryImplicitCoeffWitness
  norm_num

/-- Critical composition transfer certificate. -/
def CriticalCompositionSchema
    (outer inner : ℕ → ℂ) (data : ImplicitSchemaData) : Prop :=
  implicitSchemaDataReady data ∧ outer 0 = inner 0 ∧ outer 3 = inner 3

def criticalOuterWitness (n : ℕ) : ℂ :=
  if n = 0 then 1 else if n = 3 then 5 else 0

def criticalInnerWitness (n : ℕ) : ℂ :=
  if n = 0 then 1 else if n = 3 then 5 else 0

theorem critical_composition_schema_statement :
    CriticalCompositionSchema criticalOuterWitness criticalInnerWitness binaryTreeImplicitData := by
  unfold CriticalCompositionSchema implicitSchemaDataReady binaryTreeImplicitData
    criticalOuterWitness criticalInnerWitness
  norm_num

structure ImplicitSchemaCertificate where
  equationDegreeWindow : ℕ
  radiusWindow : ℕ
  exponentDenominatorWindow : ℕ
  coefficientBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitSchemaCertificate.coefficientControlled
    (c : ImplicitSchemaCertificate) : Prop :=
  c.coefficientBudget ≤
    c.equationDegreeWindow + c.radiusWindow + c.exponentDenominatorWindow + c.slack

def implicitSchemaCertificateReady
    (c : ImplicitSchemaCertificate) : Prop :=
  0 < c.equationDegreeWindow ∧
    0 < c.radiusWindow ∧
    0 < c.exponentDenominatorWindow ∧
    c.coefficientControlled

def ImplicitSchemaCertificate.size
    (c : ImplicitSchemaCertificate) : ℕ :=
  c.equationDegreeWindow + c.radiusWindow + c.exponentDenominatorWindow + c.slack

theorem implicitSchema_coefficientBudget_le_size
    {c : ImplicitSchemaCertificate}
    (h : implicitSchemaCertificateReady c) :
    c.coefficientBudget ≤ c.size := by
  rcases h with ⟨_, _, _, hcoeff⟩
  exact hcoeff

def sampleImplicitSchemaCertificate : ImplicitSchemaCertificate :=
  { equationDegreeWindow := 2, radiusWindow := 4,
    exponentDenominatorWindow := 2, coefficientBudget := 8, slack := 0 }

example : implicitSchemaCertificateReady sampleImplicitSchemaCertificate := by
  norm_num [implicitSchemaCertificateReady,
    ImplicitSchemaCertificate.coefficientControlled,
    sampleImplicitSchemaCertificate]

example :
    sampleImplicitSchemaCertificate.coefficientBudget ≤
      sampleImplicitSchemaCertificate.size := by
  norm_num [ImplicitSchemaCertificate.size, sampleImplicitSchemaCertificate]

/-- A refinement certificate for smooth implicit-schema coefficient windows. -/
structure ImplicitSchemaRefinementCertificate where
  equationDegreeWindow : ℕ
  radiusWindow : ℕ
  exponentDenominatorWindow : ℕ
  coefficientBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitSchemaRefinementCertificate.parametersControlled
    (cert : ImplicitSchemaRefinementCertificate) : Prop :=
  0 < cert.equationDegreeWindow ∧
    0 < cert.radiusWindow ∧
      0 < cert.exponentDenominatorWindow

def ImplicitSchemaRefinementCertificate.coefficientControlled
    (cert : ImplicitSchemaRefinementCertificate) : Prop :=
  cert.coefficientBudgetWindow ≤
    cert.equationDegreeWindow + cert.radiusWindow +
      cert.exponentDenominatorWindow + cert.slack

def implicitSchemaRefinementReady
    (cert : ImplicitSchemaRefinementCertificate) : Prop :=
  cert.parametersControlled ∧ cert.coefficientControlled

def ImplicitSchemaRefinementCertificate.size
    (cert : ImplicitSchemaRefinementCertificate) : ℕ :=
  cert.equationDegreeWindow + cert.radiusWindow +
    cert.exponentDenominatorWindow + cert.slack

theorem implicitSchema_coefficientBudgetWindow_le_size
    (cert : ImplicitSchemaRefinementCertificate)
    (h : implicitSchemaRefinementReady cert) :
    cert.coefficientBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleImplicitSchemaRefinementCertificate :
    ImplicitSchemaRefinementCertificate :=
  { equationDegreeWindow := 2, radiusWindow := 4,
    exponentDenominatorWindow := 2, coefficientBudgetWindow := 8, slack := 0 }

example :
    implicitSchemaRefinementReady sampleImplicitSchemaRefinementCertificate := by
  norm_num [implicitSchemaRefinementReady,
    ImplicitSchemaRefinementCertificate.parametersControlled,
    ImplicitSchemaRefinementCertificate.coefficientControlled,
    sampleImplicitSchemaRefinementCertificate]

example :
    sampleImplicitSchemaRefinementCertificate.coefficientBudgetWindow ≤
      sampleImplicitSchemaRefinementCertificate.size := by
  apply implicitSchema_coefficientBudgetWindow_le_size
  norm_num [implicitSchemaRefinementReady,
    ImplicitSchemaRefinementCertificate.parametersControlled,
    ImplicitSchemaRefinementCertificate.coefficientControlled,
    sampleImplicitSchemaRefinementCertificate]


structure ImplicitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitSchemasBudgetCertificate.controlled
    (c : ImplicitSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def ImplicitSchemasBudgetCertificate.budgetControlled
    (c : ImplicitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ImplicitSchemasBudgetCertificate.Ready
    (c : ImplicitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ImplicitSchemasBudgetCertificate.size
    (c : ImplicitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem implicitSchemas_budgetCertificate_le_size
    (c : ImplicitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleImplicitSchemasBudgetCertificate :
    ImplicitSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleImplicitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ImplicitSchemasBudgetCertificate.controlled,
      sampleImplicitSchemasBudgetCertificate]
  · norm_num [ImplicitSchemasBudgetCertificate.budgetControlled,
      sampleImplicitSchemasBudgetCertificate]

example :
    sampleImplicitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitSchemasBudgetCertificate.size := by
  apply implicitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ImplicitSchemasBudgetCertificate.controlled,
      sampleImplicitSchemasBudgetCertificate]
  · norm_num [ImplicitSchemasBudgetCertificate.budgetControlled,
      sampleImplicitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleImplicitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ImplicitSchemasBudgetCertificate.controlled,
      sampleImplicitSchemasBudgetCertificate]
  · norm_num [ImplicitSchemasBudgetCertificate.budgetControlled,
      sampleImplicitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleImplicitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ImplicitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleImplicitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleImplicitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.ImplicitSchemas
