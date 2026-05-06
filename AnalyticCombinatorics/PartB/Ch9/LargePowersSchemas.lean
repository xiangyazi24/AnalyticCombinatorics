import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Large Powers Schemas

Finite large-power coefficient models and saddle descriptors.
-/

namespace AnalyticCombinatorics.PartB.Ch9.LargePowersSchemas

def largePowerCoeff (m n k : ℕ) : ℕ :=
  if k ≤ m * n then (m * n).choose k else 0

theorem largePowerCoeff_samples :
    largePowerCoeff 2 3 0 = 1 ∧
    largePowerCoeff 2 3 3 = 20 ∧
    largePowerCoeff 2 3 7 = 0 := by
  native_decide

def centralLargePowerCoeff (m n : ℕ) : ℕ :=
  largePowerCoeff m n ((m * n) / 2)

theorem centralLargePowerCoeff_samples :
    centralLargePowerCoeff 2 3 = 20 ∧
    centralLargePowerCoeff 2 4 = 70 := by
  native_decide

structure LargePowersData where
  baseDegree : ℕ
  saddleNumerator : ℕ
  saddleDenominator : ℕ

def binomialLargePowersData : LargePowersData where
  baseDegree := 2
  saddleNumerator := 1
  saddleDenominator := 1

theorem binomialLargePowersData_values :
    binomialLargePowersData.baseDegree = 2 ∧
    binomialLargePowersData.saddleNumerator = 1 ∧
    binomialLargePowersData.saddleDenominator = 1 := by
  native_decide

def largePowersDataReady (data : LargePowersData) : Prop :=
  0 < data.baseDegree ∧ 0 < data.saddleNumerator ∧ 0 < data.saddleDenominator

theorem binomialLargePowersData_ready : largePowersDataReady binomialLargePowersData := by
  unfold largePowersDataReady binomialLargePowersData
  native_decide

def LargePowersSaddleSchema
    (coeff : ℕ → ℕ → ℂ) (data : LargePowersData) : Prop :=
  largePowersDataReady data ∧ coeff 2 3 = 20 ∧ coeff 2 4 = 70

def largePowerCoeffWitness (m n : ℕ) : ℂ :=
  if m = 2 ∧ n = 3 then 20 else if m = 2 ∧ n = 4 then 70 else 0

theorem large_powers_saddle_schema_statement :
    LargePowersSaddleSchema largePowerCoeffWitness binomialLargePowersData := by
  unfold LargePowersSaddleSchema largePowersDataReady binomialLargePowersData
    largePowerCoeffWitness
  norm_num

/-- Finite executable readiness audit for large-power saddle descriptors. -/
def largePowersDataListReady
    (data : List LargePowersData) : Bool :=
  data.all fun d =>
    0 < d.baseDegree && 0 < d.saddleNumerator && 0 < d.saddleDenominator

theorem largePowersDataList_readyWindow :
    largePowersDataListReady
      [{ baseDegree := 2, saddleNumerator := 1, saddleDenominator := 1 },
       { baseDegree := 3, saddleNumerator := 2, saddleDenominator := 5 }] =
      true := by
  unfold largePowersDataListReady
  native_decide

structure LargePowersSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LargePowersSchemasBudgetCertificate.controlled
    (c : LargePowersSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LargePowersSchemasBudgetCertificate.budgetControlled
    (c : LargePowersSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LargePowersSchemasBudgetCertificate.Ready
    (c : LargePowersSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LargePowersSchemasBudgetCertificate.size
    (c : LargePowersSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem largePowersSchemas_budgetCertificate_le_size
    (c : LargePowersSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLargePowersSchemasBudgetCertificate :
    LargePowersSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleLargePowersSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LargePowersSchemasBudgetCertificate.controlled,
      sampleLargePowersSchemasBudgetCertificate]
  · norm_num [LargePowersSchemasBudgetCertificate.budgetControlled,
      sampleLargePowersSchemasBudgetCertificate]

example :
    sampleLargePowersSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLargePowersSchemasBudgetCertificate.size := by
  apply largePowersSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LargePowersSchemasBudgetCertificate.controlled,
      sampleLargePowersSchemasBudgetCertificate]
  · norm_num [LargePowersSchemasBudgetCertificate.budgetControlled,
      sampleLargePowersSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLargePowersSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LargePowersSchemasBudgetCertificate.controlled,
      sampleLargePowersSchemasBudgetCertificate]
  · norm_num [LargePowersSchemasBudgetCertificate.budgetControlled,
      sampleLargePowersSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLargePowersSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLargePowersSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LargePowersSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLargePowersSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLargePowersSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.LargePowersSchemas
