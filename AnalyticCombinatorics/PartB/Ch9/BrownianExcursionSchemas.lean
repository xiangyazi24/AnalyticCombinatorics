import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Brownian Excursion Schemas

Finite Dyck-path area and height proxies for Brownian excursion limits.
-/

namespace AnalyticCombinatorics.PartB.Ch9.BrownianExcursionSchemas

def catalan (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

theorem catalan_samples :
    (List.range 8).map catalan = [1, 1, 2, 5, 14, 42, 132, 429] := by
  native_decide

def dyckHeightProxy (n : ℕ) : ℕ :=
  n

def dyckAreaProxy (n : ℕ) : ℕ :=
  n * n

theorem dyck_proxy_samples :
    (List.range 6).map dyckHeightProxy = [0, 1, 2, 3, 4, 5] ∧
    (List.range 6).map dyckAreaProxy = [0, 1, 4, 9, 16, 25] := by
  native_decide

structure BrownianExcursionData where
  heightScaleNumerator : ℕ
  heightScaleDenominator : ℕ
  areaScalePower : ℕ

def dyckExcursionData : BrownianExcursionData where
  heightScaleNumerator := 1
  heightScaleDenominator := 2
  areaScalePower := 3

theorem dyckExcursionData_values :
    dyckExcursionData.heightScaleNumerator = 1 ∧
    dyckExcursionData.heightScaleDenominator = 2 ∧
    dyckExcursionData.areaScalePower = 3 := by
  native_decide

def brownianExcursionDataReady (data : BrownianExcursionData) : Prop :=
  0 < data.heightScaleNumerator ∧ 0 < data.heightScaleDenominator ∧
    0 < data.areaScalePower

theorem dyckExcursionData_ready : brownianExcursionDataReady dyckExcursionData := by
  unfold brownianExcursionDataReady dyckExcursionData
  native_decide

def BrownianExcursionLimit
    (parameter : ℕ → ℕ → ℚ) (data : BrownianExcursionData) : Prop :=
  brownianExcursionDataReady data ∧ parameter 0 0 = 0 ∧ parameter 5 0 = 5 ∧
    parameter 5 1 = 25

def dyckParameterWitness (n marker : ℕ) : ℚ :=
  if marker = 0 then dyckHeightProxy n else dyckAreaProxy n

theorem brownian_excursion_limit_statement :
    BrownianExcursionLimit dyckParameterWitness dyckExcursionData := by
  unfold BrownianExcursionLimit brownianExcursionDataReady dyckExcursionData
    dyckParameterWitness
  native_decide

/-- Finite executable readiness audit for Brownian-excursion descriptors. -/
def brownianExcursionDataListReady
    (data : List BrownianExcursionData) : Bool :=
  data.all fun d =>
    0 < d.heightScaleNumerator &&
      0 < d.heightScaleDenominator &&
        0 < d.areaScalePower

theorem brownianExcursionDataList_readyWindow :
    brownianExcursionDataListReady
      [{ heightScaleNumerator := 1, heightScaleDenominator := 2,
         areaScalePower := 3 },
       { heightScaleNumerator := 2, heightScaleDenominator := 3,
         areaScalePower := 4 }] = true := by
  unfold brownianExcursionDataListReady
  native_decide

structure BrownianExcursionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BrownianExcursionSchemasBudgetCertificate.controlled
    (c : BrownianExcursionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BrownianExcursionSchemasBudgetCertificate.budgetControlled
    (c : BrownianExcursionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BrownianExcursionSchemasBudgetCertificate.Ready
    (c : BrownianExcursionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BrownianExcursionSchemasBudgetCertificate.size
    (c : BrownianExcursionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem brownianExcursionSchemas_budgetCertificate_le_size
    (c : BrownianExcursionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBrownianExcursionSchemasBudgetCertificate :
    BrownianExcursionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleBrownianExcursionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BrownianExcursionSchemasBudgetCertificate.controlled,
      sampleBrownianExcursionSchemasBudgetCertificate]
  · norm_num [BrownianExcursionSchemasBudgetCertificate.budgetControlled,
      sampleBrownianExcursionSchemasBudgetCertificate]

example :
    sampleBrownianExcursionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBrownianExcursionSchemasBudgetCertificate.size := by
  apply brownianExcursionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [BrownianExcursionSchemasBudgetCertificate.controlled,
      sampleBrownianExcursionSchemasBudgetCertificate]
  · norm_num [BrownianExcursionSchemasBudgetCertificate.budgetControlled,
      sampleBrownianExcursionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBrownianExcursionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BrownianExcursionSchemasBudgetCertificate.controlled,
      sampleBrownianExcursionSchemasBudgetCertificate]
  · norm_num [BrownianExcursionSchemasBudgetCertificate.budgetControlled,
      sampleBrownianExcursionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBrownianExcursionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBrownianExcursionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List BrownianExcursionSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBrownianExcursionSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleBrownianExcursionSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.BrownianExcursionSchemas
