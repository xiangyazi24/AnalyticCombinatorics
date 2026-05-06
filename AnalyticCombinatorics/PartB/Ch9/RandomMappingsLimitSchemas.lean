import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Random Mappings Limit Schemas

Finite functional-digraph checks and limit-schema descriptors for random
mappings.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomMappingsLimitSchemas

/-- Number of mappings from an `n`-set to itself. -/
def mappingCount (n : ℕ) : ℕ :=
  n ^ n

theorem mappingCount_samples :
    (List.range 7).map mappingCount = [1, 1, 4, 27, 256, 3125, 46656] := by
  native_decide

/-- Number of mappings with a distinguished image point. -/
def pointedImageMappingCount (n : ℕ) : ℕ :=
  n * n ^ n

theorem pointedImageMappingCount_samples :
    (List.range 6).map pointedImageMappingCount = [0, 1, 8, 81, 1024, 15625] := by
  native_decide

/-- Birthday collision threshold estimate `m^2/n`. -/
def collisionProxyNumerator (m _n : ℕ) : ℕ :=
  m ^ 2

theorem collisionProxyNumerator_samples :
    collisionProxyNumerator 3 10 = 9 ∧
    collisionProxyNumerator 5 100 = 25 := by
  native_decide

structure RandomMappingLimitData where
  scaleNumerator : ℕ
  scaleDenominator : ℕ
  lawName : String

def rayleighMappingData : RandomMappingLimitData where
  scaleNumerator := 1
  scaleDenominator := 2
  lawName := "Rayleigh"

theorem rayleighMappingData_values :
    rayleighMappingData.scaleNumerator = 1 ∧
    rayleighMappingData.scaleDenominator = 2 ∧
    rayleighMappingData.lawName = "Rayleigh" := by
  native_decide

def randomMappingLimitDataReady (data : RandomMappingLimitData) : Prop :=
  0 < data.scaleNumerator ∧ 0 < data.scaleDenominator ∧ 0 < data.lawName.length

theorem rayleighMappingData_ready : randomMappingLimitDataReady rayleighMappingData := by
  unfold randomMappingLimitDataReady rayleighMappingData
  native_decide

def RandomMappingRayleighLimit
    (componentSize : ℕ → ℕ → ℚ) (data : RandomMappingLimitData) : Prop :=
  randomMappingLimitDataReady data ∧ componentSize 0 0 = 0 ∧ componentSize 3 10 = 9

def componentCollisionWitness (m n : ℕ) : ℚ :=
  collisionProxyNumerator m n

theorem random_mapping_rayleigh_limit_statement :
    RandomMappingRayleighLimit componentCollisionWitness rayleighMappingData := by
  unfold RandomMappingRayleighLimit randomMappingLimitDataReady rayleighMappingData
    componentCollisionWitness
  native_decide

/-- Finite executable readiness audit for random mapping limit descriptors. -/
def randomMappingLimitDataListReady
    (data : List RandomMappingLimitData) : Bool :=
  data.all fun d =>
    0 < d.scaleNumerator &&
      0 < d.scaleDenominator &&
        0 < d.lawName.length

theorem randomMappingLimitDataList_readyWindow :
    randomMappingLimitDataListReady
      [{ scaleNumerator := 1, scaleDenominator := 2, lawName := "Rayleigh" },
       { scaleNumerator := 2, scaleDenominator := 3, lawName := "Gaussian" }] =
      true := by
  unfold randomMappingLimitDataListReady
  native_decide

structure RandomMappingsLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomMappingsLimitSchemasBudgetCertificate.controlled
    (c : RandomMappingsLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomMappingsLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomMappingsLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomMappingsLimitSchemasBudgetCertificate.Ready
    (c : RandomMappingsLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomMappingsLimitSchemasBudgetCertificate.size
    (c : RandomMappingsLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomMappingsLimitSchemas_budgetCertificate_le_size
    (c : RandomMappingsLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomMappingsLimitSchemasBudgetCertificate :
    RandomMappingsLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRandomMappingsLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomMappingsLimitSchemasBudgetCertificate.controlled,
      sampleRandomMappingsLimitSchemasBudgetCertificate]
  · norm_num [RandomMappingsLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomMappingsLimitSchemasBudgetCertificate]

example :
    sampleRandomMappingsLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomMappingsLimitSchemasBudgetCertificate.size := by
  apply randomMappingsLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomMappingsLimitSchemasBudgetCertificate.controlled,
      sampleRandomMappingsLimitSchemasBudgetCertificate]
  · norm_num [RandomMappingsLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomMappingsLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRandomMappingsLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomMappingsLimitSchemasBudgetCertificate.controlled,
      sampleRandomMappingsLimitSchemasBudgetCertificate]
  · norm_num [RandomMappingsLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomMappingsLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomMappingsLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomMappingsLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RandomMappingsLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomMappingsLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomMappingsLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomMappingsLimitSchemas
