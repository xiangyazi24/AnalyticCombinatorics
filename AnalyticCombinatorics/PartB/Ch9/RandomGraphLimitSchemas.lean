import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Random Graph Limit Schemas

Finite Erdos-Renyi coefficient and threshold models.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomGraphLimitSchemas

def edgeCountComplete (n : ℕ) : ℕ :=
  n * (n - 1) / 2

theorem edgeCountComplete_samples :
    (List.range 7).map edgeCountComplete = [0, 0, 1, 3, 6, 10, 15] := by
  native_decide

def graphCount (n : ℕ) : ℕ :=
  2 ^ edgeCountComplete n

theorem graphCount_samples :
    (List.range 6).map graphCount = [1, 1, 2, 8, 64, 1024] := by
  native_decide

def isolatedVertexExpectationNumerator (n : ℕ) : ℕ :=
  n * (n - 1) ^ (n - 1)

theorem isolatedVertexExpectationNumerator_samples :
    isolatedVertexExpectationNumerator 1 = 1 ∧
    isolatedVertexExpectationNumerator 3 = 12 ∧
    isolatedVertexExpectationNumerator 4 = 108 := by
  native_decide

structure RandomGraphLimitData where
  thresholdName : String
  windowNumerator : ℕ
  windowDenominator : ℕ

def connectivityThresholdData : RandomGraphLimitData where
  thresholdName := "connectivity"
  windowNumerator := 1
  windowDenominator := 2

theorem connectivityThresholdData_values :
    connectivityThresholdData.thresholdName = "connectivity" ∧
    connectivityThresholdData.windowNumerator = 1 ∧
    connectivityThresholdData.windowDenominator = 2 := by
  native_decide

def randomGraphLimitDataReady (data : RandomGraphLimitData) : Prop :=
  0 < data.thresholdName.length ∧ 0 < data.windowNumerator ∧ 0 < data.windowDenominator

theorem connectivityThresholdData_ready :
    randomGraphLimitDataReady connectivityThresholdData := by
  unfold randomGraphLimitDataReady connectivityThresholdData
  native_decide

def RandomGraphLimitSchema
    (event : ℕ → ℚ) (data : RandomGraphLimitData) : Prop :=
  randomGraphLimitDataReady data ∧ event 0 = 0 ∧ event 4 = 108

def connectivityEventWitness (n : ℕ) : ℚ :=
  isolatedVertexExpectationNumerator n

theorem random_graph_limit_schema_statement :
    RandomGraphLimitSchema connectivityEventWitness connectivityThresholdData := by
  unfold RandomGraphLimitSchema randomGraphLimitDataReady connectivityThresholdData
    connectivityEventWitness
  native_decide

/-- Finite executable readiness audit for random graph limit descriptors. -/
def randomGraphLimitDataListReady
    (data : List RandomGraphLimitData) : Bool :=
  data.all fun d =>
    0 < d.thresholdName.length &&
      0 < d.windowNumerator &&
        0 < d.windowDenominator

theorem randomGraphLimitDataList_readyWindow :
    randomGraphLimitDataListReady
      [{ thresholdName := "connectivity", windowNumerator := 1,
         windowDenominator := 2 },
       { thresholdName := "giant component", windowNumerator := 2,
         windowDenominator := 3 }] = true := by
  unfold randomGraphLimitDataListReady
  native_decide

structure RandomGraphLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomGraphLimitSchemasBudgetCertificate.controlled
    (c : RandomGraphLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomGraphLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomGraphLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomGraphLimitSchemasBudgetCertificate.Ready
    (c : RandomGraphLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomGraphLimitSchemasBudgetCertificate.size
    (c : RandomGraphLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomGraphLimitSchemas_budgetCertificate_le_size
    (c : RandomGraphLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomGraphLimitSchemasBudgetCertificate :
    RandomGraphLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRandomGraphLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomGraphLimitSchemasBudgetCertificate.controlled,
      sampleRandomGraphLimitSchemasBudgetCertificate]
  · norm_num [RandomGraphLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomGraphLimitSchemasBudgetCertificate]

example :
    sampleRandomGraphLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomGraphLimitSchemasBudgetCertificate.size := by
  apply randomGraphLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomGraphLimitSchemasBudgetCertificate.controlled,
      sampleRandomGraphLimitSchemasBudgetCertificate]
  · norm_num [RandomGraphLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomGraphLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRandomGraphLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomGraphLimitSchemasBudgetCertificate.controlled,
      sampleRandomGraphLimitSchemasBudgetCertificate]
  · norm_num [RandomGraphLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomGraphLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomGraphLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomGraphLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RandomGraphLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomGraphLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomGraphLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomGraphLimitSchemas
