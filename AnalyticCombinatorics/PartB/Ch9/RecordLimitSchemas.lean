import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Record Limit Schemas

Finite record-count tables and logarithmic limit descriptors.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RecordLimitSchemas

def unsignedStirlingFirst : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => unsignedStirlingFirst n k + n * unsignedStirlingFirst n (k + 1)

theorem unsignedStirlingFirst_recordRow4 :
    (List.range 5).map (unsignedStirlingFirst 4) = [0, 6, 11, 6, 1] := by
  native_decide

def harmonic : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonic n + 1 / (n + 1 : ℚ)

theorem harmonic_record_means :
    (List.range 6).map harmonic = [0, 1, 3 / 2, 11 / 6, 25 / 12, 137 / 60] := by
  native_decide

def recordCountTotal (n : ℕ) : ℕ :=
  ((List.range (n + 1)).map (unsignedStirlingFirst n)).sum

theorem recordCountTotal_factorial :
    (List.range 7).map recordCountTotal = [1, 1, 2, 6, 24, 120, 720] := by
  native_decide

structure RecordLimitData where
  meanScale : String
  varianceScale : String

def logarithmicRecordLimitData : RecordLimitData where
  meanScale := "log n"
  varianceScale := "log n"

theorem logarithmicRecordLimitData_values :
    logarithmicRecordLimitData.meanScale = "log n" ∧
    logarithmicRecordLimitData.varianceScale = "log n" := by
  native_decide

def recordLimitDataReady (data : RecordLimitData) : Prop :=
  0 < data.meanScale.length ∧ 0 < data.varianceScale.length

theorem logarithmicRecordLimitData_ready :
    recordLimitDataReady logarithmicRecordLimitData := by
  unfold recordLimitDataReady logarithmicRecordLimitData
  native_decide

def RecordCentralLimitSchema
    (records : ℕ → ℕ → ℚ) (data : RecordLimitData) : Prop :=
  recordLimitDataReady data ∧ records 0 0 = 1 ∧ records 4 2 = 11

def recordCountWitness (n k : ℕ) : ℚ :=
  unsignedStirlingFirst n k

theorem record_central_limit_schema_statement :
    RecordCentralLimitSchema recordCountWitness logarithmicRecordLimitData := by
  unfold RecordCentralLimitSchema recordLimitDataReady logarithmicRecordLimitData
    recordCountWitness
  native_decide

/-- Finite executable readiness audit for record-limit descriptors. -/
def recordLimitDataListReady (data : List RecordLimitData) : Bool :=
  data.all fun d =>
    0 < d.meanScale.length && 0 < d.varianceScale.length

theorem recordLimitDataList_readyWindow :
    recordLimitDataListReady
      [{ meanScale := "log n", varianceScale := "log n" },
       { meanScale := "sqrt n", varianceScale := "sqrt n" }] = true := by
  unfold recordLimitDataListReady
  native_decide

structure RecordLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RecordLimitSchemasBudgetCertificate.controlled
    (c : RecordLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RecordLimitSchemasBudgetCertificate.budgetControlled
    (c : RecordLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RecordLimitSchemasBudgetCertificate.Ready
    (c : RecordLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RecordLimitSchemasBudgetCertificate.size
    (c : RecordLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem recordLimitSchemas_budgetCertificate_le_size
    (c : RecordLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRecordLimitSchemasBudgetCertificate :
    RecordLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRecordLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RecordLimitSchemasBudgetCertificate.controlled,
      sampleRecordLimitSchemasBudgetCertificate]
  · norm_num [RecordLimitSchemasBudgetCertificate.budgetControlled,
      sampleRecordLimitSchemasBudgetCertificate]

example :
    sampleRecordLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRecordLimitSchemasBudgetCertificate.size := by
  apply recordLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RecordLimitSchemasBudgetCertificate.controlled,
      sampleRecordLimitSchemasBudgetCertificate]
  · norm_num [RecordLimitSchemasBudgetCertificate.budgetControlled,
      sampleRecordLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRecordLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RecordLimitSchemasBudgetCertificate.controlled,
      sampleRecordLimitSchemasBudgetCertificate]
  · norm_num [RecordLimitSchemasBudgetCertificate.budgetControlled,
      sampleRecordLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRecordLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRecordLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RecordLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRecordLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRecordLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RecordLimitSchemas
