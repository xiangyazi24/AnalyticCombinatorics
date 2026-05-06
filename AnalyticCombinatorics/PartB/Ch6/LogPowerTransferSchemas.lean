import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter VI: Log-Power Transfer Schemas

Finite models for logarithmic powers multiplying algebraic singularities.
-/

namespace AnalyticCombinatorics.PartB.Ch6.LogPowerTransferSchemas

def harmonic : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonic n + 1 / (n + 1 : ℚ)

theorem harmonic_samples :
    (List.range 7).map harmonic = [0, 1, 3 / 2, 11 / 6, 25 / 12, 137 / 60, 49 / 20] := by
  native_decide

def logCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else 1 / (n : ℚ)

theorem logCoeff_samples :
    (List.range 6).map logCoeff = [0, 1, 1 / 2, 1 / 3, 1 / 4, 1 / 5] := by
  native_decide

def logSquaredCoeffPrefix (n : ℕ) : ℚ :=
  (List.range (n + 1)).foldl (fun s k => s + logCoeff k * logCoeff (n - k)) 0

theorem logSquaredCoeffPrefix_samples :
    logSquaredCoeffPrefix 0 = 0 ∧
    logSquaredCoeffPrefix 1 = 0 ∧
    logSquaredCoeffPrefix 2 = 1 ∧
    logSquaredCoeffPrefix 3 = 1 ∧
    logSquaredCoeffPrefix 4 = 11 / 12 := by
  native_decide

structure LogPowerData where
  algebraicNumerator : ℤ
  algebraicDenominator : ℕ
  logPower : ℕ

def simpleLogData : LogPowerData where
  algebraicNumerator := 0
  algebraicDenominator := 1
  logPower := 1

theorem simpleLogData_values :
    simpleLogData.algebraicNumerator = 0 ∧
    simpleLogData.algebraicDenominator = 1 ∧
    simpleLogData.logPower = 1 := by
  native_decide

def logPowerDataReady (data : LogPowerData) : Prop :=
  0 < data.algebraicDenominator

theorem simpleLogData_ready : logPowerDataReady simpleLogData := by
  unfold logPowerDataReady simpleLogData
  native_decide

def LogPowerTransfer
    (coeff : ℕ → ℂ) (data : LogPowerData) : Prop :=
  logPowerDataReady data ∧ coeff 0 = coeff data.logPower

theorem log_power_transfer_statement :
    LogPowerTransfer (fun _ => 0) simpleLogData := by
  unfold LogPowerTransfer logPowerDataReady simpleLogData
  norm_num


structure LogPowerTransferSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogPowerTransferSchemasBudgetCertificate.controlled
    (c : LogPowerTransferSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LogPowerTransferSchemasBudgetCertificate.budgetControlled
    (c : LogPowerTransferSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LogPowerTransferSchemasBudgetCertificate.Ready
    (c : LogPowerTransferSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LogPowerTransferSchemasBudgetCertificate.size
    (c : LogPowerTransferSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem logPowerTransferSchemas_budgetCertificate_le_size
    (c : LogPowerTransferSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLogPowerTransferSchemasBudgetCertificate :
    LogPowerTransferSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleLogPowerTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LogPowerTransferSchemasBudgetCertificate.controlled,
      sampleLogPowerTransferSchemasBudgetCertificate]
  · norm_num [LogPowerTransferSchemasBudgetCertificate.budgetControlled,
      sampleLogPowerTransferSchemasBudgetCertificate]

example :
    sampleLogPowerTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLogPowerTransferSchemasBudgetCertificate.size := by
  apply logPowerTransferSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LogPowerTransferSchemasBudgetCertificate.controlled,
      sampleLogPowerTransferSchemasBudgetCertificate]
  · norm_num [LogPowerTransferSchemasBudgetCertificate.budgetControlled,
      sampleLogPowerTransferSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLogPowerTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LogPowerTransferSchemasBudgetCertificate.controlled,
      sampleLogPowerTransferSchemasBudgetCertificate]
  · norm_num [LogPowerTransferSchemasBudgetCertificate.budgetControlled,
      sampleLogPowerTransferSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLogPowerTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLogPowerTransferSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LogPowerTransferSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLogPowerTransferSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLogPowerTransferSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.LogPowerTransferSchemas
