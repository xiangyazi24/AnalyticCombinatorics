import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter VI: Polylogarithm Transfer

Finite polylogarithm coefficient models and singular-transfer descriptors.
-/

namespace AnalyticCombinatorics.PartB.Ch6.PolylogTransfer

def polylogCoeff (s n : ℕ) : ℚ :=
  if n = 0 then 0 else 1 / ((n : ℚ) ^ s)

theorem polylogCoeff_s1 :
    (List.range 6).map (polylogCoeff 1) = [0, 1, 1 / 2, 1 / 3, 1 / 4, 1 / 5] := by
  native_decide

theorem polylogCoeff_s2 :
    (List.range 6).map (polylogCoeff 2) = [0, 1, 1 / 4, 1 / 9, 1 / 16, 1 / 25] := by
  native_decide

def polylogPrefix (s N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl (fun acc n => acc + polylogCoeff s n) 0

theorem polylogPrefix_samples :
    polylogPrefix 1 3 = 11 / 6 ∧
    polylogPrefix 2 3 = 49 / 36 := by
  native_decide

structure PolylogSingularData where
  order : ℕ
  logPower : ℕ

def dilogarithmSingularData : PolylogSingularData where
  order := 2
  logPower := 1

theorem dilogarithmSingularData_values :
    dilogarithmSingularData.order = 2 ∧ dilogarithmSingularData.logPower = 1 := by
  native_decide

def polylogSingularDataReady (data : PolylogSingularData) : Prop :=
  0 < data.order

theorem dilogarithmSingularData_ready :
    polylogSingularDataReady dilogarithmSingularData := by
  unfold polylogSingularDataReady dilogarithmSingularData
  native_decide

def PolylogTransferSchema
    (coeff : ℕ → ℂ) (data : PolylogSingularData) : Prop :=
  polylogSingularDataReady data ∧ coeff 0 = coeff data.logPower

theorem polylog_transfer_schema_statement :
    PolylogTransferSchema (fun _ => 0) dilogarithmSingularData := by
  unfold PolylogTransferSchema polylogSingularDataReady dilogarithmSingularData
  norm_num


structure PolylogTransferBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PolylogTransferBudgetCertificate.controlled
    (c : PolylogTransferBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PolylogTransferBudgetCertificate.budgetControlled
    (c : PolylogTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PolylogTransferBudgetCertificate.Ready
    (c : PolylogTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PolylogTransferBudgetCertificate.size
    (c : PolylogTransferBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem polylogTransfer_budgetCertificate_le_size
    (c : PolylogTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePolylogTransferBudgetCertificate :
    PolylogTransferBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePolylogTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [PolylogTransferBudgetCertificate.controlled,
      samplePolylogTransferBudgetCertificate]
  · norm_num [PolylogTransferBudgetCertificate.budgetControlled,
      samplePolylogTransferBudgetCertificate]

example :
    samplePolylogTransferBudgetCertificate.certificateBudgetWindow ≤
      samplePolylogTransferBudgetCertificate.size := by
  apply polylogTransfer_budgetCertificate_le_size
  constructor
  · norm_num [PolylogTransferBudgetCertificate.controlled,
      samplePolylogTransferBudgetCertificate]
  · norm_num [PolylogTransferBudgetCertificate.budgetControlled,
      samplePolylogTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePolylogTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [PolylogTransferBudgetCertificate.controlled,
      samplePolylogTransferBudgetCertificate]
  · norm_num [PolylogTransferBudgetCertificate.budgetControlled,
      samplePolylogTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePolylogTransferBudgetCertificate.certificateBudgetWindow ≤
      samplePolylogTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PolylogTransferBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePolylogTransferBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePolylogTransferBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.PolylogTransfer
