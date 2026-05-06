import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter VIII: Saddle Local Limit

Finite saddle-point mass checks for local Gaussian approximations.
-/

namespace AnalyticCombinatorics.PartB.Ch8.SaddleLocalLimit

def centralBinom (n : ℕ) : ℕ :=
  (2 * n).choose n

theorem centralBinom_samples :
    (List.range 7).map centralBinom = [1, 2, 6, 20, 70, 252, 924] := by
  native_decide

def localRatio (n k : ℕ) : ℚ :=
  ((2 * n).choose (n - k) : ℚ) / (centralBinom n : ℚ)

theorem localRatio_n5 :
    localRatio 5 0 = 1 ∧
    localRatio 5 1 = 5 / 6 ∧
    localRatio 5 2 = 10 / 21 := by
  native_decide

def saddleVariance (n : ℕ) : ℚ :=
  n / 2

theorem saddleVariance_samples :
    saddleVariance 2 = 1 ∧ saddleVariance 5 = 5 / 2 := by
  native_decide

structure SaddleLocalData where
  centerNumerator : ℕ
  centerDenominator : ℕ
  varianceNumerator : ℕ
  varianceDenominator : ℕ

def binomialSaddleLocalData : SaddleLocalData where
  centerNumerator := 1
  centerDenominator := 2
  varianceNumerator := 1
  varianceDenominator := 2

theorem binomialSaddleLocalData_values :
    binomialSaddleLocalData.centerNumerator = 1 ∧
    binomialSaddleLocalData.centerDenominator = 2 ∧
    binomialSaddleLocalData.varianceDenominator = 2 := by
  native_decide

def saddleLocalDataReady (data : SaddleLocalData) : Prop :=
  0 < data.centerDenominator ∧ 0 < data.varianceNumerator ∧ 0 < data.varianceDenominator

theorem binomialSaddleLocalData_ready :
    saddleLocalDataReady binomialSaddleLocalData := by
  unfold saddleLocalDataReady binomialSaddleLocalData
  native_decide

def SaddleLocalLimitSchema
    (mass : ℕ → ℕ → ℚ) (data : SaddleLocalData) : Prop :=
  saddleLocalDataReady data ∧ mass 5 0 = 1

theorem saddle_local_limit_schema_statement :
    SaddleLocalLimitSchema (fun n k => localRatio n k) binomialSaddleLocalData := by
  unfold SaddleLocalLimitSchema saddleLocalDataReady binomialSaddleLocalData
  native_decide


structure SaddleLocalLimitBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleLocalLimitBudgetCertificate.controlled
    (c : SaddleLocalLimitBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SaddleLocalLimitBudgetCertificate.budgetControlled
    (c : SaddleLocalLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SaddleLocalLimitBudgetCertificate.Ready
    (c : SaddleLocalLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SaddleLocalLimitBudgetCertificate.size
    (c : SaddleLocalLimitBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem saddleLocalLimit_budgetCertificate_le_size
    (c : SaddleLocalLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSaddleLocalLimitBudgetCertificate :
    SaddleLocalLimitBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSaddleLocalLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddleLocalLimitBudgetCertificate.controlled,
      sampleSaddleLocalLimitBudgetCertificate]
  · norm_num [SaddleLocalLimitBudgetCertificate.budgetControlled,
      sampleSaddleLocalLimitBudgetCertificate]

example :
    sampleSaddleLocalLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleLocalLimitBudgetCertificate.size := by
  apply saddleLocalLimit_budgetCertificate_le_size
  constructor
  · norm_num [SaddleLocalLimitBudgetCertificate.controlled,
      sampleSaddleLocalLimitBudgetCertificate]
  · norm_num [SaddleLocalLimitBudgetCertificate.budgetControlled,
      sampleSaddleLocalLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSaddleLocalLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddleLocalLimitBudgetCertificate.controlled,
      sampleSaddleLocalLimitBudgetCertificate]
  · norm_num [SaddleLocalLimitBudgetCertificate.budgetControlled,
      sampleSaddleLocalLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddleLocalLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleLocalLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SaddleLocalLimitBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSaddleLocalLimitBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSaddleLocalLimitBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.SaddleLocalLimit
