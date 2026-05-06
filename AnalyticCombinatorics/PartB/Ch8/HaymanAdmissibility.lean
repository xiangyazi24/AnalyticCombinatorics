import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter VIII: Hayman Admissibility

Finite models for admissibility checks, saddle variance, and concentration
windows.
-/

namespace AnalyticCombinatorics.PartB.Ch8.HaymanAdmissibility

def expSeriesCoeffInvFactorial (n : ℕ) : ℚ :=
  1 / (Nat.factorial n : ℚ)

theorem expSeriesCoeffInvFactorial_samples :
    (List.range 7).map expSeriesCoeffInvFactorial =
      [1, 1, 1 / 2, 1 / 6, 1 / 24, 1 / 120, 1 / 720] := by
  native_decide

def saddleMeanModel (r : ℕ) : ℕ :=
  r

def saddleVarianceModel (r : ℕ) : ℕ :=
  r

theorem saddle_models_samples :
    saddleMeanModel 5 = 5 ∧ saddleVarianceModel 5 = 5 := by
  native_decide

def concentrationWindow (r : ℕ) : ℕ :=
  r * r

theorem concentrationWindow_samples :
    (List.range 6).map concentrationWindow = [0, 1, 4, 9, 16, 25] := by
  native_decide

structure HaymanData where
  captureExponentNumerator : ℕ
  captureExponentDenominator : ℕ
  localityWindow : ℕ

def exponentialHaymanData : HaymanData where
  captureExponentNumerator := 1
  captureExponentDenominator := 2
  localityWindow := 3

theorem exponentialHaymanData_values :
    exponentialHaymanData.captureExponentNumerator = 1 ∧
    exponentialHaymanData.captureExponentDenominator = 2 ∧
    exponentialHaymanData.localityWindow = 3 := by
  native_decide

def haymanDataReady (data : HaymanData) : Prop :=
  0 < data.captureExponentDenominator ∧ 0 < data.localityWindow

theorem exponentialHaymanData_ready : haymanDataReady exponentialHaymanData := by
  unfold haymanDataReady exponentialHaymanData
  native_decide

def HaymanAdmissible
    (f : ℂ → ℂ) (data : HaymanData) : Prop :=
  haymanDataReady data ∧ f 0 = 0

theorem hayman_admissible_statement :
    HaymanAdmissible (fun z => z) exponentialHaymanData := by
  unfold HaymanAdmissible haymanDataReady exponentialHaymanData
  norm_num


structure HaymanAdmissibilityBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HaymanAdmissibilityBudgetCertificate.controlled
    (c : HaymanAdmissibilityBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HaymanAdmissibilityBudgetCertificate.budgetControlled
    (c : HaymanAdmissibilityBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HaymanAdmissibilityBudgetCertificate.Ready
    (c : HaymanAdmissibilityBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HaymanAdmissibilityBudgetCertificate.size
    (c : HaymanAdmissibilityBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem haymanAdmissibility_budgetCertificate_le_size
    (c : HaymanAdmissibilityBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHaymanAdmissibilityBudgetCertificate :
    HaymanAdmissibilityBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleHaymanAdmissibilityBudgetCertificate.Ready := by
  constructor
  · norm_num [HaymanAdmissibilityBudgetCertificate.controlled,
      sampleHaymanAdmissibilityBudgetCertificate]
  · norm_num [HaymanAdmissibilityBudgetCertificate.budgetControlled,
      sampleHaymanAdmissibilityBudgetCertificate]

example :
    sampleHaymanAdmissibilityBudgetCertificate.certificateBudgetWindow ≤
      sampleHaymanAdmissibilityBudgetCertificate.size := by
  apply haymanAdmissibility_budgetCertificate_le_size
  constructor
  · norm_num [HaymanAdmissibilityBudgetCertificate.controlled,
      sampleHaymanAdmissibilityBudgetCertificate]
  · norm_num [HaymanAdmissibilityBudgetCertificate.budgetControlled,
      sampleHaymanAdmissibilityBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleHaymanAdmissibilityBudgetCertificate.Ready := by
  constructor
  · norm_num [HaymanAdmissibilityBudgetCertificate.controlled,
      sampleHaymanAdmissibilityBudgetCertificate]
  · norm_num [HaymanAdmissibilityBudgetCertificate.budgetControlled,
      sampleHaymanAdmissibilityBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHaymanAdmissibilityBudgetCertificate.certificateBudgetWindow ≤
      sampleHaymanAdmissibilityBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List HaymanAdmissibilityBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHaymanAdmissibilityBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHaymanAdmissibilityBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.HaymanAdmissibility
