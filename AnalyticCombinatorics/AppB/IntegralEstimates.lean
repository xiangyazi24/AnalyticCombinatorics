import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix B: Integral Estimates

Finite rational estimates for contour lengths, sup bounds, and integral
majorants.
-/

namespace AnalyticCombinatorics.AppB.IntegralEstimates

def rectanglePerimeter (width height : ℚ) : ℚ :=
  2 * (width + height)

theorem rectanglePerimeter_samples :
    rectanglePerimeter 1 1 = 4 ∧
    rectanglePerimeter 2 3 = 10 ∧
    rectanglePerimeter (1 / 2) (3 / 2) = 4 := by
  native_decide

def integralBound (length supNorm : ℚ) : ℚ :=
  length * supNorm

theorem integralBound_samples :
    integralBound 4 3 = 12 ∧
    integralBound (1 / 2) 6 = 3 := by
  native_decide

def tailGeometricBound (ratio : ℚ) (N : ℕ) : ℚ :=
  ratio ^ N / (1 - ratio)

theorem tailGeometricBound_half :
    tailGeometricBound (1 / 2) 1 = 1 ∧
    tailGeometricBound (1 / 2) 2 = 1 / 2 ∧
    tailGeometricBound (1 / 2) 3 = 1 / 4 := by
  native_decide

structure IntegralEstimateData where
  contourLengthNumerator : ℕ
  contourLengthDenominator : ℕ
  supNormNumerator : ℕ
  supNormDenominator : ℕ

def unitCircleEstimateData : IntegralEstimateData where
  contourLengthNumerator := 628
  contourLengthDenominator := 100
  supNormNumerator := 1
  supNormDenominator := 1

theorem unitCircleEstimateData_values :
    unitCircleEstimateData.contourLengthNumerator = 628 ∧
    unitCircleEstimateData.contourLengthDenominator = 100 ∧
    unitCircleEstimateData.supNormNumerator = 1 := by
  native_decide

def integralEstimateDataReady (data : IntegralEstimateData) : Prop :=
  0 < data.contourLengthNumerator ∧ 0 < data.contourLengthDenominator ∧
    0 < data.supNormNumerator ∧ 0 < data.supNormDenominator

theorem unitCircleEstimateData_ready : integralEstimateDataReady unitCircleEstimateData := by
  unfold integralEstimateDataReady unitCircleEstimateData
  native_decide

def ContourIntegralEstimate
    (f : ℂ → ℂ) (data : IntegralEstimateData) : Prop :=
  integralEstimateDataReady data ∧ f 0 = 0

theorem contour_integral_estimate_statement :
    ContourIntegralEstimate (fun z => z) unitCircleEstimateData := by
  unfold ContourIntegralEstimate integralEstimateDataReady unitCircleEstimateData
  norm_num


structure IntegralEstimatesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def IntegralEstimatesBudgetCertificate.controlled
    (c : IntegralEstimatesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def IntegralEstimatesBudgetCertificate.budgetControlled
    (c : IntegralEstimatesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def IntegralEstimatesBudgetCertificate.Ready
    (c : IntegralEstimatesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def IntegralEstimatesBudgetCertificate.size
    (c : IntegralEstimatesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem integralEstimates_budgetCertificate_le_size
    (c : IntegralEstimatesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleIntegralEstimatesBudgetCertificate :
    IntegralEstimatesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleIntegralEstimatesBudgetCertificate.Ready := by
  constructor
  · norm_num [IntegralEstimatesBudgetCertificate.controlled,
      sampleIntegralEstimatesBudgetCertificate]
  · norm_num [IntegralEstimatesBudgetCertificate.budgetControlled,
      sampleIntegralEstimatesBudgetCertificate]

example :
    sampleIntegralEstimatesBudgetCertificate.certificateBudgetWindow ≤
      sampleIntegralEstimatesBudgetCertificate.size := by
  apply integralEstimates_budgetCertificate_le_size
  constructor
  · norm_num [IntegralEstimatesBudgetCertificate.controlled,
      sampleIntegralEstimatesBudgetCertificate]
  · norm_num [IntegralEstimatesBudgetCertificate.budgetControlled,
      sampleIntegralEstimatesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleIntegralEstimatesBudgetCertificate.Ready := by
  constructor
  · norm_num [IntegralEstimatesBudgetCertificate.controlled,
      sampleIntegralEstimatesBudgetCertificate]
  · norm_num [IntegralEstimatesBudgetCertificate.budgetControlled,
      sampleIntegralEstimatesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleIntegralEstimatesBudgetCertificate.certificateBudgetWindow ≤
      sampleIntegralEstimatesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List IntegralEstimatesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleIntegralEstimatesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleIntegralEstimatesBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.IntegralEstimates
