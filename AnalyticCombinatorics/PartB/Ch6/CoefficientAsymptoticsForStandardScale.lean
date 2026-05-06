import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Coefficient asymptotics for the standard scale
-/

namespace AnalyticCombinatorics.PartB.Ch6.CoefficientAsymptoticsForStandardScale

def standardScaleProxy (n alphaShift : ℕ) : ℕ :=
  (n + 1) ^ alphaShift

theorem standardScaleProxy_samples :
    standardScaleProxy 3 2 = 16 ∧
      standardScaleProxy 4 0 = 1 := by
  native_decide

structure StandardScaleCoefficientWindow where
  scaleWindow : ℕ
  exponentWindow : ℕ
  coefficientWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StandardScaleCoefficientWindow.ready
    (w : StandardScaleCoefficientWindow) : Prop :=
  0 < w.scaleWindow ∧
    w.coefficientWindow ≤ w.scaleWindow + w.exponentWindow + w.slack

def sampleStandardScaleCoefficientWindow : StandardScaleCoefficientWindow :=
  { scaleWindow := 5, exponentWindow := 3, coefficientWindow := 9, slack := 1 }

example : sampleStandardScaleCoefficientWindow.ready := by
  norm_num [StandardScaleCoefficientWindow.ready,
    sampleStandardScaleCoefficientWindow]

/-- The standard-scale certificate is one at exponent zero. -/
theorem standardScaleProxy_zero_shift (n : ℕ) :
    standardScaleProxy n 0 = 1 := by
  unfold standardScaleProxy
  simp

/-- The standard-scale certificate at shift one is the cleared linear scale. -/
theorem standardScaleProxy_one_shift (n : ℕ) :
    standardScaleProxy n 1 = n + 1 := by
  unfold standardScaleProxy
  simp

structure CoefficientAsymptoticsForStandardScaleBudgetCertificate where
  scaleWindow : ℕ
  exponentWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoefficientAsymptoticsForStandardScaleBudgetCertificate.controlled
    (c : CoefficientAsymptoticsForStandardScaleBudgetCertificate) : Prop :=
  0 < c.scaleWindow ∧
    c.coefficientWindow ≤ c.scaleWindow + c.exponentWindow + c.slack

def CoefficientAsymptoticsForStandardScaleBudgetCertificate.budgetControlled
    (c : CoefficientAsymptoticsForStandardScaleBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.scaleWindow + c.exponentWindow + c.coefficientWindow + c.slack

def CoefficientAsymptoticsForStandardScaleBudgetCertificate.Ready
    (c : CoefficientAsymptoticsForStandardScaleBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CoefficientAsymptoticsForStandardScaleBudgetCertificate.size
    (c : CoefficientAsymptoticsForStandardScaleBudgetCertificate) : ℕ :=
  c.scaleWindow + c.exponentWindow + c.coefficientWindow + c.slack

def sampleCoefficientAsymptoticsForStandardScaleBudgetCertificate :
    CoefficientAsymptoticsForStandardScaleBudgetCertificate :=
  { scaleWindow := 5
    exponentWindow := 3
    coefficientWindow := 9
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCoefficientAsymptoticsForStandardScaleBudgetCertificate.Ready := by
  constructor
  · norm_num [CoefficientAsymptoticsForStandardScaleBudgetCertificate.controlled,
      sampleCoefficientAsymptoticsForStandardScaleBudgetCertificate]
  · norm_num [CoefficientAsymptoticsForStandardScaleBudgetCertificate.budgetControlled,
      sampleCoefficientAsymptoticsForStandardScaleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCoefficientAsymptoticsForStandardScaleBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientAsymptoticsForStandardScaleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCoefficientAsymptoticsForStandardScaleBudgetCertificate.Ready := by
  constructor
  · norm_num
      [CoefficientAsymptoticsForStandardScaleBudgetCertificate.controlled,
        sampleCoefficientAsymptoticsForStandardScaleBudgetCertificate]
  · norm_num
      [CoefficientAsymptoticsForStandardScaleBudgetCertificate.budgetControlled,
        sampleCoefficientAsymptoticsForStandardScaleBudgetCertificate]

def budgetCertificateListReady
    (data : List CoefficientAsymptoticsForStandardScaleBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCoefficientAsymptoticsForStandardScaleBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCoefficientAsymptoticsForStandardScaleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.CoefficientAsymptoticsForStandardScale
