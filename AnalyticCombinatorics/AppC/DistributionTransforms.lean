import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix C: transforms of distributions.

Finite probability generating, moment generating, and characteristic
transform windows.
-/

namespace AnalyticCombinatorics.AppC.DistributionTransforms

/-- Probability generating transform prefix for finite rational masses. -/
def probabilityGeneratingPrefix
    (mass : ℕ → ℚ) (zPower N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun total k => total + mass k * (zPower : ℚ) ^ k) 0

/-- Moment generating estimate at an integer sample point. -/
def momentGeneratingPrefix
    (mass : ℕ → ℚ) (base N : ℕ) : ℚ :=
  probabilityGeneratingPrefix mass base N

def bernoulliHalfMass : ℕ → ℚ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | _ => 0

theorem bernoulliHalf_pgf_samples :
    probabilityGeneratingPrefix bernoulliHalfMass 1 1 = 1 ∧
    probabilityGeneratingPrefix bernoulliHalfMass 2 1 = 3 / 2 := by
  unfold probabilityGeneratingPrefix bernoulliHalfMass
  native_decide

/-- Finite transform normalization check at `z = 1`. -/
def transformNormalizationCheck (mass : ℕ → ℚ) (N : ℕ) : Bool :=
  probabilityGeneratingPrefix mass 1 N = 1

theorem bernoulliHalf_transformNormalization :
    transformNormalizationCheck bernoulliHalfMass 1 = true := by
  unfold transformNormalizationCheck probabilityGeneratingPrefix bernoulliHalfMass
  native_decide

structure DistributionTransformWindow where
  supportSize : ℕ
  transformOrder : ℕ
  coefficientWindow : ℕ
  transformSlack : ℕ
deriving DecidableEq, Repr

def distributionTransformReady (w : DistributionTransformWindow) : Prop :=
  0 < w.supportSize ∧
    w.coefficientWindow ≤ w.supportSize * (w.transformOrder + 1) + w.transformSlack

def distributionTransformBudget (w : DistributionTransformWindow) : ℕ :=
  w.supportSize + w.transformOrder + w.coefficientWindow + w.transformSlack

theorem coefficientWindow_le_budget (w : DistributionTransformWindow) :
    w.coefficientWindow ≤ distributionTransformBudget w := by
  unfold distributionTransformBudget
  omega

def sampleDistributionTransformWindow : DistributionTransformWindow :=
  { supportSize := 5, transformOrder := 2, coefficientWindow := 12,
    transformSlack := 3 }

example : distributionTransformReady sampleDistributionTransformWindow := by
  norm_num [distributionTransformReady, sampleDistributionTransformWindow]

structure DistributionTransformsBudgetCertificate where
  supportWindow : ℕ
  transformWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DistributionTransformsBudgetCertificate.controlled
    (c : DistributionTransformsBudgetCertificate) : Prop :=
  0 < c.supportWindow ∧
    c.coefficientWindow ≤ c.supportWindow * (c.transformWindow + 1) + c.slack

def DistributionTransformsBudgetCertificate.budgetControlled
    (c : DistributionTransformsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.supportWindow + c.transformWindow + c.coefficientWindow + c.slack

def DistributionTransformsBudgetCertificate.Ready
    (c : DistributionTransformsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DistributionTransformsBudgetCertificate.size
    (c : DistributionTransformsBudgetCertificate) : ℕ :=
  c.supportWindow + c.transformWindow + c.coefficientWindow + c.slack

theorem distributionTransforms_budgetCertificate_le_size
    (c : DistributionTransformsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleDistributionTransformsBudgetCertificate :
    DistributionTransformsBudgetCertificate :=
  { supportWindow := 5
    transformWindow := 2
    coefficientWindow := 12
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDistributionTransformsBudgetCertificate.Ready := by
  constructor
  · norm_num [DistributionTransformsBudgetCertificate.controlled,
      sampleDistributionTransformsBudgetCertificate]
  · norm_num [DistributionTransformsBudgetCertificate.budgetControlled,
      sampleDistributionTransformsBudgetCertificate]

example : sampleDistributionTransformsBudgetCertificate.Ready := by
  constructor
  · norm_num [DistributionTransformsBudgetCertificate.controlled,
      sampleDistributionTransformsBudgetCertificate]
  · norm_num [DistributionTransformsBudgetCertificate.budgetControlled,
      sampleDistributionTransformsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleDistributionTransformsBudgetCertificate.certificateBudgetWindow ≤
      sampleDistributionTransformsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DistributionTransformsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleDistributionTransformsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleDistributionTransformsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.DistributionTransforms
