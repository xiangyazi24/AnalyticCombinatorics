import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Non-Gaussian continuous limits.
-/

namespace AnalyticCombinatorics.PartB.Ch9.NonGaussianContinuousLimits

/-- Moment descriptor for a sampled continuous limit. -/
structure MomentSignature where
  mean : ℚ
  variance : ℚ
  thirdCentralMoment : ℚ
deriving Repr

def MomentSignature.nonGaussian (m : MomentSignature) : Prop :=
  0 < m.variance ∧ m.thirdCentralMoment ≠ 0

def airyMomentProxy : MomentSignature :=
  { mean := 0, variance := 1, thirdCentralMoment := 1 }

/-- Finite statement form for non-Gaussian continuous limits. -/
def NonGaussianWindow (m : MomentSignature) : Prop :=
  m.nonGaussian

theorem airyMomentProxy_nonGaussian :
    NonGaussianWindow airyMomentProxy := by
  norm_num [NonGaussianWindow, MomentSignature.nonGaussian, airyMomentProxy]

def MomentSignature.positiveSkew (m : MomentSignature) : Prop :=
  0 < m.thirdCentralMoment

def PositiveSkewWindow (m : MomentSignature) : Prop :=
  m.nonGaussian ∧ m.positiveSkew

theorem airyMomentProxy_positiveSkewWindow :
    PositiveSkewWindow airyMomentProxy := by
  norm_num [PositiveSkewWindow, MomentSignature.nonGaussian,
    MomentSignature.positiveSkew, airyMomentProxy]

structure NonGaussianContinuousLimitsBudgetCertificate where
  scalingWindow : ℕ
  transformWindow : ℕ
  distributionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def NonGaussianContinuousLimitsBudgetCertificate.controlled
    (c : NonGaussianContinuousLimitsBudgetCertificate) : Prop :=
  0 < c.scalingWindow ∧
    c.distributionWindow ≤ c.scalingWindow + c.transformWindow + c.slack

def NonGaussianContinuousLimitsBudgetCertificate.budgetControlled
    (c : NonGaussianContinuousLimitsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.scalingWindow + c.transformWindow + c.distributionWindow + c.slack

def NonGaussianContinuousLimitsBudgetCertificate.Ready
    (c : NonGaussianContinuousLimitsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def NonGaussianContinuousLimitsBudgetCertificate.size
    (c : NonGaussianContinuousLimitsBudgetCertificate) : ℕ :=
  c.scalingWindow + c.transformWindow + c.distributionWindow + c.slack

theorem nonGaussianContinuousLimits_budgetCertificate_le_size
    (c : NonGaussianContinuousLimitsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleNonGaussianContinuousLimitsBudgetCertificate :
    NonGaussianContinuousLimitsBudgetCertificate :=
  { scalingWindow := 5
    transformWindow := 6
    distributionWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleNonGaussianContinuousLimitsBudgetCertificate.Ready := by
  constructor
  · norm_num [NonGaussianContinuousLimitsBudgetCertificate.controlled,
      sampleNonGaussianContinuousLimitsBudgetCertificate]
  · norm_num [NonGaussianContinuousLimitsBudgetCertificate.budgetControlled,
      sampleNonGaussianContinuousLimitsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleNonGaussianContinuousLimitsBudgetCertificate.certificateBudgetWindow ≤
      sampleNonGaussianContinuousLimitsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleNonGaussianContinuousLimitsBudgetCertificate.Ready := by
  constructor
  · norm_num [NonGaussianContinuousLimitsBudgetCertificate.controlled,
      sampleNonGaussianContinuousLimitsBudgetCertificate]
  · norm_num [NonGaussianContinuousLimitsBudgetCertificate.budgetControlled,
      sampleNonGaussianContinuousLimitsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List NonGaussianContinuousLimitsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleNonGaussianContinuousLimitsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleNonGaussianContinuousLimitsBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleNonGaussianContinuousLimitsBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch9.NonGaussianContinuousLimits
