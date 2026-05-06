import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multivariate limit laws.
-/

namespace AnalyticCombinatorics.PartB.Ch9.MultivariateLimitLaws

/-- Two-dimensional finite mean/covariance descriptor. -/
structure BivariateMomentWindow where
  meanX : ℚ
  meanY : ℚ
  varX : ℚ
  varY : ℚ
  covXY : ℚ
deriving Repr

def BivariateMomentWindow.valid (w : BivariateMomentWindow) : Prop :=
  0 ≤ w.varX ∧ 0 ≤ w.varY ∧ w.covXY * w.covXY ≤ w.varX * w.varY

def independentUnitWindow : BivariateMomentWindow :=
  { meanX := 0, meanY := 0, varX := 1, varY := 1, covXY := 0 }

def MultivariateLawWindow (w : BivariateMomentWindow) : Prop :=
  w.valid

theorem independentUnit_multivariateWindow :
    MultivariateLawWindow independentUnitWindow := by
  norm_num [MultivariateLawWindow, BivariateMomentWindow.valid,
    independentUnitWindow]

def BivariateMomentWindow.covarianceDeterminant
    (w : BivariateMomentWindow) : ℚ :=
  w.varX * w.varY - w.covXY * w.covXY

def PositiveCovarianceWindow (w : BivariateMomentWindow) : Prop :=
  0 < w.varX ∧ 0 < w.varY ∧ 0 < w.covarianceDeterminant

theorem independentUnit_positiveCovarianceWindow :
    PositiveCovarianceWindow independentUnitWindow := by
  norm_num [PositiveCovarianceWindow,
    BivariateMomentWindow.covarianceDeterminant, independentUnitWindow]

structure MultivariateLimitLawsBudgetCertificate where
  dimensionWindow : ℕ
  covarianceWindow : ℕ
  convergenceWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultivariateLimitLawsBudgetCertificate.controlled
    (c : MultivariateLimitLawsBudgetCertificate) : Prop :=
  0 < c.dimensionWindow ∧
    c.convergenceWindow ≤ c.dimensionWindow + c.covarianceWindow + c.slack

def MultivariateLimitLawsBudgetCertificate.budgetControlled
    (c : MultivariateLimitLawsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.dimensionWindow + c.covarianceWindow + c.convergenceWindow + c.slack

def MultivariateLimitLawsBudgetCertificate.Ready
    (c : MultivariateLimitLawsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultivariateLimitLawsBudgetCertificate.size
    (c : MultivariateLimitLawsBudgetCertificate) : ℕ :=
  c.dimensionWindow + c.covarianceWindow + c.convergenceWindow + c.slack

theorem multivariateLimitLaws_budgetCertificate_le_size
    (c : MultivariateLimitLawsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleMultivariateLimitLawsBudgetCertificate :
    MultivariateLimitLawsBudgetCertificate :=
  { dimensionWindow := 5
    covarianceWindow := 6
    convergenceWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMultivariateLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivariateLimitLawsBudgetCertificate.controlled,
      sampleMultivariateLimitLawsBudgetCertificate]
  · norm_num [MultivariateLimitLawsBudgetCertificate.budgetControlled,
      sampleMultivariateLimitLawsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultivariateLimitLawsBudgetCertificate.certificateBudgetWindow ≤
      sampleMultivariateLimitLawsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMultivariateLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivariateLimitLawsBudgetCertificate.controlled,
      sampleMultivariateLimitLawsBudgetCertificate]
  · norm_num [MultivariateLimitLawsBudgetCertificate.budgetControlled,
      sampleMultivariateLimitLawsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MultivariateLimitLawsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleMultivariateLimitLawsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleMultivariateLimitLawsBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleMultivariateLimitLawsBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch9.MultivariateLimitLaws
