import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Limit law schemas.
-/

namespace AnalyticCombinatorics.PartA.Ch3.LimitLaws

structure LimitLawWindow where
  scale : ℕ
  varianceProxy : ℕ
  errorWindow : ℕ
deriving DecidableEq, Repr

def limitLawReady (w : LimitLawWindow) : Prop :=
  0 < w.scale ∧ w.errorWindow ≤ w.scale + w.varianceProxy

def limitLawBudget (w : LimitLawWindow) : ℕ :=
  w.scale + w.varianceProxy + w.errorWindow

theorem errorWindow_le_budget (w : LimitLawWindow) :
    w.errorWindow ≤ limitLawBudget w := by
  unfold limitLawBudget
  omega

def sampleLimitLawWindow : LimitLawWindow :=
  { scale := 10, varianceProxy := 4, errorWindow := 12 }

example : limitLawReady sampleLimitLawWindow := by
  norm_num [limitLawReady, sampleLimitLawWindow]

example : limitLawBudget sampleLimitLawWindow = 26 := by
  native_decide

structure GaussianLimitCertificate where
  sampleSize : ℕ
  centeringScale : ℕ
  varianceScale : ℕ
  approximationError : ℕ
deriving DecidableEq, Repr

def GaussianLimitCertificate.scaledVarianceReady (c : GaussianLimitCertificate) : Prop :=
  0 < c.sampleSize ∧ 0 < c.varianceScale

def GaussianLimitCertificate.errorControlled (c : GaussianLimitCertificate) : Prop :=
  c.approximationError ≤ c.sampleSize + c.varianceScale

def GaussianLimitCertificate.certificate (c : GaussianLimitCertificate) : ℕ :=
  c.sampleSize + c.centeringScale + c.varianceScale + c.approximationError

theorem approximationError_le_certificate (c : GaussianLimitCertificate) :
    c.approximationError ≤ c.certificate := by
  unfold GaussianLimitCertificate.certificate
  omega

def sampleGaussianLimitCertificate : GaussianLimitCertificate :=
  { sampleSize := 25, centeringScale := 10, varianceScale := 5, approximationError := 8 }

example : sampleGaussianLimitCertificate.scaledVarianceReady := by
  norm_num [sampleGaussianLimitCertificate, GaussianLimitCertificate.scaledVarianceReady]

example : sampleGaussianLimitCertificate.errorControlled := by
  norm_num [sampleGaussianLimitCertificate, GaussianLimitCertificate.errorControlled]


structure LimitLawsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LimitLawsBudgetCertificate.controlled
    (c : LimitLawsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LimitLawsBudgetCertificate.budgetControlled
    (c : LimitLawsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LimitLawsBudgetCertificate.Ready
    (c : LimitLawsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LimitLawsBudgetCertificate.size
    (c : LimitLawsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem limitLaws_budgetCertificate_le_size
    (c : LimitLawsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLimitLawsBudgetCertificate :
    LimitLawsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [LimitLawsBudgetCertificate.controlled,
      sampleLimitLawsBudgetCertificate]
  · norm_num [LimitLawsBudgetCertificate.budgetControlled,
      sampleLimitLawsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLimitLawsBudgetCertificate.certificateBudgetWindow ≤
      sampleLimitLawsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [LimitLawsBudgetCertificate.controlled,
      sampleLimitLawsBudgetCertificate]
  · norm_num [LimitLawsBudgetCertificate.budgetControlled,
      sampleLimitLawsBudgetCertificate]

example :
    sampleLimitLawsBudgetCertificate.certificateBudgetWindow ≤
      sampleLimitLawsBudgetCertificate.size := by
  apply limitLaws_budgetCertificate_le_size
  constructor
  · norm_num [LimitLawsBudgetCertificate.controlled,
      sampleLimitLawsBudgetCertificate]
  · norm_num [LimitLawsBudgetCertificate.budgetControlled,
      sampleLimitLawsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LimitLawsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLimitLawsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLimitLawsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.LimitLaws
