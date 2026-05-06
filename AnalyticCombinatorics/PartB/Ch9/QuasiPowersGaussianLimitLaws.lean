import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Quasi-powers and Gaussian limit laws.
-/

namespace AnalyticCombinatorics.PartB.Ch9.QuasiPowersGaussianLimitLaws

/-- Finite quasi-power descriptor: mean and variance growth proxies. -/
structure QuasiPowerWindow where
  mean : ℕ → ℚ
  variance : ℕ → ℚ

/-- Finite audit that variance is positive and nondecreasing. -/
def varianceReadyUpTo (variance : ℕ → ℚ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => 0 < variance n &&
    if n = 0 then true else variance (n - 1) ≤ variance n

def linearGaussianProxy : QuasiPowerWindow :=
  { mean := fun n => n
    variance := fun n => n + 1 }

def QuasiPowerGaussianWindow (w : QuasiPowerWindow) (N : ℕ) : Prop :=
  varianceReadyUpTo w.variance N = true

theorem linearGaussianProxy_window :
    QuasiPowerGaussianWindow linearGaussianProxy 24 := by
  unfold QuasiPowerGaussianWindow varianceReadyUpTo linearGaussianProxy
  native_decide

/-- Finite audit that the mean and variance proxies have the expected linear slope. -/
def linearMomentReadyUpTo (w : QuasiPowerWindow) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    w.mean n = n && w.variance n = n + 1

def LinearQuasiPowerWindow (w : QuasiPowerWindow) (N : ℕ) : Prop :=
  linearMomentReadyUpTo w N = true

theorem linearGaussianProxy_linearMomentWindow :
    LinearQuasiPowerWindow linearGaussianProxy 16 := by
  unfold LinearQuasiPowerWindow linearMomentReadyUpTo linearGaussianProxy
  native_decide

structure QuasiPowersGaussianLimitLawsBudgetCertificate where
  quasiPowerWindow : ℕ
  varianceWindow : ℕ
  gaussianWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuasiPowersGaussianLimitLawsBudgetCertificate.controlled
    (c : QuasiPowersGaussianLimitLawsBudgetCertificate) : Prop :=
  0 < c.quasiPowerWindow ∧
    c.gaussianWindow ≤ c.quasiPowerWindow + c.varianceWindow + c.slack

def QuasiPowersGaussianLimitLawsBudgetCertificate.budgetControlled
    (c : QuasiPowersGaussianLimitLawsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.quasiPowerWindow + c.varianceWindow + c.gaussianWindow + c.slack

def QuasiPowersGaussianLimitLawsBudgetCertificate.Ready
    (c : QuasiPowersGaussianLimitLawsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def QuasiPowersGaussianLimitLawsBudgetCertificate.size
    (c : QuasiPowersGaussianLimitLawsBudgetCertificate) : ℕ :=
  c.quasiPowerWindow + c.varianceWindow + c.gaussianWindow + c.slack

theorem quasiPowersGaussianLimitLaws_budgetCertificate_le_size
    (c : QuasiPowersGaussianLimitLawsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleQuasiPowersGaussianLimitLawsBudgetCertificate :
    QuasiPowersGaussianLimitLawsBudgetCertificate :=
  { quasiPowerWindow := 5
    varianceWindow := 6
    gaussianWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleQuasiPowersGaussianLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [QuasiPowersGaussianLimitLawsBudgetCertificate.controlled,
      sampleQuasiPowersGaussianLimitLawsBudgetCertificate]
  · norm_num [QuasiPowersGaussianLimitLawsBudgetCertificate.budgetControlled,
      sampleQuasiPowersGaussianLimitLawsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleQuasiPowersGaussianLimitLawsBudgetCertificate.certificateBudgetWindow ≤
      sampleQuasiPowersGaussianLimitLawsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleQuasiPowersGaussianLimitLawsBudgetCertificate.Ready := by
  constructor
  · norm_num [QuasiPowersGaussianLimitLawsBudgetCertificate.controlled,
      sampleQuasiPowersGaussianLimitLawsBudgetCertificate]
  · norm_num [QuasiPowersGaussianLimitLawsBudgetCertificate.budgetControlled,
      sampleQuasiPowersGaussianLimitLawsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List QuasiPowersGaussianLimitLawsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleQuasiPowersGaussianLimitLawsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleQuasiPowersGaussianLimitLawsBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleQuasiPowersGaussianLimitLawsBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch9.QuasiPowersGaussianLimitLaws
