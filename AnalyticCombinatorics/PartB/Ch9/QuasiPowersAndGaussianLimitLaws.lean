import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Quasi-powers and Gaussian limit laws
-/

namespace AnalyticCombinatorics.PartB.Ch9.QuasiPowersAndGaussianLimitLaws

/-- Cleared cumulant data for a quasi-power schema. -/
structure QuasiPowerCumulants where
  first : ℕ
  second : ℕ
  thirdBound : ℕ
deriving DecidableEq, Repr

def QuasiPowerCumulants.gaussianReady (c : QuasiPowerCumulants) : Prop :=
  0 < c.second ∧ c.thirdBound ≤ c.second ^ 2

theorem quasiPowerCumulants_sample_ready :
    ({ first := 5, second := 4,
       thirdBound := 16 } : QuasiPowerCumulants).gaussianReady := by
  norm_num [QuasiPowerCumulants.gaussianReady]

/-- Linear variance certificate from a quasi-power second cumulant. -/
def quasiPowerVarianceProxy (n second : ℕ) : ℕ :=
  n * second

theorem quasiPowerVarianceProxy_sample :
    quasiPowerVarianceProxy 7 4 = 28 := by
  native_decide

structure QuasiPowerGaussianWindow where
  quasiPowerWindow : ℕ
  cumulantWindow : ℕ
  gaussianWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def QuasiPowerGaussianWindow.ready (w : QuasiPowerGaussianWindow) : Prop :=
  0 < w.quasiPowerWindow ∧
    w.gaussianWindow ≤ w.quasiPowerWindow + w.cumulantWindow + w.slack

def sampleQuasiPowerGaussianWindow : QuasiPowerGaussianWindow :=
  { quasiPowerWindow := 4, cumulantWindow := 3,
    gaussianWindow := 7, slack := 0 }

example : sampleQuasiPowerGaussianWindow.ready := by
  norm_num [QuasiPowerGaussianWindow.ready, sampleQuasiPowerGaussianWindow]

structure BudgetCertificate where
  quasiPowerWindow : ℕ
  gaussianWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.quasiPowerWindow ∧
    c.gaussianWindow ≤ c.quasiPowerWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.quasiPowerWindow + c.gaussianWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.quasiPowerWindow + c.gaussianWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { quasiPowerWindow := 5, gaussianWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  have h : sampleBudgetCertificate.Ready := by
    constructor
    · norm_num [BudgetCertificate.controlled,
        sampleBudgetCertificate]
    · norm_num [BudgetCertificate.budgetControlled,
        sampleBudgetCertificate]
  exact h.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.QuasiPowersAndGaussianLimitLaws
