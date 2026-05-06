import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Gamma asymptotics
-/

namespace AnalyticCombinatorics.Asymptotics.GammaAsymptotics

def gammaIntegerProxy (n : ℕ) : ℕ :=
  Nat.factorial n

theorem gammaIntegerProxy_zero :
    gammaIntegerProxy 0 = 1 := by
  simp [gammaIntegerProxy]

theorem gammaIntegerProxy_succ (n : ℕ) :
    gammaIntegerProxy (n + 1) = (n + 1) * gammaIntegerProxy n := by
  simp [gammaIntegerProxy, Nat.factorial_succ]

theorem gammaIntegerProxy_samples :
    gammaIntegerProxy 0 = 1 ∧ gammaIntegerProxy 4 = 24 := by
  native_decide

/-- Integer Stirling envelope used for coarse Gamma growth checks. -/
def gammaScaleEnvelope (n : ℕ) : ℕ :=
  n ^ n

theorem gammaIntegerProxy_le_envelope (n : ℕ) :
    gammaIntegerProxy n ≤ gammaScaleEnvelope n := by
  unfold gammaIntegerProxy gammaScaleEnvelope
  exact Nat.factorial_le_pow n

def gammaRatioProxy (n : ℕ) : ℕ :=
  gammaIntegerProxy (n + 1) / gammaIntegerProxy n

theorem gammaRatioProxy_eq_succ (n : ℕ) :
    gammaRatioProxy n = n + 1 := by
  unfold gammaRatioProxy gammaIntegerProxy
  rw [Nat.factorial_succ, Nat.mul_comm]
  exact Nat.mul_div_right (n + 1) (Nat.factorial_pos n)

structure BudgetCertificate where
  gammaWindow : ℕ
  scaleWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.gammaWindow ∧ c.scaleWindow ≤ c.gammaWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.gammaWindow + c.scaleWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.gammaWindow + c.scaleWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { gammaWindow := 5, scaleWindow := 6, certificateBudgetWindow := 12,
    slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.Asymptotics.GammaAsymptotics
