import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Stirling formula
-/

namespace AnalyticCombinatorics.Asymptotics.StirlingFormula

def factorialRatioProxy (n : ℕ) : ℕ :=
  Nat.factorial (n + 1) / Nat.factorial n

theorem factorialRatioProxy_eq_succ (n : ℕ) :
    factorialRatioProxy n = n + 1 := by
  unfold factorialRatioProxy
  rw [Nat.factorial_succ]
  rw [Nat.mul_comm]
  exact Nat.mul_div_right (n + 1) (Nat.factorial_pos n)

theorem factorialRatioProxy_samples :
    factorialRatioProxy 1 = 2 ∧ factorialRatioProxy 5 = 6 := by
  native_decide

/-- The leading integer scale in Stirling's formula. -/
def stirlingIntegerScale (n : ℕ) : ℕ :=
  n ^ n

theorem stirlingIntegerScale_zero :
    stirlingIntegerScale 0 = 1 := by
  simp [stirlingIntegerScale]

theorem stirlingIntegerScale_one :
    stirlingIntegerScale 1 = 1 := by
  simp [stirlingIntegerScale]

theorem factorial_le_stirlingIntegerScale
    (n : ℕ) :
    Nat.factorial n ≤ stirlingIntegerScale n := by
  unfold stirlingIntegerScale
  exact Nat.factorial_le_pow n

structure BudgetCertificate where
  factorialWindow : ℕ
  errorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.factorialWindow ∧ c.errorWindow ≤ c.factorialWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.factorialWindow + c.errorWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.factorialWindow + c.errorWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { factorialWindow := 5, errorWindow := 6, certificateBudgetWindow := 12,
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

end AnalyticCombinatorics.Asymptotics.StirlingFormula
