import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Large powers.
-/

namespace AnalyticCombinatorics.PartB.Ch8.LargePowers

/-- Coefficient model for the large power `(1 + z)^m`. -/
def binomialPowerCoeff (m k : ℕ) : ℕ :=
  m.choose k

/-- Finite coefficient envelope for a large power row. -/
def binomialPowerEnvelopeCheck (m : ℕ) : Bool :=
  (List.range (m + 1)).all fun k => binomialPowerCoeff m k ≤ 2 ^ m

/-- Prefix-row sum for sampled large-power coefficients. -/
def binomialPowerPrefix (m n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + binomialPowerCoeff m k) 0

/-- Finite large-power statement: coefficients and prefixes are bounded. -/
def LargePowerWindow (m : ℕ) : Prop :=
  binomialPowerEnvelopeCheck m = true ∧
    binomialPowerPrefix m m = 2 ^ m

theorem binomialPowerCoeff_samples :
    binomialPowerCoeff 5 0 = 1 ∧
    binomialPowerCoeff 5 1 = 5 ∧
    binomialPowerCoeff 5 2 = 10 ∧
    binomialPowerCoeff 5 3 = 10 := by
  unfold binomialPowerCoeff
  native_decide

theorem binomialPower_largePowerWindow_8 :
    LargePowerWindow 8 := by
  unfold LargePowerWindow binomialPowerEnvelopeCheck binomialPowerPrefix
    binomialPowerCoeff
  native_decide

/-- Finite symmetry audit for a large binomial-power row. -/
def binomialPowerSymmetryCheck (m : ℕ) : Bool :=
  (List.range (m + 1)).all fun k =>
    binomialPowerCoeff m k = binomialPowerCoeff m (m - k)

theorem binomialPower_symmetryWindow_10 :
    binomialPowerSymmetryCheck 10 = true := by
  unfold binomialPowerSymmetryCheck binomialPowerCoeff
  native_decide

example : binomialPowerPrefix 4 2 = 11 := by
  unfold binomialPowerPrefix binomialPowerCoeff
  native_decide

example : binomialPowerSymmetryCheck 6 = true := by
  unfold binomialPowerSymmetryCheck binomialPowerCoeff
  native_decide

structure LargePowersBudgetCertificate where
  baseFunctionWindow : ℕ
  exponentWindow : ℕ
  saddleWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LargePowersBudgetCertificate.controlled
    (c : LargePowersBudgetCertificate) : Prop :=
  0 < c.baseFunctionWindow ∧
    c.saddleWindow ≤ c.baseFunctionWindow + c.exponentWindow + c.slack

def LargePowersBudgetCertificate.budgetControlled
    (c : LargePowersBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.baseFunctionWindow + c.exponentWindow + c.saddleWindow + c.slack

def LargePowersBudgetCertificate.Ready
    (c : LargePowersBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LargePowersBudgetCertificate.size
    (c : LargePowersBudgetCertificate) : ℕ :=
  c.baseFunctionWindow + c.exponentWindow + c.saddleWindow + c.slack

theorem largePowers_budgetCertificate_le_size
    (c : LargePowersBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleLargePowersBudgetCertificate : LargePowersBudgetCertificate :=
  { baseFunctionWindow := 5
    exponentWindow := 6
    saddleWindow := 9
    certificateBudgetWindow := 21
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLargePowersBudgetCertificate.Ready := by
  constructor
  · norm_num [LargePowersBudgetCertificate.controlled,
      sampleLargePowersBudgetCertificate]
  · norm_num [LargePowersBudgetCertificate.budgetControlled,
      sampleLargePowersBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLargePowersBudgetCertificate.certificateBudgetWindow ≤
      sampleLargePowersBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLargePowersBudgetCertificate.Ready := by
  constructor
  · norm_num [LargePowersBudgetCertificate.controlled,
      sampleLargePowersBudgetCertificate]
  · norm_num [LargePowersBudgetCertificate.budgetControlled,
      sampleLargePowersBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LargePowersBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleLargePowersBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleLargePowersBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.LargePowers
