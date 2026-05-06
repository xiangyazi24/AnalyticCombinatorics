import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Lagrange inversion.
-/

namespace AnalyticCombinatorics.AppA.LagrangeInversion

/-- Coefficient model from the Lagrange schema `T = z (1 + T)^2`. -/
def lagrangeBinaryTreeCoeff (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

/-- Finite coefficient envelope for the Lagrange binary-tree solution. -/
def lagrangeCoefficientEnvelopeCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => lagrangeBinaryTreeCoeff n ≤ 4 ^ n

/-- Finite Lagrange inversion window for the binary-tree schema. -/
def LagrangeBinaryTreeWindow (N : ℕ) : Prop :=
  lagrangeCoefficientEnvelopeCheck N = true

theorem lagrangeBinaryTreeCoeff_samples :
    lagrangeBinaryTreeCoeff 0 = 1 ∧
    lagrangeBinaryTreeCoeff 1 = 1 ∧
    lagrangeBinaryTreeCoeff 2 = 2 ∧
    lagrangeBinaryTreeCoeff 3 = 5 ∧
    lagrangeBinaryTreeCoeff 4 = 14 ∧
    lagrangeBinaryTreeCoeff 5 = 42 := by
  unfold lagrangeBinaryTreeCoeff
  native_decide

theorem lagrangeBinaryTree_window :
    LagrangeBinaryTreeWindow 16 := by
  unfold LagrangeBinaryTreeWindow lagrangeCoefficientEnvelopeCheck
    lagrangeBinaryTreeCoeff
  native_decide

/-- Finite Catalan recurrence audit for the Lagrange binary-tree coefficients. -/
def lagrangeCatalanRecurrenceCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    lagrangeBinaryTreeCoeff (n + 1) * (n + 2) =
      2 * (2 * n + 1) * lagrangeBinaryTreeCoeff n

theorem lagrangeBinaryTree_recurrenceWindow :
    lagrangeCatalanRecurrenceCheck 12 = true := by
  unfold lagrangeCatalanRecurrenceCheck lagrangeBinaryTreeCoeff
  native_decide

structure LagrangeInversionBudgetCertificate where
  equationWindow : ℕ
  inversionWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LagrangeInversionBudgetCertificate.controlled
    (c : LagrangeInversionBudgetCertificate) : Prop :=
  0 < c.equationWindow ∧
    c.coefficientWindow ≤ c.equationWindow + c.inversionWindow + c.slack

def LagrangeInversionBudgetCertificate.budgetControlled
    (c : LagrangeInversionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.equationWindow + c.inversionWindow + c.coefficientWindow + c.slack

def LagrangeInversionBudgetCertificate.Ready
    (c : LagrangeInversionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LagrangeInversionBudgetCertificate.size
    (c : LagrangeInversionBudgetCertificate) : ℕ :=
  c.equationWindow + c.inversionWindow + c.coefficientWindow + c.slack

theorem lagrangeInversion_budgetCertificate_le_size
    (c : LagrangeInversionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleLagrangeInversionBudgetCertificate :
    LagrangeInversionBudgetCertificate :=
  { equationWindow := 5
    inversionWindow := 6
    coefficientWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLagrangeInversionBudgetCertificate.Ready := by
  constructor
  · norm_num [LagrangeInversionBudgetCertificate.controlled,
      sampleLagrangeInversionBudgetCertificate]
  · norm_num [LagrangeInversionBudgetCertificate.budgetControlled,
      sampleLagrangeInversionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLagrangeInversionBudgetCertificate.certificateBudgetWindow ≤
      sampleLagrangeInversionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLagrangeInversionBudgetCertificate.Ready := by
  constructor
  · norm_num [LagrangeInversionBudgetCertificate.controlled,
      sampleLagrangeInversionBudgetCertificate]
  · norm_num [LagrangeInversionBudgetCertificate.budgetControlled,
      sampleLagrangeInversionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LagrangeInversionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleLagrangeInversionBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleLagrangeInversionBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleLagrangeInversionBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.AppA.LagrangeInversion
