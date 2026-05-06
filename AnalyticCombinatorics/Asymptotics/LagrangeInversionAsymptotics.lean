import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Lagrange inversion asymptotics
-/

namespace AnalyticCombinatorics.Asymptotics.LagrangeInversionAsymptotics

/-- Lagrange inversion coefficient model for rooted plane trees. -/
def catalanByLagrange (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

theorem catalanByLagrange_samples :
    catalanByLagrange 0 = 1 ∧
      catalanByLagrange 3 = 5 ∧
        catalanByLagrange 5 = 42 := by
  native_decide

/-- Critical composition envelope for square-root Lagrange schemas. -/
def lagrangeCriticalEnvelope (radiusInv n : ℕ) : ℕ :=
  (n + 1) * radiusInv ^ n

theorem lagrangeCriticalEnvelope_zero (radiusInv : ℕ) :
    lagrangeCriticalEnvelope radiusInv 0 = 1 := by
  simp [lagrangeCriticalEnvelope]

def lagrangeEnvelopeCheck (coeff : ℕ → ℕ) (radiusInv N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => coeff n ≤ lagrangeCriticalEnvelope radiusInv n

theorem catalan_lagrangeEnvelopeCheck :
    lagrangeEnvelopeCheck catalanByLagrange 4 8 = true := by
  unfold lagrangeEnvelopeCheck lagrangeCriticalEnvelope catalanByLagrange
  native_decide

structure LagrangeAsymptoticWindow where
  inversionWindow : ℕ
  criticalWindow : ℕ
  coefficientWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LagrangeAsymptoticWindow.ready
    (w : LagrangeAsymptoticWindow) : Prop :=
  0 < w.inversionWindow ∧
    w.coefficientWindow ≤ w.inversionWindow + w.criticalWindow + w.slack

def sampleLagrangeAsymptoticWindow : LagrangeAsymptoticWindow :=
  { inversionWindow := 4, criticalWindow := 3,
    coefficientWindow := 7, slack := 0 }

example : sampleLagrangeAsymptoticWindow.ready := by
  norm_num [LagrangeAsymptoticWindow.ready, sampleLagrangeAsymptoticWindow]

structure BudgetCertificate where
  inversionWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.inversionWindow ∧
    c.coefficientWindow ≤ c.inversionWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.inversionWindow + c.coefficientWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.inversionWindow + c.coefficientWindow + c.slack

theorem lagrangeInversionAsymptotics_budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBudgetCertificate : BudgetCertificate :=
  { inversionWindow := 5, coefficientWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

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

end AnalyticCombinatorics.Asymptotics.LagrangeInversionAsymptotics
