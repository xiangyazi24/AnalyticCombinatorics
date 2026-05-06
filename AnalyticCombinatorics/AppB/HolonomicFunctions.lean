import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix B: holonomic functions.

Finite order and recurrence-window bookkeeping for D-finite closures.
-/

namespace AnalyticCombinatorics.AppB.HolonomicFunctions

/-- A finite recurrence check for coefficient sequences. -/
def firstOrderRecurrenceCheck
    (a : ℕ → ℕ) (multiplier N : ℕ) : Bool :=
  (List.range N).all fun n => a (n + 1) = multiplier * a n

/-- Geometric sequences are the basic first-order holonomic model. -/
def geometricHolonomicCoeff (multiplier n : ℕ) : ℕ :=
  multiplier ^ n

/-- Finite closure check for sums of two holonomic coefficient models. -/
def holonomicSumEnvelopeCheck
    (a b envelope : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => a n + b n ≤ envelope n

theorem geometricHolonomic_recurrence :
    firstOrderRecurrenceCheck (geometricHolonomicCoeff 3) 3 16 = true := by
  unfold firstOrderRecurrenceCheck geometricHolonomicCoeff
  native_decide

theorem holonomicSum_geometricEnvelope :
    holonomicSumEnvelopeCheck
      (geometricHolonomicCoeff 2) (geometricHolonomicCoeff 2)
      (fun n => 2 * 2 ^ n) 16 = true := by
  unfold holonomicSumEnvelopeCheck geometricHolonomicCoeff
  native_decide

structure HolonomicWindow where
  differentialOrder : ℕ
  polynomialDegree : ℕ
  recurrenceOrder : ℕ
  closureSlack : ℕ
deriving DecidableEq, Repr

def holonomicWindowReady (w : HolonomicWindow) : Prop :=
  0 < w.differentialOrder ∧
    w.recurrenceOrder ≤ w.differentialOrder + w.polynomialDegree + w.closureSlack

def holonomicWindowBudget (w : HolonomicWindow) : ℕ :=
  w.differentialOrder + w.polynomialDegree + w.recurrenceOrder + w.closureSlack

theorem recurrenceOrder_le_budget (w : HolonomicWindow) :
    w.recurrenceOrder ≤ holonomicWindowBudget w := by
  unfold holonomicWindowBudget
  omega

def sampleHolonomicWindow : HolonomicWindow :=
  { differentialOrder := 2
    polynomialDegree := 5
    recurrenceOrder := 7
    closureSlack := 1 }

example : holonomicWindowReady sampleHolonomicWindow := by
  norm_num [holonomicWindowReady, sampleHolonomicWindow]

structure HolonomicFunctionsBudgetCertificate where
  orderWindow : ℕ
  degreeWindow : ℕ
  recurrenceWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HolonomicFunctionsBudgetCertificate.controlled
    (c : HolonomicFunctionsBudgetCertificate) : Prop :=
  0 < c.orderWindow ∧
    c.recurrenceWindow ≤ c.orderWindow + c.degreeWindow + c.slack

def HolonomicFunctionsBudgetCertificate.budgetControlled
    (c : HolonomicFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.orderWindow + c.degreeWindow + c.recurrenceWindow + c.slack

def HolonomicFunctionsBudgetCertificate.Ready
    (c : HolonomicFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HolonomicFunctionsBudgetCertificate.size
    (c : HolonomicFunctionsBudgetCertificate) : ℕ :=
  c.orderWindow + c.degreeWindow + c.recurrenceWindow + c.slack

theorem holonomicFunctions_budgetCertificate_le_size
    (c : HolonomicFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleHolonomicFunctionsBudgetCertificate :
    HolonomicFunctionsBudgetCertificate :=
  { orderWindow := 2
    degreeWindow := 5
    recurrenceWindow := 7
    certificateBudgetWindow := 15
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleHolonomicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [HolonomicFunctionsBudgetCertificate.controlled,
      sampleHolonomicFunctionsBudgetCertificate]
  · norm_num [HolonomicFunctionsBudgetCertificate.budgetControlled,
      sampleHolonomicFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHolonomicFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleHolonomicFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleHolonomicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [HolonomicFunctionsBudgetCertificate.controlled,
      sampleHolonomicFunctionsBudgetCertificate]
  · norm_num [HolonomicFunctionsBudgetCertificate.budgetControlled,
      sampleHolonomicFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List HolonomicFunctionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleHolonomicFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleHolonomicFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.HolonomicFunctions
