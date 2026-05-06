import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Polylogarithms.

Finite singular-window bookkeeping for polylogarithmic transfer schemas.
-/

namespace AnalyticCombinatorics.PartB.Ch6.Polylogarithms

/-- Finite polylogarithm coefficient model `1 / n^s`, shifted away from zero. -/
def polylogCoeffQ (s n : ℕ) : ℚ :=
  1 / ((n + 1 : ℚ) ^ s)

/-- Finite prefix of a polylogarithm coefficient sequence. -/
def polylogPrefixQ (s N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl (fun total n => total + polylogCoeffQ s n) 0

/-- Finite monotonicity audit for positive-order polylog coefficients. -/
def polylogCoeffNonincreasing (s N : ℕ) : Bool :=
  (List.range N).all fun n => polylogCoeffQ s (n + 1) ≤ polylogCoeffQ s n

theorem polylogCoeff_orderTwo_samples :
    polylogCoeffQ 2 0 = 1 ∧
    polylogCoeffQ 2 1 = 1 / 4 ∧
    polylogCoeffQ 2 2 = 1 / 9 := by
  unfold polylogCoeffQ
  native_decide

theorem polylogCoeff_nonincreasing_orderTwo :
    polylogCoeffNonincreasing 2 24 = true := by
  unfold polylogCoeffNonincreasing polylogCoeffQ
  native_decide

theorem polylogPrefix_orderTwo_samples :
    polylogPrefixQ 2 0 = 1 ∧
      polylogPrefixQ 2 1 = 5 / 4 ∧
      polylogPrefixQ 2 2 = 49 / 36 := by
  unfold polylogPrefixQ polylogCoeffQ
  native_decide

structure PolylogWindow where
  orderWindow : ℕ
  singularWindow : ℕ
  coefficientWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def polylogReady (w : PolylogWindow) : Prop :=
  0 < w.orderWindow ∧
    w.coefficientWindow ≤ w.orderWindow + w.singularWindow + w.slack

def polylogBudget (w : PolylogWindow) : ℕ :=
  w.orderWindow + w.singularWindow + w.coefficientWindow + w.slack

theorem coefficientWindow_le_polylogBudget (w : PolylogWindow) :
    w.coefficientWindow ≤ polylogBudget w := by
  unfold polylogBudget
  omega

def samplePolylogWindow : PolylogWindow :=
  { orderWindow := 4, singularWindow := 5, coefficientWindow := 8, slack := 1 }

example : polylogReady samplePolylogWindow := by
  norm_num [polylogReady, samplePolylogWindow]

structure PolylogarithmsBudgetCertificate where
  orderWindow : ℕ
  singularWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PolylogarithmsBudgetCertificate.controlled
    (c : PolylogarithmsBudgetCertificate) : Prop :=
  0 < c.orderWindow ∧
    c.coefficientWindow ≤ c.orderWindow + c.singularWindow + c.slack

def PolylogarithmsBudgetCertificate.budgetControlled
    (c : PolylogarithmsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.orderWindow + c.singularWindow + c.coefficientWindow + c.slack

def PolylogarithmsBudgetCertificate.Ready
    (c : PolylogarithmsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PolylogarithmsBudgetCertificate.size
    (c : PolylogarithmsBudgetCertificate) : ℕ :=
  c.orderWindow + c.singularWindow + c.coefficientWindow + c.slack

theorem polylogarithms_budgetCertificate_le_size
    (c : PolylogarithmsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def samplePolylogarithmsBudgetCertificate :
    PolylogarithmsBudgetCertificate :=
  { orderWindow := 4
    singularWindow := 5
    coefficientWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

example : samplePolylogarithmsBudgetCertificate.Ready := by
  constructor
  · norm_num [PolylogarithmsBudgetCertificate.controlled,
      samplePolylogarithmsBudgetCertificate]
  · norm_num [PolylogarithmsBudgetCertificate.budgetControlled,
      samplePolylogarithmsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePolylogarithmsBudgetCertificate.Ready := by
  constructor
  · norm_num [PolylogarithmsBudgetCertificate.controlled,
      samplePolylogarithmsBudgetCertificate]
  · norm_num [PolylogarithmsBudgetCertificate.budgetControlled,
      samplePolylogarithmsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePolylogarithmsBudgetCertificate.certificateBudgetWindow ≤
      samplePolylogarithmsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PolylogarithmsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [samplePolylogarithmsBudgetCertificate] = true := by
  unfold budgetCertificateListReady samplePolylogarithmsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.Polylogarithms
