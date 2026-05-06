import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Implicit Function Theorem.
-/

namespace AnalyticCombinatorics.AppB.ImplicitFunctionTheorem

/-- Integer polynomial model `F(x,y) = y - x * (1 + y)^2`. -/
def implicitTreeEquation (x y : ℤ) : ℤ :=
  y - x * (1 + y) ^ 2

/-- Formal partial derivative with respect to `y`. -/
def implicitTreeDerivativeY (x y : ℤ) : ℤ :=
  1 - x * (2 * (1 + y))

/-- Finite nonzero derivative audit over a sampled box. -/
def derivativeNonzeroOnBox
    (deriv : ℤ → ℤ → ℤ) (radius : ℕ) : Bool :=
  (List.range (radius + 1)).all fun x =>
    (List.range (radius + 1)).all fun y =>
      deriv x y ≠ 0

/-- Local IFT window at the origin for the tree equation. -/
def ImplicitTreeWindow : Prop :=
  implicitTreeEquation 0 0 = 0 ∧ implicitTreeDerivativeY 0 0 = 1

theorem implicitTree_originWindow :
    ImplicitTreeWindow := by
  unfold ImplicitTreeWindow implicitTreeEquation implicitTreeDerivativeY
  norm_num

theorem implicitTreeDerivative_smallBox :
    derivativeNonzeroOnBox implicitTreeDerivativeY 0 = true := by
  unfold derivativeNonzeroOnBox implicitTreeDerivativeY
  native_decide

def ImplicitResidualWindow (x y residual derivative : ℤ) : Prop :=
  implicitTreeEquation x y = residual ∧
    implicitTreeDerivativeY x y = derivative

theorem implicitTree_sampleResidualWindow :
    ImplicitResidualWindow 1 2 (-7) (-5) := by
  unfold ImplicitResidualWindow implicitTreeEquation implicitTreeDerivativeY
  norm_num

example : implicitTreeEquation 2 1 = -7 := by
  unfold implicitTreeEquation
  norm_num

example : implicitTreeDerivativeY 2 1 = -7 := by
  unfold implicitTreeDerivativeY
  norm_num

structure ImplicitFunctionTheoremBudgetCertificate where
  equationWindow : ℕ
  derivativeWindow : ℕ
  solutionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitFunctionTheoremBudgetCertificate.controlled
    (c : ImplicitFunctionTheoremBudgetCertificate) : Prop :=
  0 < c.equationWindow ∧
    c.solutionWindow ≤ c.equationWindow + c.derivativeWindow + c.slack

def ImplicitFunctionTheoremBudgetCertificate.budgetControlled
    (c : ImplicitFunctionTheoremBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.equationWindow + c.derivativeWindow + c.solutionWindow + c.slack

def ImplicitFunctionTheoremBudgetCertificate.Ready
    (c : ImplicitFunctionTheoremBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ImplicitFunctionTheoremBudgetCertificate.size
    (c : ImplicitFunctionTheoremBudgetCertificate) : ℕ :=
  c.equationWindow + c.derivativeWindow + c.solutionWindow + c.slack

theorem implicitFunctionTheorem_budgetCertificate_le_size
    (c : ImplicitFunctionTheoremBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleImplicitFunctionTheoremBudgetCertificate :
    ImplicitFunctionTheoremBudgetCertificate :=
  { equationWindow := 5
    derivativeWindow := 6
    solutionWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleImplicitFunctionTheoremBudgetCertificate.Ready := by
  constructor
  · norm_num [ImplicitFunctionTheoremBudgetCertificate.controlled,
      sampleImplicitFunctionTheoremBudgetCertificate]
  · norm_num [ImplicitFunctionTheoremBudgetCertificate.budgetControlled,
      sampleImplicitFunctionTheoremBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleImplicitFunctionTheoremBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitFunctionTheoremBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleImplicitFunctionTheoremBudgetCertificate.Ready := by
  constructor
  · norm_num [ImplicitFunctionTheoremBudgetCertificate.controlled,
      sampleImplicitFunctionTheoremBudgetCertificate]
  · norm_num [ImplicitFunctionTheoremBudgetCertificate.budgetControlled,
      sampleImplicitFunctionTheoremBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ImplicitFunctionTheoremBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleImplicitFunctionTheoremBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleImplicitFunctionTheoremBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.ImplicitFunctionTheorem
