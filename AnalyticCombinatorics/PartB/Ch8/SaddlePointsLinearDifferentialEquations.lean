import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Saddle-points and linear differential equations.

Finite coefficient and residual checks for the saddle-point treatment of
linear differential equations.
-/

namespace AnalyticCombinatorics.PartB.Ch8.SaddlePointsLinearDifferentialEquations

/-- Coefficient table for a first-order linear differential equation
`A(z) y'(z) + B(z) y(z) = C(z)`, truncated to finite windows. -/
structure LinearDifferentialWindow where
  derivativeCoeff : ℕ → ℤ
  solutionCoeff : ℕ → ℤ
  forcingCoeff : ℕ → ℤ

/-- Formal derivative coefficient: `[z^n] y'(z) = (n+1) a_{n+1}`. -/
def shiftedDerivativeCoeff (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  (n + 1 : ℤ) * a (n + 1)

/-- Residual for the model equation `y' - y = f`. -/
def firstOrderResidual (a f : ℕ → ℤ) (n : ℕ) : ℤ :=
  shiftedDerivativeCoeff a n - a n - f n

/-- Finite residual audit for a truncated linear differential equation. -/
def residualZeroUpTo (a f : ℕ → ℤ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => firstOrderResidual a f n = 0

def factorialCoeff (n : ℕ) : ℤ :=
  Nat.factorial n

def factorialForcing (n : ℕ) : ℤ :=
  (n + 1 : ℤ) * Nat.factorial (n + 1) - Nat.factorial n

theorem factorialCoeff_firstOrderResidual_window :
    residualZeroUpTo factorialCoeff factorialForcing 8 = true := by
  unfold residualZeroUpTo firstOrderResidual shiftedDerivativeCoeff
    factorialCoeff factorialForcing
  native_decide

/-- A discrete phase induced by a coefficient sequence and a scale. -/
def coefficientPhase (scale : ℕ) (n : ℕ) : ℤ :=
  ((n : ℤ) - (scale : ℤ)) ^ 2

/-- The saddle point is where the finite coefficient phase is minimized. -/
def differentialSaddleCheck
    (scale width : ℕ) : Bool :=
  (List.range (2 * scale + width + 1)).all fun n =>
    coefficientPhase scale scale ≤ coefficientPhase scale n

theorem differentialSaddleCheck_sample :
    differentialSaddleCheck 5 4 = true := by
  unfold differentialSaddleCheck coefficientPhase
  native_decide

example : shiftedDerivativeCoeff factorialCoeff 4 = 600 := by
  unfold shiftedDerivativeCoeff factorialCoeff
  native_decide

example : differentialSaddleCheck 3 2 = true := by
  unfold differentialSaddleCheck coefficientPhase
  native_decide

/-- A finite WKB-style balance window for first and second derivative terms. -/
structure WKBWindow where
  firstDerivativeBudget : ℕ
  secondDerivativeBudget : ℕ
  phaseBudget : ℕ
  forcingBudget : ℕ
deriving DecidableEq, Repr

def WKBWindow.derivativesControlled (w : WKBWindow) : Prop :=
  w.firstDerivativeBudget ≤ w.phaseBudget + w.forcingBudget ∧
    w.secondDerivativeBudget ≤
      w.firstDerivativeBudget + w.phaseBudget + w.forcingBudget

def WKBWindow.ready (w : WKBWindow) : Prop :=
  0 < w.phaseBudget ∧ w.derivativesControlled

def sampleWKBWindow : WKBWindow :=
  { firstDerivativeBudget := 5
    secondDerivativeBudget := 9
    phaseBudget := 6
    forcingBudget := 2 }

theorem sampleWKBWindow_ready :
    sampleWKBWindow.ready := by
  norm_num [WKBWindow.ready, WKBWindow.derivativesControlled,
    sampleWKBWindow]

/-- Boolean readiness audit for finite WKB windows. -/
def wkbWindowListReady (data : List WKBWindow) : Bool :=
  data.all fun w =>
    0 < w.phaseBudget &&
      w.firstDerivativeBudget ≤ w.phaseBudget + w.forcingBudget &&
        w.secondDerivativeBudget ≤
          w.firstDerivativeBudget + w.phaseBudget + w.forcingBudget

theorem wkbWindowList_readyWindow :
    wkbWindowListReady
      [sampleWKBWindow,
       { firstDerivativeBudget := 4, secondDerivativeBudget := 7,
         phaseBudget := 5, forcingBudget := 1 }] = true := by
  unfold wkbWindowListReady sampleWKBWindow
  native_decide

structure SaddlePointsLinearDifferentialEquationsBudgetCertificate where
  equationWindow : ℕ
  residualWindow : ℕ
  saddleWindow : ℕ
  wkbWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddlePointsLinearDifferentialEquationsBudgetCertificate.controlled
    (c : SaddlePointsLinearDifferentialEquationsBudgetCertificate) : Prop :=
  0 < c.equationWindow ∧
    c.residualWindow ≤ c.equationWindow + c.slack ∧
      c.wkbWindow ≤ c.residualWindow + c.saddleWindow + c.slack

def SaddlePointsLinearDifferentialEquationsBudgetCertificate.budgetControlled
    (c : SaddlePointsLinearDifferentialEquationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.equationWindow + c.residualWindow + c.saddleWindow +
      c.wkbWindow + c.slack

def SaddlePointsLinearDifferentialEquationsBudgetCertificate.Ready
    (c : SaddlePointsLinearDifferentialEquationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SaddlePointsLinearDifferentialEquationsBudgetCertificate.size
    (c : SaddlePointsLinearDifferentialEquationsBudgetCertificate) : ℕ :=
  c.equationWindow + c.residualWindow + c.saddleWindow +
    c.wkbWindow + c.slack

theorem saddlePointsLinearDifferentialEquations_budgetCertificate_le_size
    (c : SaddlePointsLinearDifferentialEquationsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSaddlePointsLinearDifferentialEquationsBudgetCertificate :
    SaddlePointsLinearDifferentialEquationsBudgetCertificate :=
  { equationWindow := 5
    residualWindow := 6
    saddleWindow := 7
    wkbWindow := 12
    certificateBudgetWindow := 31
    slack := 1 }

example :
    sampleSaddlePointsLinearDifferentialEquationsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [SaddlePointsLinearDifferentialEquationsBudgetCertificate.controlled,
       sampleSaddlePointsLinearDifferentialEquationsBudgetCertificate]
  · norm_num
      [SaddlePointsLinearDifferentialEquationsBudgetCertificate.budgetControlled,
       sampleSaddlePointsLinearDifferentialEquationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSaddlePointsLinearDifferentialEquationsBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddlePointsLinearDifferentialEquationsBudgetCertificate.controlled,
      sampleSaddlePointsLinearDifferentialEquationsBudgetCertificate]
  · norm_num [SaddlePointsLinearDifferentialEquationsBudgetCertificate.budgetControlled,
      sampleSaddlePointsLinearDifferentialEquationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddlePointsLinearDifferentialEquationsBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddlePointsLinearDifferentialEquationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SaddlePointsLinearDifferentialEquationsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSaddlePointsLinearDifferentialEquationsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSaddlePointsLinearDifferentialEquationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.SaddlePointsLinearDifferentialEquations
