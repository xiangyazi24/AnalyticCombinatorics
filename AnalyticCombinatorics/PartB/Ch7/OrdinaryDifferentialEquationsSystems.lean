import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Ordinary differential equations and systems.

Finite bookkeeping for differential systems that define generating
functions.
-/

namespace AnalyticCombinatorics.PartB.Ch7.OrdinaryDifferentialEquationsSystems

/-- Forward-difference model for the derivative of a coefficient sequence. -/
def forwardDifference (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  a (n + 1) - a n

/-- Finite check for the ODE `y' = 1` under forward differences. -/
def constantDerivativeCheck (a : ℕ → ℤ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => forwardDifference a n = 1

def linearSolution (n : ℕ) : ℤ :=
  n

theorem linearSolution_constantDerivative :
    constantDerivativeCheck linearSolution 24 = true := by
  unfold constantDerivativeCheck forwardDifference linearSolution
  native_decide

/-- Second forward difference for sampled ODE coefficient sequences. -/
def secondForwardDifference (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  forwardDifference a (n + 1) - forwardDifference a n

def quadraticSolution (n : ℕ) : ℤ :=
  n * n

/-- Finite check for the sampled identity `Delta^2 n^2 = 2`. -/
def quadraticSecondDerivativeCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    secondForwardDifference quadraticSolution n = 2

theorem quadraticSolution_secondDerivativeWindow :
    quadraticSecondDerivativeCheck 16 = true := by
  unfold quadraticSecondDerivativeCheck secondForwardDifference
    forwardDifference quadraticSolution
  native_decide

structure ODESystemWindow where
  equationWindow : ℕ
  derivativeOrderWindow : ℕ
  coefficientWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def odeSystemReady (w : ODESystemWindow) : Prop :=
  0 < w.equationWindow ∧
    w.coefficientWindow ≤
      w.equationWindow + w.derivativeOrderWindow + w.slack

def odeSystemBudget (w : ODESystemWindow) : ℕ :=
  w.equationWindow + w.derivativeOrderWindow + w.coefficientWindow + w.slack

theorem coefficientWindow_le_odeSystemBudget (w : ODESystemWindow) :
    w.coefficientWindow ≤ odeSystemBudget w := by
  unfold odeSystemBudget
  omega

def sampleODESystemWindow : ODESystemWindow :=
  { equationWindow := 4
    derivativeOrderWindow := 5
    coefficientWindow := 8
    slack := 1 }

example : odeSystemReady sampleODESystemWindow := by
  norm_num [odeSystemReady, sampleODESystemWindow]

structure OrdinaryDifferentialEquationsSystemsBudgetCertificate where
  equationWindow : ℕ
  derivativeWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def OrdinaryDifferentialEquationsSystemsBudgetCertificate.controlled
    (c : OrdinaryDifferentialEquationsSystemsBudgetCertificate) : Prop :=
  0 < c.equationWindow ∧
    c.coefficientWindow ≤ c.equationWindow + c.derivativeWindow + c.slack

def OrdinaryDifferentialEquationsSystemsBudgetCertificate.budgetControlled
    (c : OrdinaryDifferentialEquationsSystemsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.equationWindow + c.derivativeWindow + c.coefficientWindow + c.slack

def OrdinaryDifferentialEquationsSystemsBudgetCertificate.Ready
    (c : OrdinaryDifferentialEquationsSystemsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def OrdinaryDifferentialEquationsSystemsBudgetCertificate.size
    (c : OrdinaryDifferentialEquationsSystemsBudgetCertificate) : ℕ :=
  c.equationWindow + c.derivativeWindow + c.coefficientWindow + c.slack

theorem ordinaryDifferentialEquationsSystems_budgetCertificate_le_size
    (c : OrdinaryDifferentialEquationsSystemsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleOrdinaryDifferentialEquationsSystemsBudgetCertificate :
    OrdinaryDifferentialEquationsSystemsBudgetCertificate :=
  { equationWindow := 4
    derivativeWindow := 5
    coefficientWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleOrdinaryDifferentialEquationsSystemsBudgetCertificate.Ready := by
  constructor
  · norm_num [OrdinaryDifferentialEquationsSystemsBudgetCertificate.controlled,
      sampleOrdinaryDifferentialEquationsSystemsBudgetCertificate]
  · norm_num [OrdinaryDifferentialEquationsSystemsBudgetCertificate.budgetControlled,
      sampleOrdinaryDifferentialEquationsSystemsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleOrdinaryDifferentialEquationsSystemsBudgetCertificate.certificateBudgetWindow ≤
      sampleOrdinaryDifferentialEquationsSystemsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleOrdinaryDifferentialEquationsSystemsBudgetCertificate.Ready := by
  constructor
  · norm_num [OrdinaryDifferentialEquationsSystemsBudgetCertificate.controlled,
      sampleOrdinaryDifferentialEquationsSystemsBudgetCertificate]
  · norm_num
      [OrdinaryDifferentialEquationsSystemsBudgetCertificate.budgetControlled,
        sampleOrdinaryDifferentialEquationsSystemsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List OrdinaryDifferentialEquationsSystemsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleOrdinaryDifferentialEquationsSystemsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleOrdinaryDifferentialEquationsSystemsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.OrdinaryDifferentialEquationsSystems
