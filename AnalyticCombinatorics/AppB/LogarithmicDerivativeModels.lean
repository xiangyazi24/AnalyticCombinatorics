import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Logarithmic derivative bookkeeping.

The analytic logarithmic derivative is represented by zero and pole counts
plus a regular remainder budget.
-/

namespace AnalyticCombinatorics.AppB.LogarithmicDerivativeModels

structure LogDerivativeDatum where
  zeroCount : ℕ
  poleCount : ℕ
  regularRemainder : ℕ
deriving DecidableEq, Repr

def divisorBalance (d : LogDerivativeDatum) : ℤ :=
  (d.zeroCount : ℤ) - (d.poleCount : ℤ)

def regularBudget (d : LogDerivativeDatum) : ℕ :=
  d.zeroCount + d.poleCount + d.regularRemainder

def hasDivisorData (d : LogDerivativeDatum) : Prop :=
  0 < d.zeroCount + d.poleCount

theorem zeroCount_le_regularBudget (d : LogDerivativeDatum) :
    d.zeroCount ≤ regularBudget d := by
  unfold regularBudget
  omega

theorem hasDivisorData_of_zero_pos {d : LogDerivativeDatum}
    (h : 0 < d.zeroCount) :
    hasDivisorData d := by
  unfold hasDivisorData
  omega

def sampleLogDerivative : LogDerivativeDatum :=
  { zeroCount := 5, poleCount := 2, regularRemainder := 3 }

example : divisorBalance sampleLogDerivative = 3 := by
  native_decide

example : regularBudget sampleLogDerivative = 10 := by
  native_decide

example : hasDivisorData sampleLogDerivative := by
  norm_num [hasDivisorData, sampleLogDerivative]

structure LogDerivativeWindow where
  zeroCount : ℕ
  poleCount : ℕ
  regularRemainder : ℕ
  derivativeBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogDerivativeWindow.divisorReady (w : LogDerivativeWindow) : Prop :=
  0 < w.zeroCount + w.poleCount

def LogDerivativeWindow.derivativeControlled (w : LogDerivativeWindow) : Prop :=
  w.derivativeBudget ≤ w.zeroCount + w.poleCount + w.regularRemainder + w.slack

def LogDerivativeWindow.ready (w : LogDerivativeWindow) : Prop :=
  w.divisorReady ∧ w.derivativeControlled

def LogDerivativeWindow.certificate (w : LogDerivativeWindow) : ℕ :=
  w.zeroCount + w.poleCount + w.regularRemainder + w.derivativeBudget + w.slack

theorem derivativeBudget_le_certificate (w : LogDerivativeWindow) :
    w.derivativeBudget ≤ w.certificate := by
  unfold LogDerivativeWindow.certificate
  omega

def sampleLogDerivativeWindow : LogDerivativeWindow :=
  { zeroCount := 5, poleCount := 2, regularRemainder := 3, derivativeBudget := 8, slack := 0 }

example : sampleLogDerivativeWindow.ready := by
  norm_num [sampleLogDerivativeWindow, LogDerivativeWindow.ready,
    LogDerivativeWindow.divisorReady, LogDerivativeWindow.derivativeControlled]


structure LogarithmicDerivativeModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogarithmicDerivativeModelsBudgetCertificate.controlled
    (c : LogarithmicDerivativeModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LogarithmicDerivativeModelsBudgetCertificate.budgetControlled
    (c : LogarithmicDerivativeModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LogarithmicDerivativeModelsBudgetCertificate.Ready
    (c : LogarithmicDerivativeModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LogarithmicDerivativeModelsBudgetCertificate.size
    (c : LogarithmicDerivativeModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem logarithmicDerivativeModels_budgetCertificate_le_size
    (c : LogarithmicDerivativeModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLogarithmicDerivativeModelsBudgetCertificate :
    LogarithmicDerivativeModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLogarithmicDerivativeModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [LogarithmicDerivativeModelsBudgetCertificate.controlled,
      sampleLogarithmicDerivativeModelsBudgetCertificate]
  · norm_num [LogarithmicDerivativeModelsBudgetCertificate.budgetControlled,
      sampleLogarithmicDerivativeModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLogarithmicDerivativeModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleLogarithmicDerivativeModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLogarithmicDerivativeModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [LogarithmicDerivativeModelsBudgetCertificate.controlled,
      sampleLogarithmicDerivativeModelsBudgetCertificate]
  · norm_num [LogarithmicDerivativeModelsBudgetCertificate.budgetControlled,
      sampleLogarithmicDerivativeModelsBudgetCertificate]

example :
    sampleLogarithmicDerivativeModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleLogarithmicDerivativeModelsBudgetCertificate.size := by
  apply logarithmicDerivativeModels_budgetCertificate_le_size
  constructor
  · norm_num [LogarithmicDerivativeModelsBudgetCertificate.controlled,
      sampleLogarithmicDerivativeModelsBudgetCertificate]
  · norm_num [LogarithmicDerivativeModelsBudgetCertificate.budgetControlled,
      sampleLogarithmicDerivativeModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LogarithmicDerivativeModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLogarithmicDerivativeModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLogarithmicDerivativeModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.LogarithmicDerivativeModels
