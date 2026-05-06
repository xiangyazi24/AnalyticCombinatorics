import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix A: arithmetical functions.

Finite divisor-sum and convolution windows for elementary arithmetic
functions used in generating-function examples.
-/

namespace AnalyticCombinatorics.AppA.ArithmeticalFunctions

/-- Finite Dirichlet convolution over divisors in a bounded window. -/
def dirichletConvolutionWindow (f g : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((List.range (n + 1)).filter (fun d => 0 < d ∧ d ∣ n)).foldl
    (fun total d => total + f d * g (n / d)) 0

/-- Constant-one arithmetic function. -/
def oneArithmetic (_ : ℕ) : ℕ :=
  1

/-- Identity arithmetic function. -/
def identityArithmetic (n : ℕ) : ℕ :=
  n

theorem dirichletConvolution_one_one_samples :
    dirichletConvolutionWindow oneArithmetic oneArithmetic 6 = 4 ∧
    dirichletConvolutionWindow oneArithmetic identityArithmetic 6 = 12 := by
  unfold dirichletConvolutionWindow oneArithmetic identityArithmetic
  native_decide

def divisorCountWindow (n : ℕ) : ℕ :=
  (List.range (n + 1)).filter (fun d => 0 < d ∧ d ∣ n) |>.length

def divisorSumWindow (n : ℕ) : ℕ :=
  ((List.range (n + 1)).filter (fun d => 0 < d ∧ d ∣ n)).sum

theorem divisor_samples :
    divisorCountWindow 6 = 4 ∧
    divisorSumWindow 6 = 12 ∧
    divisorCountWindow 12 = 6 := by
  native_decide

structure ArithmeticalFunctionWindow where
  argumentWindow : ℕ
  divisorWindow : ℕ
  convolutionSlack : ℕ
deriving DecidableEq, Repr

def arithmeticalFunctionReady (w : ArithmeticalFunctionWindow) : Prop :=
  0 < w.argumentWindow ∧
    w.divisorWindow ≤ w.argumentWindow + w.convolutionSlack

def arithmeticalFunctionBudget (w : ArithmeticalFunctionWindow) : ℕ :=
  w.argumentWindow + w.divisorWindow + w.convolutionSlack

theorem divisorWindow_le_budget (w : ArithmeticalFunctionWindow) :
    w.divisorWindow ≤ arithmeticalFunctionBudget w := by
  unfold arithmeticalFunctionBudget
  omega

def sampleArithmeticalFunctionWindow : ArithmeticalFunctionWindow :=
  { argumentWindow := 12, divisorWindow := 6, convolutionSlack := 1 }

example : arithmeticalFunctionReady sampleArithmeticalFunctionWindow := by
  norm_num [arithmeticalFunctionReady, sampleArithmeticalFunctionWindow]

structure ArithmeticalFunctionsBudgetCertificate where
  argumentWindow : ℕ
  divisorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ArithmeticalFunctionsBudgetCertificate.controlled
    (c : ArithmeticalFunctionsBudgetCertificate) : Prop :=
  0 < c.argumentWindow ∧ c.divisorWindow ≤ c.argumentWindow + c.slack

def ArithmeticalFunctionsBudgetCertificate.budgetControlled
    (c : ArithmeticalFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.argumentWindow + c.divisorWindow + c.slack

def ArithmeticalFunctionsBudgetCertificate.Ready
    (c : ArithmeticalFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ArithmeticalFunctionsBudgetCertificate.size
    (c : ArithmeticalFunctionsBudgetCertificate) : ℕ :=
  c.argumentWindow + c.divisorWindow + c.slack

theorem arithmeticalFunctions_budgetCertificate_le_size
    (c : ArithmeticalFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleArithmeticalFunctionsBudgetCertificate :
    ArithmeticalFunctionsBudgetCertificate :=
  { argumentWindow := 12
    divisorWindow := 6
    certificateBudgetWindow := 19
    slack := 1 }

example : sampleArithmeticalFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [ArithmeticalFunctionsBudgetCertificate.controlled,
      sampleArithmeticalFunctionsBudgetCertificate]
  · norm_num [ArithmeticalFunctionsBudgetCertificate.budgetControlled,
      sampleArithmeticalFunctionsBudgetCertificate]

/-- Finite executable readiness audit for arithmetical-function certificates. -/
def arithmeticalFunctionsBudgetCertificateListReady
    (data : List ArithmeticalFunctionsBudgetCertificate) : Bool :=
  data.all fun c =>
    0 < c.argumentWindow &&
      c.divisorWindow ≤ c.argumentWindow + c.slack &&
        c.certificateBudgetWindow ≤ c.argumentWindow + c.divisorWindow + c.slack

theorem arithmeticalFunctionsBudgetCertificateList_readyWindow :
    arithmeticalFunctionsBudgetCertificateListReady
      [sampleArithmeticalFunctionsBudgetCertificate,
       { argumentWindow := 10, divisorWindow := 4,
         certificateBudgetWindow := 15, slack := 1 }] = true := by
  unfold arithmeticalFunctionsBudgetCertificateListReady
    sampleArithmeticalFunctionsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleArithmeticalFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [ArithmeticalFunctionsBudgetCertificate.controlled,
      sampleArithmeticalFunctionsBudgetCertificate]
  · norm_num [ArithmeticalFunctionsBudgetCertificate.budgetControlled,
      sampleArithmeticalFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleArithmeticalFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleArithmeticalFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ArithmeticalFunctionsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleArithmeticalFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleArithmeticalFunctionsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.ArithmeticalFunctions
