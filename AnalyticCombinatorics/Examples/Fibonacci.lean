import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Fibonacci compositions.

Compositions with parts in `{1, 2}` are counted by shifted Fibonacci numbers.
-/

namespace AnalyticCombinatorics.Examples.Fibonacci

/-- Count of compositions of `n` into parts `1` and `2`. -/
def fibCompositionCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => fibCompositionCount (n + 1) + fibCompositionCount n

theorem fibCompositionCount_rec (n : ℕ) :
    fibCompositionCount (n + 2) =
      fibCompositionCount (n + 1) + fibCompositionCount n := rfl

example : fibCompositionCount 0 = 1 := by native_decide
example : fibCompositionCount 1 = 1 := by native_decide
example : fibCompositionCount 2 = 2 := by native_decide
example : fibCompositionCount 3 = 3 := by native_decide
example : fibCompositionCount 4 = 5 := by native_decide
example : fibCompositionCount 5 = 8 := by native_decide
example : fibCompositionCount 6 = 13 := by native_decide
example : fibCompositionCount 7 = 21 := by native_decide
example : fibCompositionCount 8 = 34 := by native_decide
example : fibCompositionCount 9 = 55 := by native_decide
example : fibCompositionCount 10 = 89 := by native_decide

theorem fibCompositionCount_eq_shifted_fib_upto_10 :
    (List.range 11).all
      (fun n => fibCompositionCount n == Nat.fib (n + 1)) = true := by
  native_decide

structure FibonacciCompositionWindow where
  total : ℕ
  ones : ℕ
  twos : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FibonacciCompositionWindow.weight (w : FibonacciCompositionWindow) : ℕ :=
  w.ones + 2 * w.twos

def FibonacciCompositionWindow.partCount (w : FibonacciCompositionWindow) : ℕ :=
  w.ones + w.twos

def FibonacciCompositionWindow.realizesTotal (w : FibonacciCompositionWindow) : Prop :=
  w.total = w.weight

def FibonacciCompositionWindow.lengthControlled (w : FibonacciCompositionWindow) : Prop :=
  w.partCount ≤ w.total + w.slack

def FibonacciCompositionWindow.ready (w : FibonacciCompositionWindow) : Prop :=
  w.realizesTotal ∧ w.lengthControlled

def FibonacciCompositionWindow.certificate (w : FibonacciCompositionWindow) : ℕ :=
  w.total + w.ones + w.twos + w.slack

theorem twos_le_certificate (w : FibonacciCompositionWindow) :
    w.twos ≤ w.certificate := by
  unfold FibonacciCompositionWindow.certificate
  omega

def sampleFibonacciCompositionWindow : FibonacciCompositionWindow :=
  { total := 7, ones := 3, twos := 2, slack := 0 }

example : sampleFibonacciCompositionWindow.ready := by
  norm_num [sampleFibonacciCompositionWindow, FibonacciCompositionWindow.ready,
    FibonacciCompositionWindow.realizesTotal, FibonacciCompositionWindow.lengthControlled,
    FibonacciCompositionWindow.weight, FibonacciCompositionWindow.partCount]

example : sampleFibonacciCompositionWindow.partCount = 5 := by
  norm_num [sampleFibonacciCompositionWindow, FibonacciCompositionWindow.partCount]

theorem fibCompositionCount_monotone_sample :
    fibCompositionCount 7 ≤ fibCompositionCount 8 := by
  native_decide

structure FibonacciBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FibonacciBudgetCertificate.controlled
    (c : FibonacciBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FibonacciBudgetCertificate.budgetControlled
    (c : FibonacciBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FibonacciBudgetCertificate.Ready (c : FibonacciBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FibonacciBudgetCertificate.size (c : FibonacciBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem fibonacci_budgetCertificate_le_size
    (c : FibonacciBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleFibonacciBudgetCertificate : FibonacciBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleFibonacciBudgetCertificate.Ready := by
  constructor
  · norm_num [FibonacciBudgetCertificate.controlled,
      sampleFibonacciBudgetCertificate]
  · norm_num [FibonacciBudgetCertificate.budgetControlled,
      sampleFibonacciBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFibonacciBudgetCertificate.Ready := by
  constructor
  · norm_num [FibonacciBudgetCertificate.controlled,
      sampleFibonacciBudgetCertificate]
  · norm_num [FibonacciBudgetCertificate.budgetControlled,
      sampleFibonacciBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFibonacciBudgetCertificate.certificateBudgetWindow ≤
      sampleFibonacciBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FibonacciBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFibonacciBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFibonacciBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.Fibonacci
