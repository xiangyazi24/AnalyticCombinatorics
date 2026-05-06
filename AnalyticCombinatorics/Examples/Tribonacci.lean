import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Tribonacci compositions.

Compositions with parts in `{1, 2, 3}` satisfy a three-term recurrence.
-/

namespace AnalyticCombinatorics.Examples.Tribonacci

/-- Count of compositions of `n` into parts `1`, `2`, and `3`. -/
def tribCompositionCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | n + 3 =>
      tribCompositionCount (n + 2) +
        tribCompositionCount (n + 1) +
          tribCompositionCount n

theorem tribCompositionCount_rec (n : ℕ) :
    tribCompositionCount (n + 3) =
      tribCompositionCount (n + 2) +
        tribCompositionCount (n + 1) +
          tribCompositionCount n := rfl

example : tribCompositionCount 0 = 1 := by native_decide
example : tribCompositionCount 1 = 1 := by native_decide
example : tribCompositionCount 2 = 2 := by native_decide
example : tribCompositionCount 3 = 4 := by native_decide
example : tribCompositionCount 4 = 7 := by native_decide
example : tribCompositionCount 5 = 13 := by native_decide
example : tribCompositionCount 6 = 24 := by native_decide
example : tribCompositionCount 7 = 44 := by native_decide
example : tribCompositionCount 8 = 81 := by native_decide
example : tribCompositionCount 9 = 149 := by native_decide
example : tribCompositionCount 10 = 274 := by native_decide

structure TribonacciCompositionWindow where
  total : ℕ
  ones : ℕ
  twos : ℕ
  threes : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TribonacciCompositionWindow.weight (w : TribonacciCompositionWindow) : ℕ :=
  w.ones + 2 * w.twos + 3 * w.threes

def TribonacciCompositionWindow.partCount (w : TribonacciCompositionWindow) : ℕ :=
  w.ones + w.twos + w.threes

def TribonacciCompositionWindow.ready (w : TribonacciCompositionWindow) : Prop :=
  w.total = w.weight ∧ w.partCount ≤ w.total + w.slack

def TribonacciCompositionWindow.certificate (w : TribonacciCompositionWindow) : ℕ :=
  w.total + w.ones + w.twos + w.threes + w.slack

theorem threes_le_certificate (w : TribonacciCompositionWindow) :
    w.threes ≤ w.certificate := by
  unfold TribonacciCompositionWindow.certificate
  omega

def sampleTribonacciCompositionWindow : TribonacciCompositionWindow :=
  { total := 10, ones := 2, twos := 1, threes := 2, slack := 0 }

example : sampleTribonacciCompositionWindow.ready := by
  norm_num [sampleTribonacciCompositionWindow, TribonacciCompositionWindow.ready,
    TribonacciCompositionWindow.weight, TribonacciCompositionWindow.partCount]

example : sampleTribonacciCompositionWindow.partCount = 5 := by
  native_decide

structure TribonacciBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TribonacciBudgetCertificate.controlled
    (c : TribonacciBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TribonacciBudgetCertificate.budgetControlled
    (c : TribonacciBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TribonacciBudgetCertificate.Ready
    (c : TribonacciBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TribonacciBudgetCertificate.size (c : TribonacciBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem tribonacci_budgetCertificate_le_size
    (c : TribonacciBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleTribonacciBudgetCertificate : TribonacciBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleTribonacciBudgetCertificate.Ready := by
  constructor
  · norm_num [TribonacciBudgetCertificate.controlled,
      sampleTribonacciBudgetCertificate]
  · norm_num [TribonacciBudgetCertificate.budgetControlled,
      sampleTribonacciBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTribonacciBudgetCertificate.Ready := by
  constructor
  · norm_num [TribonacciBudgetCertificate.controlled,
      sampleTribonacciBudgetCertificate]
  · norm_num [TribonacciBudgetCertificate.budgetControlled,
      sampleTribonacciBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTribonacciBudgetCertificate.certificateBudgetWindow ≤
      sampleTribonacciBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List TribonacciBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTribonacciBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTribonacciBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.Tribonacci
