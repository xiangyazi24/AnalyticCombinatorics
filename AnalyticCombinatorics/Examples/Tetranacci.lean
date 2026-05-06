import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Tetranacci compositions.

Compositions with parts in `{1, 2, 3, 4}` satisfy a four-term recurrence.
-/

namespace AnalyticCombinatorics.Examples.Tetranacci

/-- Count of compositions of `n` into parts `1`, `2`, `3`, and `4`. -/
def tetraCompositionCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | n + 4 =>
      tetraCompositionCount (n + 3) +
        tetraCompositionCount (n + 2) +
          tetraCompositionCount (n + 1) +
            tetraCompositionCount n

theorem tetraCompositionCount_rec (n : ℕ) :
    tetraCompositionCount (n + 4) =
      tetraCompositionCount (n + 3) +
        tetraCompositionCount (n + 2) +
          tetraCompositionCount (n + 1) +
            tetraCompositionCount n := rfl

example : tetraCompositionCount 0 = 1 := by native_decide
example : tetraCompositionCount 1 = 1 := by native_decide
example : tetraCompositionCount 2 = 2 := by native_decide
example : tetraCompositionCount 3 = 4 := by native_decide
example : tetraCompositionCount 4 = 8 := by native_decide
example : tetraCompositionCount 5 = 15 := by native_decide
example : tetraCompositionCount 6 = 29 := by native_decide
example : tetraCompositionCount 7 = 56 := by native_decide
example : tetraCompositionCount 8 = 108 := by native_decide
example : tetraCompositionCount 9 = 208 := by native_decide
example : tetraCompositionCount 10 = 401 := by native_decide

structure TetranacciCompositionWindow where
  total : ℕ
  ones : ℕ
  twos : ℕ
  threes : ℕ
  fours : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TetranacciCompositionWindow.weight (w : TetranacciCompositionWindow) : ℕ :=
  w.ones + 2 * w.twos + 3 * w.threes + 4 * w.fours

def TetranacciCompositionWindow.partCount (w : TetranacciCompositionWindow) : ℕ :=
  w.ones + w.twos + w.threes + w.fours

def TetranacciCompositionWindow.ready (w : TetranacciCompositionWindow) : Prop :=
  w.total = w.weight ∧ w.partCount ≤ w.total + w.slack

def TetranacciCompositionWindow.certificate (w : TetranacciCompositionWindow) : ℕ :=
  w.total + w.ones + w.twos + w.threes + w.fours + w.slack

theorem fours_le_certificate (w : TetranacciCompositionWindow) :
    w.fours ≤ w.certificate := by
  unfold TetranacciCompositionWindow.certificate
  omega

def sampleTetranacciCompositionWindow : TetranacciCompositionWindow :=
  { total := 11, ones := 1, twos := 1, threes := 0, fours := 2, slack := 0 }

example : sampleTetranacciCompositionWindow.ready := by
  norm_num [sampleTetranacciCompositionWindow, TetranacciCompositionWindow.ready,
    TetranacciCompositionWindow.weight, TetranacciCompositionWindow.partCount]

structure TetranacciBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TetranacciBudgetCertificate.controlled
    (c : TetranacciBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TetranacciBudgetCertificate.budgetControlled
    (c : TetranacciBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TetranacciBudgetCertificate.Ready
    (c : TetranacciBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TetranacciBudgetCertificate.size (c : TetranacciBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem tetranacci_budgetCertificate_le_size
    (c : TetranacciBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleTetranacciBudgetCertificate : TetranacciBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleTetranacciBudgetCertificate.Ready := by
  constructor
  · norm_num [TetranacciBudgetCertificate.controlled,
      sampleTetranacciBudgetCertificate]
  · norm_num [TetranacciBudgetCertificate.budgetControlled,
      sampleTetranacciBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTetranacciBudgetCertificate.Ready := by
  constructor
  · norm_num [TetranacciBudgetCertificate.controlled,
      sampleTetranacciBudgetCertificate]
  · norm_num [TetranacciBudgetCertificate.budgetControlled,
      sampleTetranacciBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTetranacciBudgetCertificate.certificateBudgetWindow ≤
      sampleTetranacciBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List TetranacciBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTetranacciBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTetranacciBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.Tetranacci
