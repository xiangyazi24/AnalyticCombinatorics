import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Compositions into odd parts.

The number of compositions of `n` into positive odd parts follows the
Fibonacci recurrence with initial values `1, 1`.
-/

namespace AnalyticCombinatorics.Examples.CompositionsOdd

/-- Count of compositions of `n` into positive odd parts. -/
def oddCompositionCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => oddCompositionCount (n + 2) + oddCompositionCount (n + 1)

@[simp]
theorem oddCompositionCount_zero : oddCompositionCount 0 = 1 := rfl

@[simp]
theorem oddCompositionCount_one : oddCompositionCount 1 = 1 := rfl

theorem oddCompositionCount_rec (n : ℕ) :
    oddCompositionCount (n + 3) =
      oddCompositionCount (n + 2) + oddCompositionCount (n + 1) := rfl

example : oddCompositionCount 0 = 1 := by native_decide
example : oddCompositionCount 1 = 1 := by native_decide
example : oddCompositionCount 2 = 1 := by native_decide
example : oddCompositionCount 3 = 2 := by native_decide
example : oddCompositionCount 4 = 3 := by native_decide
example : oddCompositionCount 5 = 5 := by native_decide
example : oddCompositionCount 6 = 8 := by native_decide
example : oddCompositionCount 7 = 13 := by native_decide
example : oddCompositionCount 8 = 21 := by native_decide
example : oddCompositionCount 9 = 34 := by native_decide
example : oddCompositionCount 10 = 55 := by native_decide

/-- The first eleven values agree with shifted Fibonacci numbers. -/
theorem oddCompositionCount_eq_fib_upto_10 :
    (List.range 11).all
      (fun n => oddCompositionCount n == if n = 0 then 1 else Nat.fib n) = true := by
  native_decide

structure OddCompositionWindow where
  total : ℕ
  oddParts : ℕ
  maxOddPart : ℕ
  paritySlack : ℕ
deriving DecidableEq, Repr

def OddCompositionWindow.oddPartControlled (w : OddCompositionWindow) : Prop :=
  w.oddParts ≤ w.total + w.paritySlack

def OddCompositionWindow.sizeControlled (w : OddCompositionWindow) : Prop :=
  w.total ≤ w.oddParts * w.maxOddPart + w.paritySlack

def OddCompositionWindow.ready (w : OddCompositionWindow) : Prop :=
  w.oddPartControlled ∧ w.sizeControlled

def OddCompositionWindow.certificate (w : OddCompositionWindow) : ℕ :=
  w.total + w.oddParts + w.maxOddPart + w.paritySlack

theorem oddParts_le_certificate (w : OddCompositionWindow) :
    w.oddParts ≤ w.certificate := by
  unfold OddCompositionWindow.certificate
  omega

def sampleOddCompositionWindow : OddCompositionWindow :=
  { total := 7, oddParts := 3, maxOddPart := 5, paritySlack := 0 }

example : sampleOddCompositionWindow.ready := by
  norm_num [sampleOddCompositionWindow, OddCompositionWindow.ready,
    OddCompositionWindow.oddPartControlled, OddCompositionWindow.sizeControlled]

structure CompositionsOddBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompositionsOddBudgetCertificate.controlled
    (c : CompositionsOddBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CompositionsOddBudgetCertificate.budgetControlled
    (c : CompositionsOddBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CompositionsOddBudgetCertificate.Ready
    (c : CompositionsOddBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CompositionsOddBudgetCertificate.size
    (c : CompositionsOddBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem compositionsOdd_budgetCertificate_le_size
    (c : CompositionsOddBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleCompositionsOddBudgetCertificate : CompositionsOddBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleCompositionsOddBudgetCertificate.Ready := by
  constructor
  · norm_num [CompositionsOddBudgetCertificate.controlled,
      sampleCompositionsOddBudgetCertificate]
  · norm_num [CompositionsOddBudgetCertificate.budgetControlled,
      sampleCompositionsOddBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCompositionsOddBudgetCertificate.Ready := by
  constructor
  · norm_num [CompositionsOddBudgetCertificate.controlled,
      sampleCompositionsOddBudgetCertificate]
  · norm_num [CompositionsOddBudgetCertificate.budgetControlled,
      sampleCompositionsOddBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCompositionsOddBudgetCertificate.certificateBudgetWindow ≤
      sampleCompositionsOddBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CompositionsOddBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCompositionsOddBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCompositionsOddBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.CompositionsOdd
