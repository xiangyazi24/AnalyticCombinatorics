import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite difference tables for coefficient sequences.

The definitions here keep the discrete calculus side of coefficient
manipulations separate from analytic convergence arguments.
-/

namespace AnalyticCombinatorics.AppA.FiniteDifferenceTables

def forwardDelta (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  a (n + 1) - a n

def secondDelta (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  forwardDelta a (n + 1) - forwardDelta a n

def monotoneStep (a : ℕ → ℕ) : Prop :=
  ∀ n, a n ≤ a (n + 1)

theorem forwardDelta_add_of_step {a : ℕ → ℕ} {n : ℕ}
    (h : a n ≤ a (n + 1)) :
    forwardDelta a n + a n = a (n + 1) := by
  unfold forwardDelta
  omega

theorem monotoneStep.forwardDelta_add {a : ℕ → ℕ}
    (h : monotoneStep a) (n : ℕ) :
    forwardDelta a n + a n = a (n + 1) :=
  forwardDelta_add_of_step (h n)

def arithmeticSeq (step start : ℕ) (n : ℕ) : ℕ :=
  start + step * n

theorem arithmeticSeq_forwardDelta (step start n : ℕ) :
    forwardDelta (arithmeticSeq step start) n = step := by
  unfold forwardDelta arithmeticSeq
  rw [Nat.mul_succ]
  omega

example : forwardDelta (arithmeticSeq 3 2) 4 = 3 := by
  native_decide

example : secondDelta (arithmeticSeq 3 2) 4 = 0 := by
  native_decide

structure DifferenceWindow where
  index : ℕ
  value : ℕ
  firstDifference : ℕ
  secondDifference : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DifferenceWindow.firstControlled (w : DifferenceWindow) : Prop :=
  w.firstDifference ≤ w.value + w.slack

def DifferenceWindow.secondControlled (w : DifferenceWindow) : Prop :=
  w.secondDifference ≤ w.firstDifference + w.slack

def DifferenceWindow.ready (w : DifferenceWindow) : Prop :=
  w.firstControlled ∧ w.secondControlled

def DifferenceWindow.certificate (w : DifferenceWindow) : ℕ :=
  w.index + w.value + w.firstDifference + w.secondDifference + w.slack

theorem secondDifference_le_certificate (w : DifferenceWindow) :
    w.secondDifference ≤ w.certificate := by
  unfold DifferenceWindow.certificate
  omega

def sampleDifferenceWindow : DifferenceWindow :=
  { index := 4, value := 14, firstDifference := 3, secondDifference := 0, slack := 0 }

example : sampleDifferenceWindow.ready := by
  norm_num [sampleDifferenceWindow, DifferenceWindow.ready,
    DifferenceWindow.firstControlled, DifferenceWindow.secondControlled]


structure FiniteDifferenceTablesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteDifferenceTablesBudgetCertificate.controlled
    (c : FiniteDifferenceTablesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteDifferenceTablesBudgetCertificate.budgetControlled
    (c : FiniteDifferenceTablesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteDifferenceTablesBudgetCertificate.Ready
    (c : FiniteDifferenceTablesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteDifferenceTablesBudgetCertificate.size
    (c : FiniteDifferenceTablesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteDifferenceTables_budgetCertificate_le_size
    (c : FiniteDifferenceTablesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteDifferenceTablesBudgetCertificate :
    FiniteDifferenceTablesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteDifferenceTablesBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteDifferenceTablesBudgetCertificate.controlled,
      sampleFiniteDifferenceTablesBudgetCertificate]
  · norm_num [FiniteDifferenceTablesBudgetCertificate.budgetControlled,
      sampleFiniteDifferenceTablesBudgetCertificate]

example :
    sampleFiniteDifferenceTablesBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteDifferenceTablesBudgetCertificate.size := by
  apply finiteDifferenceTables_budgetCertificate_le_size
  constructor
  · norm_num [FiniteDifferenceTablesBudgetCertificate.controlled,
      sampleFiniteDifferenceTablesBudgetCertificate]
  · norm_num [FiniteDifferenceTablesBudgetCertificate.budgetControlled,
      sampleFiniteDifferenceTablesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteDifferenceTablesBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteDifferenceTablesBudgetCertificate.controlled,
      sampleFiniteDifferenceTablesBudgetCertificate]
  · norm_num [FiniteDifferenceTablesBudgetCertificate.budgetControlled,
      sampleFiniteDifferenceTablesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteDifferenceTablesBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteDifferenceTablesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteDifferenceTablesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteDifferenceTablesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteDifferenceTablesBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteDifferenceTables
