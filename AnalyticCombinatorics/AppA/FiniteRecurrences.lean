import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite recurrence templates for coefficient sequences.

These definitions provide executable recurrence schemas that can be reused
when coefficients are generated from rational or algebraic specifications.
-/

namespace AnalyticCombinatorics.AppA.FiniteRecurrences

def affineStep (mult shift value : ℕ) : ℕ :=
  mult * value + shift

def iterateAffine (mult shift start : ℕ) : ℕ → ℕ
  | 0 => start
  | n + 1 => affineStep mult shift (iterateAffine mult shift start n)

def firstOrderBounded (u bound : ℕ → ℕ) : Prop :=
  ∀ n, u (n + 1) ≤ u n + bound n

theorem iterateAffine_zero (mult shift start : ℕ) :
    iterateAffine mult shift start 0 = start := by
  rfl

theorem iterateAffine_succ (mult shift start n : ℕ) :
    iterateAffine mult shift start (n + 1) =
      affineStep mult shift (iterateAffine mult shift start n) := by
  rfl

theorem zero_firstOrderBounded (bound : ℕ → ℕ) :
    firstOrderBounded (fun _ => 0) bound := by
  intro n
  simp

def fibonacciLike : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => fibonacciLike (n + 1) + fibonacciLike n

example : affineStep 2 3 5 = 13 := by
  native_decide

example : iterateAffine 2 1 0 4 = 15 := by
  native_decide

example : fibonacciLike 6 = 13 := by
  native_decide

structure RecurrenceWindow where
  order : ℕ
  initialTerms : ℕ
  coefficientBudget : ℕ
  generatedTerms : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RecurrenceWindow.orderReady (w : RecurrenceWindow) : Prop :=
  0 < w.order ∧ w.order ≤ w.initialTerms + w.slack

def RecurrenceWindow.generationControlled (w : RecurrenceWindow) : Prop :=
  w.generatedTerms ≤ w.initialTerms + w.coefficientBudget + w.slack

def RecurrenceWindow.ready (w : RecurrenceWindow) : Prop :=
  w.orderReady ∧ w.generationControlled

def RecurrenceWindow.certificate (w : RecurrenceWindow) : ℕ :=
  w.order + w.initialTerms + w.coefficientBudget + w.generatedTerms + w.slack

theorem generatedTerms_le_certificate (w : RecurrenceWindow) :
    w.generatedTerms ≤ w.certificate := by
  unfold RecurrenceWindow.certificate
  omega

def sampleRecurrenceWindow : RecurrenceWindow :=
  { order := 2, initialTerms := 2, coefficientBudget := 5, generatedTerms := 6, slack := 0 }

example : sampleRecurrenceWindow.ready := by
  norm_num [sampleRecurrenceWindow, RecurrenceWindow.ready,
    RecurrenceWindow.orderReady, RecurrenceWindow.generationControlled]


structure FiniteRecurrencesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteRecurrencesBudgetCertificate.controlled
    (c : FiniteRecurrencesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteRecurrencesBudgetCertificate.budgetControlled
    (c : FiniteRecurrencesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteRecurrencesBudgetCertificate.Ready
    (c : FiniteRecurrencesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteRecurrencesBudgetCertificate.size
    (c : FiniteRecurrencesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteRecurrences_budgetCertificate_le_size
    (c : FiniteRecurrencesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteRecurrencesBudgetCertificate :
    FiniteRecurrencesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteRecurrencesBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRecurrencesBudgetCertificate.controlled,
      sampleFiniteRecurrencesBudgetCertificate]
  · norm_num [FiniteRecurrencesBudgetCertificate.budgetControlled,
      sampleFiniteRecurrencesBudgetCertificate]

example :
    sampleFiniteRecurrencesBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRecurrencesBudgetCertificate.size := by
  apply finiteRecurrences_budgetCertificate_le_size
  constructor
  · norm_num [FiniteRecurrencesBudgetCertificate.controlled,
      sampleFiniteRecurrencesBudgetCertificate]
  · norm_num [FiniteRecurrencesBudgetCertificate.budgetControlled,
      sampleFiniteRecurrencesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteRecurrencesBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRecurrencesBudgetCertificate.controlled,
      sampleFiniteRecurrencesBudgetCertificate]
  · norm_num [FiniteRecurrencesBudgetCertificate.budgetControlled,
      sampleFiniteRecurrencesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteRecurrencesBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRecurrencesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteRecurrencesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteRecurrencesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteRecurrencesBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteRecurrences
