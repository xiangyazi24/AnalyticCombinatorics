import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite interval models.

This file records elementary interval length, overlap, and containment
checks for finite combinatorial decompositions.
-/

namespace AnalyticCombinatorics.AppA.FiniteIntervalModels

structure Interval where
  left : ℕ
  right : ℕ
deriving DecidableEq, Repr

def validInterval (i : Interval) : Prop :=
  i.left ≤ i.right

def intervalLength (i : Interval) : ℕ :=
  i.right - i.left + 1

def containsPoint (i : Interval) (x : ℕ) : Prop :=
  i.left ≤ x ∧ x ≤ i.right

theorem intervalLength_positive (i : Interval) :
    0 < intervalLength i := by
  unfold intervalLength
  omega

theorem containsPoint.valid {i : Interval} {x : ℕ}
    (h : containsPoint i x) :
    validInterval i := by
  unfold containsPoint validInterval at *
  omega

def sampleInterval : Interval :=
  { left := 3, right := 8 }

example : validInterval sampleInterval := by
  norm_num [validInterval, sampleInterval]

example : intervalLength sampleInterval = 6 := by
  native_decide

example : containsPoint sampleInterval 5 := by
  norm_num [containsPoint, sampleInterval]

structure IntervalWindow where
  left : ℕ
  right : ℕ
  length : ℕ
  markedPoints : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def IntervalWindow.valid (w : IntervalWindow) : Prop :=
  w.left ≤ w.right

def IntervalWindow.lengthControlled (w : IntervalWindow) : Prop :=
  w.length ≤ w.right - w.left + 1 + w.slack

def IntervalWindow.markedControlled (w : IntervalWindow) : Prop :=
  w.markedPoints ≤ w.length + w.slack

def IntervalWindow.ready (w : IntervalWindow) : Prop :=
  w.valid ∧ w.lengthControlled ∧ w.markedControlled

def IntervalWindow.certificate (w : IntervalWindow) : ℕ :=
  w.left + w.right + w.length + w.markedPoints + w.slack

theorem length_le_certificate (w : IntervalWindow) :
    w.length ≤ w.certificate := by
  unfold IntervalWindow.certificate
  omega

def sampleIntervalWindow : IntervalWindow :=
  { left := 3, right := 8, length := 6, markedPoints := 2, slack := 0 }

example : sampleIntervalWindow.ready := by
  norm_num [sampleIntervalWindow, IntervalWindow.ready, IntervalWindow.valid,
    IntervalWindow.lengthControlled, IntervalWindow.markedControlled]


structure FiniteIntervalModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteIntervalModelsBudgetCertificate.controlled
    (c : FiniteIntervalModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteIntervalModelsBudgetCertificate.budgetControlled
    (c : FiniteIntervalModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteIntervalModelsBudgetCertificate.Ready
    (c : FiniteIntervalModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteIntervalModelsBudgetCertificate.size
    (c : FiniteIntervalModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteIntervalModels_budgetCertificate_le_size
    (c : FiniteIntervalModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteIntervalModelsBudgetCertificate :
    FiniteIntervalModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteIntervalModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteIntervalModelsBudgetCertificate.controlled,
      sampleFiniteIntervalModelsBudgetCertificate]
  · norm_num [FiniteIntervalModelsBudgetCertificate.budgetControlled,
      sampleFiniteIntervalModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteIntervalModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteIntervalModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteIntervalModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteIntervalModelsBudgetCertificate.controlled,
      sampleFiniteIntervalModelsBudgetCertificate]
  · norm_num [FiniteIntervalModelsBudgetCertificate.budgetControlled,
      sampleFiniteIntervalModelsBudgetCertificate]

example :
    sampleFiniteIntervalModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteIntervalModelsBudgetCertificate.size := by
  apply finiteIntervalModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteIntervalModelsBudgetCertificate.controlled,
      sampleFiniteIntervalModelsBudgetCertificate]
  · norm_num [FiniteIntervalModelsBudgetCertificate.budgetControlled,
      sampleFiniteIntervalModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteIntervalModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteIntervalModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteIntervalModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteIntervalModels
