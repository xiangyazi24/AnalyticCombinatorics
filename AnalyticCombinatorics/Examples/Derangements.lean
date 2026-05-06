import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Derangement examples.

This file records the standard recurrence for derangement numbers as a
self-contained executable table.
-/

namespace AnalyticCombinatorics.Examples.Derangements

/-- Derangement numbers with the recurrence `D(n+2) = (n+1)(D(n+1)+D n)`. -/
def derangementCount : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangementCount (n + 1) + derangementCount n)

theorem derangementCount_rec (n : ℕ) :
    derangementCount (n + 2) =
      (n + 1) * (derangementCount (n + 1) + derangementCount n) := rfl

example : derangementCount 0 = 1 := by native_decide
example : derangementCount 1 = 0 := by native_decide
example : derangementCount 2 = 1 := by native_decide
example : derangementCount 3 = 2 := by native_decide
example : derangementCount 4 = 9 := by native_decide
example : derangementCount 5 = 44 := by native_decide
example : derangementCount 6 = 265 := by native_decide
example : derangementCount 7 = 1854 := by native_decide
example : derangementCount 8 = 14833 := by native_decide
example : derangementCount 9 = 133496 := by native_decide
example : derangementCount 10 = 1334961 := by native_decide
example : derangementCount 11 = 14684570 := by native_decide

theorem derangementCount_values_0_to_11 :
    (List.range 12).map derangementCount =
      [1, 0, 1, 2, 9, 44, 265, 1854, 14833, 133496, 1334961, 14684570] := by
  native_decide

structure DerangementWindow where
  labels : ℕ
  fixedPoints : ℕ
  forbiddenPositions : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DerangementWindow.deranged (w : DerangementWindow) : Prop :=
  w.fixedPoints = 0

def DerangementWindow.forbiddenControlled (w : DerangementWindow) : Prop :=
  w.forbiddenPositions ≤ w.labels + w.slack

def DerangementWindow.ready (w : DerangementWindow) : Prop :=
  w.deranged ∧ w.forbiddenControlled

def DerangementWindow.certificate (w : DerangementWindow) : ℕ :=
  w.labels + w.fixedPoints + w.forbiddenPositions + w.slack

theorem forbiddenPositions_le_certificate (w : DerangementWindow) :
    w.forbiddenPositions ≤ w.certificate := by
  unfold DerangementWindow.certificate
  omega

def sampleDerangementWindow : DerangementWindow :=
  { labels := 6, fixedPoints := 0, forbiddenPositions := 6, slack := 0 }

example : sampleDerangementWindow.ready := by
  norm_num [sampleDerangementWindow, DerangementWindow.ready, DerangementWindow.deranged,
    DerangementWindow.forbiddenControlled]

example : sampleDerangementWindow.certificate = 12 := by
  native_decide

structure DerangementsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DerangementsBudgetCertificate.controlled
    (c : DerangementsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DerangementsBudgetCertificate.budgetControlled
    (c : DerangementsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DerangementsBudgetCertificate.Ready
    (c : DerangementsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DerangementsBudgetCertificate.size
    (c : DerangementsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem derangements_budgetCertificate_le_size
    (c : DerangementsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleDerangementsBudgetCertificate : DerangementsBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleDerangementsBudgetCertificate.Ready := by
  constructor
  · norm_num [DerangementsBudgetCertificate.controlled,
      sampleDerangementsBudgetCertificate]
  · norm_num [DerangementsBudgetCertificate.budgetControlled,
      sampleDerangementsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDerangementsBudgetCertificate.Ready := by
  constructor
  · norm_num [DerangementsBudgetCertificate.controlled,
      sampleDerangementsBudgetCertificate]
  · norm_num [DerangementsBudgetCertificate.budgetControlled,
      sampleDerangementsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDerangementsBudgetCertificate.certificateBudgetWindow ≤
      sampleDerangementsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List DerangementsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDerangementsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDerangementsBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.Derangements
