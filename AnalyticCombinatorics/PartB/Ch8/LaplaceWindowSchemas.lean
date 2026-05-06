import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Laplace-window schemas for saddle integrations.

The finite data records the central window, outer tail, and matching budget
for Laplace-method estimates.
-/

namespace AnalyticCombinatorics.PartB.Ch8.LaplaceWindowSchemas

structure LaplaceWindow where
  center : ℕ
  halfWidth : ℕ
  tailBudget : ℕ
deriving DecidableEq, Repr

def nonemptyWindow (w : LaplaceWindow) : Prop :=
  0 < w.halfWidth

def windowLeft (w : LaplaceWindow) : ℕ :=
  w.center - w.halfWidth

def windowRight (w : LaplaceWindow) : ℕ :=
  w.center + w.halfWidth

def laplaceWindowReady (w : LaplaceWindow) : Prop :=
  nonemptyWindow w ∧ w.tailBudget ≤ windowRight w

theorem windowLeft_le_center (w : LaplaceWindow) :
    windowLeft w ≤ w.center := by
  unfold windowLeft
  omega

theorem laplaceWindowReady.nonempty {w : LaplaceWindow}
    (h : laplaceWindowReady w) :
    nonemptyWindow w := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

def sampleWindow : LaplaceWindow :=
  { center := 10, halfWidth := 3, tailBudget := 5 }

example : laplaceWindowReady sampleWindow := by
  norm_num [laplaceWindowReady, nonemptyWindow, windowRight, sampleWindow]

example : windowLeft sampleWindow = 7 := by
  native_decide

example : windowRight sampleWindow = 13 := by
  native_decide

structure LaplaceWindowBudgetCertificate where
  centerWindow : ℕ
  halfWidthWindow : ℕ
  tailBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaplaceWindowBudgetCertificate.controlled
    (c : LaplaceWindowBudgetCertificate) : Prop :=
  0 < c.halfWidthWindow ∧
    c.tailBudgetWindow ≤ c.centerWindow + c.halfWidthWindow + c.slack

def LaplaceWindowBudgetCertificate.budgetControlled
    (c : LaplaceWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.centerWindow + c.halfWidthWindow + c.tailBudgetWindow + c.slack

def LaplaceWindowBudgetCertificate.Ready
    (c : LaplaceWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LaplaceWindowBudgetCertificate.size
    (c : LaplaceWindowBudgetCertificate) : ℕ :=
  c.centerWindow + c.halfWidthWindow + c.tailBudgetWindow + c.slack

theorem laplaceWindow_budgetCertificate_le_size
    (c : LaplaceWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLaplaceWindowBudgetCertificate :
    LaplaceWindowBudgetCertificate :=
  { centerWindow := 10
    halfWidthWindow := 3
    tailBudgetWindow := 5
    certificateBudgetWindow := 19
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLaplaceWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [LaplaceWindowBudgetCertificate.controlled,
      sampleLaplaceWindowBudgetCertificate]
  · norm_num [LaplaceWindowBudgetCertificate.budgetControlled,
      sampleLaplaceWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLaplaceWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplaceWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLaplaceWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [LaplaceWindowBudgetCertificate.controlled,
      sampleLaplaceWindowBudgetCertificate]
  · norm_num [LaplaceWindowBudgetCertificate.budgetControlled,
      sampleLaplaceWindowBudgetCertificate]

example :
    sampleLaplaceWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplaceWindowBudgetCertificate.size := by
  apply laplaceWindow_budgetCertificate_le_size
  constructor
  · norm_num [LaplaceWindowBudgetCertificate.controlled,
      sampleLaplaceWindowBudgetCertificate]
  · norm_num [LaplaceWindowBudgetCertificate.budgetControlled,
      sampleLaplaceWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LaplaceWindowBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleLaplaceWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleLaplaceWindowBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.LaplaceWindowSchemas
