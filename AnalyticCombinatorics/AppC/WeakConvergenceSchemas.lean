import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Weak-convergence schema bookkeeping.

The finite record stores tightness, test-function count, and error budget
for weak limit arguments.
-/

namespace AnalyticCombinatorics.AppC.WeakConvergenceSchemas

structure WeakConvergenceData where
  tight : Prop
  testFunctionCount : ℕ
  discrepancyBudget : ℕ
deriving Repr

def nonemptyTestFamily (d : WeakConvergenceData) : Prop :=
  0 < d.testFunctionCount

def weakConvergenceReady (d : WeakConvergenceData) : Prop :=
  d.tight ∧ nonemptyTestFamily d

def weakConvergenceBudget (d : WeakConvergenceData) : ℕ :=
  d.testFunctionCount + d.discrepancyBudget

theorem weakConvergenceReady.tight {d : WeakConvergenceData}
    (h : weakConvergenceReady d) :
    d.tight := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem testFunctionCount_le_budget (d : WeakConvergenceData) :
    d.testFunctionCount ≤ weakConvergenceBudget d := by
  unfold weakConvergenceBudget
  omega

def sampleWeakConvergence : WeakConvergenceData :=
  { tight := 2 ≤ 6, testFunctionCount := 6, discrepancyBudget := 2 }

example : weakConvergenceReady sampleWeakConvergence := by
  norm_num [weakConvergenceReady, nonemptyTestFamily, sampleWeakConvergence]

example : weakConvergenceBudget sampleWeakConvergence = 8 := by
  native_decide

structure WeakConvergenceWindow where
  supportCutoff : ℕ
  testFunctions : ℕ
  discrepancyBudget : ℕ
  tightnessSlack : ℕ
deriving DecidableEq, Repr

def WeakConvergenceWindow.testFamilyReady (w : WeakConvergenceWindow) : Prop :=
  0 < w.testFunctions

def WeakConvergenceWindow.discrepancyControlled (w : WeakConvergenceWindow) : Prop :=
  w.discrepancyBudget ≤ w.supportCutoff + w.tightnessSlack

def WeakConvergenceWindow.ready (w : WeakConvergenceWindow) : Prop :=
  w.testFamilyReady ∧ w.discrepancyControlled

def WeakConvergenceWindow.certificate (w : WeakConvergenceWindow) : ℕ :=
  w.supportCutoff + w.testFunctions + w.discrepancyBudget + w.tightnessSlack

theorem discrepancyBudget_le_certificate (w : WeakConvergenceWindow) :
    w.discrepancyBudget ≤ w.certificate := by
  unfold WeakConvergenceWindow.certificate
  omega

def sampleWeakConvergenceWindow : WeakConvergenceWindow :=
  { supportCutoff := 6, testFunctions := 6, discrepancyBudget := 2, tightnessSlack := 0 }

example : sampleWeakConvergenceWindow.ready := by
  norm_num [sampleWeakConvergenceWindow, WeakConvergenceWindow.ready,
    WeakConvergenceWindow.testFamilyReady, WeakConvergenceWindow.discrepancyControlled]

structure WeakConvergenceRefinementWindow where
  supportWindow : ℕ
  testWindow : ℕ
  discrepancyWindow : ℕ
  weakBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeakConvergenceRefinementWindow.discrepancyControlled
    (w : WeakConvergenceRefinementWindow) : Prop :=
  w.discrepancyWindow ≤ w.supportWindow + w.slack

def weakConvergenceRefinementWindowReady
    (w : WeakConvergenceRefinementWindow) : Prop :=
  0 < w.testWindow ∧ w.discrepancyControlled ∧
    w.weakBudget ≤ w.supportWindow + w.testWindow + w.discrepancyWindow + w.slack

def WeakConvergenceRefinementWindow.certificate
    (w : WeakConvergenceRefinementWindow) : ℕ :=
  w.supportWindow + w.testWindow + w.discrepancyWindow + w.weakBudget + w.slack

theorem weakConvergenceRefinement_budget_le_certificate
    (w : WeakConvergenceRefinementWindow) :
    w.weakBudget ≤ w.certificate := by
  unfold WeakConvergenceRefinementWindow.certificate
  omega

def sampleWeakConvergenceRefinementWindow : WeakConvergenceRefinementWindow :=
  { supportWindow := 6, testWindow := 6, discrepancyWindow := 2,
    weakBudget := 15, slack := 1 }

example : weakConvergenceRefinementWindowReady
    sampleWeakConvergenceRefinementWindow := by
  norm_num [weakConvergenceRefinementWindowReady,
    WeakConvergenceRefinementWindow.discrepancyControlled,
    sampleWeakConvergenceRefinementWindow]


structure WeakConvergenceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeakConvergenceSchemasBudgetCertificate.controlled
    (c : WeakConvergenceSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def WeakConvergenceSchemasBudgetCertificate.budgetControlled
    (c : WeakConvergenceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def WeakConvergenceSchemasBudgetCertificate.Ready
    (c : WeakConvergenceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def WeakConvergenceSchemasBudgetCertificate.size
    (c : WeakConvergenceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem weakConvergenceSchemas_budgetCertificate_le_size
    (c : WeakConvergenceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleWeakConvergenceSchemasBudgetCertificate :
    WeakConvergenceSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleWeakConvergenceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [WeakConvergenceSchemasBudgetCertificate.controlled,
      sampleWeakConvergenceSchemasBudgetCertificate]
  · norm_num [WeakConvergenceSchemasBudgetCertificate.budgetControlled,
      sampleWeakConvergenceSchemasBudgetCertificate]

example :
    sampleWeakConvergenceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleWeakConvergenceSchemasBudgetCertificate.size := by
  apply weakConvergenceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [WeakConvergenceSchemasBudgetCertificate.controlled,
      sampleWeakConvergenceSchemasBudgetCertificate]
  · norm_num [WeakConvergenceSchemasBudgetCertificate.budgetControlled,
      sampleWeakConvergenceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleWeakConvergenceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [WeakConvergenceSchemasBudgetCertificate.controlled,
      sampleWeakConvergenceSchemasBudgetCertificate]
  · norm_num [WeakConvergenceSchemasBudgetCertificate.budgetControlled,
      sampleWeakConvergenceSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleWeakConvergenceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleWeakConvergenceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List WeakConvergenceSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleWeakConvergenceSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleWeakConvergenceSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.WeakConvergenceSchemas
