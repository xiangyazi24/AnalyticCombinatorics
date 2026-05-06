import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bounded continuous test window schemas.

This module records finite bookkeeping for bounded continuous tests.
-/

namespace AnalyticCombinatorics.AppC.BoundedContinuousTestWindowSchemas

structure BoundedContinuousTestWindowData where
  testCount : ℕ
  continuityWindow : ℕ
  testSlack : ℕ
deriving DecidableEq, Repr

def hasTestCount (d : BoundedContinuousTestWindowData) : Prop :=
  0 < d.testCount

def continuityWindowControlled
    (d : BoundedContinuousTestWindowData) : Prop :=
  d.continuityWindow ≤ d.testCount + d.testSlack

def boundedContinuousTestReady
    (d : BoundedContinuousTestWindowData) : Prop :=
  hasTestCount d ∧ continuityWindowControlled d

def boundedContinuousTestBudget
    (d : BoundedContinuousTestWindowData) : ℕ :=
  d.testCount + d.continuityWindow + d.testSlack

theorem boundedContinuousTestReady.hasTestCount
    {d : BoundedContinuousTestWindowData}
    (h : boundedContinuousTestReady d) :
    hasTestCount d ∧ continuityWindowControlled d ∧
      d.continuityWindow ≤ boundedContinuousTestBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold boundedContinuousTestBudget
  omega

theorem continuityWindow_le_budget
    (d : BoundedContinuousTestWindowData) :
    d.continuityWindow ≤ boundedContinuousTestBudget d := by
  unfold boundedContinuousTestBudget
  omega

def sampleBoundedContinuousTestWindowData :
    BoundedContinuousTestWindowData :=
  { testCount := 6, continuityWindow := 8, testSlack := 3 }

example : boundedContinuousTestReady
    sampleBoundedContinuousTestWindowData := by
  norm_num [boundedContinuousTestReady, hasTestCount]
  norm_num [continuityWindowControlled, sampleBoundedContinuousTestWindowData]

example :
    boundedContinuousTestBudget sampleBoundedContinuousTestWindowData = 17 := by
  native_decide

structure BoundedContinuousTestCertificateWindow where
  testWindow : ℕ
  continuityWindow : ℕ
  testSlack : ℕ
  continuityBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundedContinuousTestCertificateWindow.continuityControlled
    (w : BoundedContinuousTestCertificateWindow) : Prop :=
  w.continuityWindow ≤ w.testWindow + w.testSlack + w.slack

def boundedContinuousTestCertificateReady
    (w : BoundedContinuousTestCertificateWindow) : Prop :=
  0 < w.testWindow ∧ w.continuityControlled ∧
    w.continuityBudget ≤ w.testWindow + w.continuityWindow + w.slack

def BoundedContinuousTestCertificateWindow.certificate
    (w : BoundedContinuousTestCertificateWindow) : ℕ :=
  w.testWindow + w.continuityWindow + w.testSlack + w.continuityBudget + w.slack

theorem boundedContinuousTest_budget_le_certificate
    (w : BoundedContinuousTestCertificateWindow) :
    w.continuityBudget ≤ w.certificate := by
  unfold BoundedContinuousTestCertificateWindow.certificate
  omega

def sampleBoundedContinuousTestCertificateWindow :
    BoundedContinuousTestCertificateWindow :=
  { testWindow := 5, continuityWindow := 7, testSlack := 2,
    continuityBudget := 14, slack := 2 }

example : boundedContinuousTestCertificateReady
    sampleBoundedContinuousTestCertificateWindow := by
  norm_num [boundedContinuousTestCertificateReady,
    BoundedContinuousTestCertificateWindow.continuityControlled,
    sampleBoundedContinuousTestCertificateWindow]


structure BoundedContinuousTestWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundedContinuousTestWindowSchemasBudgetCertificate.controlled
    (c : BoundedContinuousTestWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BoundedContinuousTestWindowSchemasBudgetCertificate.budgetControlled
    (c : BoundedContinuousTestWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BoundedContinuousTestWindowSchemasBudgetCertificate.Ready
    (c : BoundedContinuousTestWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BoundedContinuousTestWindowSchemasBudgetCertificate.size
    (c : BoundedContinuousTestWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem boundedContinuousTestWindowSchemas_budgetCertificate_le_size
    (c : BoundedContinuousTestWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBoundedContinuousTestWindowSchemasBudgetCertificate :
    BoundedContinuousTestWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBoundedContinuousTestWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundedContinuousTestWindowSchemasBudgetCertificate.controlled,
      sampleBoundedContinuousTestWindowSchemasBudgetCertificate]
  · norm_num [BoundedContinuousTestWindowSchemasBudgetCertificate.budgetControlled,
      sampleBoundedContinuousTestWindowSchemasBudgetCertificate]

example : sampleBoundedContinuousTestWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundedContinuousTestWindowSchemasBudgetCertificate.controlled,
      sampleBoundedContinuousTestWindowSchemasBudgetCertificate]
  · norm_num [BoundedContinuousTestWindowSchemasBudgetCertificate.budgetControlled,
      sampleBoundedContinuousTestWindowSchemasBudgetCertificate]

example :
    sampleBoundedContinuousTestWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundedContinuousTestWindowSchemasBudgetCertificate.size := by
  apply boundedContinuousTestWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [BoundedContinuousTestWindowSchemasBudgetCertificate.controlled,
      sampleBoundedContinuousTestWindowSchemasBudgetCertificate]
  · norm_num [BoundedContinuousTestWindowSchemasBudgetCertificate.budgetControlled,
      sampleBoundedContinuousTestWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleBoundedContinuousTestWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundedContinuousTestWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List BoundedContinuousTestWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBoundedContinuousTestWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBoundedContinuousTestWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.BoundedContinuousTestWindowSchemas
