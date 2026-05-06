import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random measure limit schemas.

The finite schema records support cells, mass budget, and tightness slack.
-/

namespace AnalyticCombinatorics.AppC.RandomMeasureLimitSchemas

structure RandomMeasureLimitData where
  supportCells : ℕ
  massBudget : ℕ
  tightnessSlack : ℕ
deriving DecidableEq, Repr

def supportCellsPositive (d : RandomMeasureLimitData) : Prop :=
  0 < d.supportCells

def massBudgetControlled (d : RandomMeasureLimitData) : Prop :=
  d.massBudget ≤ d.supportCells + d.tightnessSlack

def randomMeasureLimitReady (d : RandomMeasureLimitData) : Prop :=
  supportCellsPositive d ∧ massBudgetControlled d

def randomMeasureLimitBudget (d : RandomMeasureLimitData) : ℕ :=
  d.supportCells + d.massBudget + d.tightnessSlack

theorem randomMeasureLimitReady.support {d : RandomMeasureLimitData}
    (h : randomMeasureLimitReady d) :
    supportCellsPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem massBudget_le_randomMeasureBudget (d : RandomMeasureLimitData) :
    d.massBudget ≤ randomMeasureLimitBudget d := by
  unfold randomMeasureLimitBudget
  omega

def sampleRandomMeasureLimitData : RandomMeasureLimitData :=
  { supportCells := 6, massBudget := 8, tightnessSlack := 3 }

example : randomMeasureLimitReady sampleRandomMeasureLimitData := by
  norm_num [randomMeasureLimitReady, supportCellsPositive]
  norm_num [massBudgetControlled, sampleRandomMeasureLimitData]

example : randomMeasureLimitBudget sampleRandomMeasureLimitData = 17 := by
  native_decide

structure RandomMeasureWindow where
  supportCells : ℕ
  massBudget : ℕ
  tightnessSlack : ℕ
  atomCount : ℕ
deriving DecidableEq, Repr

def RandomMeasureWindow.supportReady (w : RandomMeasureWindow) : Prop :=
  0 < w.supportCells

def RandomMeasureWindow.massControlled (w : RandomMeasureWindow) : Prop :=
  w.massBudget ≤ w.supportCells + w.tightnessSlack

def RandomMeasureWindow.atomControlled (w : RandomMeasureWindow) : Prop :=
  w.atomCount ≤ w.supportCells + w.tightnessSlack

def RandomMeasureWindow.ready (w : RandomMeasureWindow) : Prop :=
  w.supportReady ∧ w.massControlled ∧ w.atomControlled

def RandomMeasureWindow.certificate (w : RandomMeasureWindow) : ℕ :=
  w.supportCells + w.massBudget + w.tightnessSlack + w.atomCount

theorem atomCount_le_certificate (w : RandomMeasureWindow) :
    w.atomCount ≤ w.certificate := by
  unfold RandomMeasureWindow.certificate
  omega

def sampleRandomMeasureWindow : RandomMeasureWindow :=
  { supportCells := 6, massBudget := 8, tightnessSlack := 3, atomCount := 5 }

example : sampleRandomMeasureWindow.ready := by
  norm_num [sampleRandomMeasureWindow, RandomMeasureWindow.ready,
    RandomMeasureWindow.supportReady, RandomMeasureWindow.massControlled,
    RandomMeasureWindow.atomControlled]


structure RandomMeasureLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomMeasureLimitSchemasBudgetCertificate.controlled
    (c : RandomMeasureLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomMeasureLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomMeasureLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomMeasureLimitSchemasBudgetCertificate.Ready
    (c : RandomMeasureLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomMeasureLimitSchemasBudgetCertificate.size
    (c : RandomMeasureLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomMeasureLimitSchemas_budgetCertificate_le_size
    (c : RandomMeasureLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomMeasureLimitSchemasBudgetCertificate :
    RandomMeasureLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomMeasureLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomMeasureLimitSchemasBudgetCertificate.controlled,
      sampleRandomMeasureLimitSchemasBudgetCertificate]
  · norm_num [RandomMeasureLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomMeasureLimitSchemasBudgetCertificate]

example : sampleRandomMeasureLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomMeasureLimitSchemasBudgetCertificate.controlled,
      sampleRandomMeasureLimitSchemasBudgetCertificate]
  · norm_num [RandomMeasureLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomMeasureLimitSchemasBudgetCertificate]

example :
    sampleRandomMeasureLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomMeasureLimitSchemasBudgetCertificate.size := by
  apply randomMeasureLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomMeasureLimitSchemasBudgetCertificate.controlled,
      sampleRandomMeasureLimitSchemasBudgetCertificate]
  · norm_num [RandomMeasureLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomMeasureLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleRandomMeasureLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomMeasureLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RandomMeasureLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomMeasureLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRandomMeasureLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.RandomMeasureLimitSchemas
