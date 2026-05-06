import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cumulant comparison schemas.

The finite schema records cumulant order, comparison budget, and
uniformity slack.
-/

namespace AnalyticCombinatorics.AppC.CumulantComparisonSchemas

structure CumulantComparisonData where
  cumulantOrder : ℕ
  comparisonBudget : ℕ
  uniformitySlack : ℕ
deriving DecidableEq, Repr

def cumulantOrderPositive (d : CumulantComparisonData) : Prop :=
  0 < d.cumulantOrder

def comparisonControlled (d : CumulantComparisonData) : Prop :=
  d.comparisonBudget ≤ d.cumulantOrder + d.uniformitySlack

def cumulantComparisonReady (d : CumulantComparisonData) : Prop :=
  cumulantOrderPositive d ∧ comparisonControlled d

def cumulantComparisonBudget (d : CumulantComparisonData) : ℕ :=
  d.cumulantOrder + d.comparisonBudget + d.uniformitySlack

theorem cumulantComparisonReady.order {d : CumulantComparisonData}
    (h : cumulantComparisonReady d) :
    cumulantOrderPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem comparisonBudget_le_cumulantBudget
    (d : CumulantComparisonData) :
    d.comparisonBudget ≤ cumulantComparisonBudget d := by
  unfold cumulantComparisonBudget
  omega

def sampleCumulantComparisonData : CumulantComparisonData :=
  { cumulantOrder := 5, comparisonBudget := 7, uniformitySlack := 3 }

example : cumulantComparisonReady sampleCumulantComparisonData := by
  norm_num [cumulantComparisonReady, cumulantOrderPositive]
  norm_num [comparisonControlled, sampleCumulantComparisonData]

example : cumulantComparisonBudget sampleCumulantComparisonData = 15 := by
  native_decide

structure CumulantComparisonWindow where
  orderWindow : ℕ
  comparisonWindow : ℕ
  uniformitySlack : ℕ
  comparisonBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CumulantComparisonWindow.comparisonControlled
    (w : CumulantComparisonWindow) : Prop :=
  w.comparisonWindow ≤ w.orderWindow + w.uniformitySlack + w.slack

def cumulantComparisonWindowReady (w : CumulantComparisonWindow) : Prop :=
  0 < w.orderWindow ∧ w.comparisonControlled ∧
    w.comparisonBudget ≤ w.orderWindow + w.comparisonWindow + w.slack

def CumulantComparisonWindow.certificate (w : CumulantComparisonWindow) : ℕ :=
  w.orderWindow + w.comparisonWindow + w.uniformitySlack + w.comparisonBudget + w.slack

theorem cumulantComparison_comparisonBudget_le_certificate
    (w : CumulantComparisonWindow) :
    w.comparisonBudget ≤ w.certificate := by
  unfold CumulantComparisonWindow.certificate
  omega

def sampleCumulantComparisonWindow : CumulantComparisonWindow :=
  { orderWindow := 5, comparisonWindow := 7, uniformitySlack := 2,
    comparisonBudget := 14, slack := 2 }

example : cumulantComparisonWindowReady sampleCumulantComparisonWindow := by
  norm_num [cumulantComparisonWindowReady,
    CumulantComparisonWindow.comparisonControlled, sampleCumulantComparisonWindow]


structure CumulantComparisonSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CumulantComparisonSchemasBudgetCertificate.controlled
    (c : CumulantComparisonSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CumulantComparisonSchemasBudgetCertificate.budgetControlled
    (c : CumulantComparisonSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CumulantComparisonSchemasBudgetCertificate.Ready
    (c : CumulantComparisonSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CumulantComparisonSchemasBudgetCertificate.size
    (c : CumulantComparisonSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cumulantComparisonSchemas_budgetCertificate_le_size
    (c : CumulantComparisonSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCumulantComparisonSchemasBudgetCertificate :
    CumulantComparisonSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCumulantComparisonSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CumulantComparisonSchemasBudgetCertificate.controlled,
      sampleCumulantComparisonSchemasBudgetCertificate]
  · norm_num [CumulantComparisonSchemasBudgetCertificate.budgetControlled,
      sampleCumulantComparisonSchemasBudgetCertificate]

example : sampleCumulantComparisonSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CumulantComparisonSchemasBudgetCertificate.controlled,
      sampleCumulantComparisonSchemasBudgetCertificate]
  · norm_num [CumulantComparisonSchemasBudgetCertificate.budgetControlled,
      sampleCumulantComparisonSchemasBudgetCertificate]

example :
    sampleCumulantComparisonSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCumulantComparisonSchemasBudgetCertificate.size := by
  apply cumulantComparisonSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CumulantComparisonSchemasBudgetCertificate.controlled,
      sampleCumulantComparisonSchemasBudgetCertificate]
  · norm_num [CumulantComparisonSchemasBudgetCertificate.budgetControlled,
      sampleCumulantComparisonSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleCumulantComparisonSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCumulantComparisonSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CumulantComparisonSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCumulantComparisonSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCumulantComparisonSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.CumulantComparisonSchemas
