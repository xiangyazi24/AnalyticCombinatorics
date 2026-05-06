import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic moment schema bookkeeping.

The module records finite moment orders, cumulant budgets, and variance
checks for analytic moment methods.
-/

namespace AnalyticCombinatorics.PartA.Ch3.AnalyticMomentSchemas

structure MomentSchemaData where
  momentOrder : ℕ
  varianceBudget : ℕ
  cumulantBudget : ℕ
deriving DecidableEq, Repr

def positiveMomentOrder (d : MomentSchemaData) : Prop :=
  0 < d.momentOrder

def positiveVariance (d : MomentSchemaData) : Prop :=
  0 < d.varianceBudget

def analyticMomentReady (d : MomentSchemaData) : Prop :=
  positiveMomentOrder d ∧ positiveVariance d

def momentSchemaBudget (d : MomentSchemaData) : ℕ :=
  d.momentOrder + d.varianceBudget + d.cumulantBudget

theorem analyticMomentReady.variance {d : MomentSchemaData}
    (h : analyticMomentReady d) :
    positiveVariance d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem momentOrder_le_budget (d : MomentSchemaData) :
    d.momentOrder ≤ momentSchemaBudget d := by
  unfold momentSchemaBudget
  omega

def sampleMomentSchema : MomentSchemaData :=
  { momentOrder := 4, varianceBudget := 6, cumulantBudget := 3 }

example : analyticMomentReady sampleMomentSchema := by
  norm_num [analyticMomentReady, positiveMomentOrder, positiveVariance, sampleMomentSchema]

example : momentSchemaBudget sampleMomentSchema = 13 := by
  native_decide

structure AnalyticMomentWindow where
  momentOrder : ℕ
  varianceBudget : ℕ
  cumulantBudget : ℕ
  transferError : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticMomentWindow.positiveReady (w : AnalyticMomentWindow) : Prop :=
  0 < w.momentOrder ∧ 0 < w.varianceBudget

def AnalyticMomentWindow.cumulantControlled (w : AnalyticMomentWindow) : Prop :=
  w.cumulantBudget ≤ w.momentOrder + w.varianceBudget + w.slack

def AnalyticMomentWindow.errorControlled (w : AnalyticMomentWindow) : Prop :=
  w.transferError ≤ w.cumulantBudget + w.varianceBudget + w.slack

def AnalyticMomentWindow.ready (w : AnalyticMomentWindow) : Prop :=
  w.positiveReady ∧ w.cumulantControlled ∧ w.errorControlled

def AnalyticMomentWindow.certificate (w : AnalyticMomentWindow) : ℕ :=
  w.momentOrder + w.varianceBudget + w.cumulantBudget + w.transferError + w.slack

theorem transferError_le_certificate (w : AnalyticMomentWindow) :
    w.transferError ≤ w.certificate := by
  unfold AnalyticMomentWindow.certificate
  omega

def sampleAnalyticMomentWindow : AnalyticMomentWindow :=
  { momentOrder := 4, varianceBudget := 6, cumulantBudget := 3, transferError := 5, slack := 0 }

example : sampleAnalyticMomentWindow.ready := by
  norm_num [sampleAnalyticMomentWindow, AnalyticMomentWindow.ready,
    AnalyticMomentWindow.positiveReady, AnalyticMomentWindow.cumulantControlled,
    AnalyticMomentWindow.errorControlled]


structure AnalyticMomentSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticMomentSchemasBudgetCertificate.controlled
    (c : AnalyticMomentSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticMomentSchemasBudgetCertificate.budgetControlled
    (c : AnalyticMomentSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticMomentSchemasBudgetCertificate.Ready
    (c : AnalyticMomentSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticMomentSchemasBudgetCertificate.size
    (c : AnalyticMomentSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticMomentSchemas_budgetCertificate_le_size
    (c : AnalyticMomentSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticMomentSchemasBudgetCertificate :
    AnalyticMomentSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticMomentSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticMomentSchemasBudgetCertificate.controlled,
      sampleAnalyticMomentSchemasBudgetCertificate]
  · norm_num [AnalyticMomentSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticMomentSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticMomentSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticMomentSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticMomentSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticMomentSchemasBudgetCertificate.controlled,
      sampleAnalyticMomentSchemasBudgetCertificate]
  · norm_num [AnalyticMomentSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticMomentSchemasBudgetCertificate]

example :
    sampleAnalyticMomentSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticMomentSchemasBudgetCertificate.size := by
  apply analyticMomentSchemas_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticMomentSchemasBudgetCertificate.controlled,
      sampleAnalyticMomentSchemasBudgetCertificate]
  · norm_num [AnalyticMomentSchemasBudgetCertificate.budgetControlled,
      sampleAnalyticMomentSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticMomentSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticMomentSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticMomentSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.AnalyticMomentSchemas
