import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Levy metric remainder schemas.

This module records finite bookkeeping for Levy metric remainders.
-/

namespace AnalyticCombinatorics.AppC.LevyMetricRemainderSchemas

structure LevyMetricRemainderData where
  metricScale : ℕ
  remainderWindow : ℕ
  levySlack : ℕ
deriving DecidableEq, Repr

def hasMetricScale (d : LevyMetricRemainderData) : Prop :=
  0 < d.metricScale

def remainderWindowControlled (d : LevyMetricRemainderData) : Prop :=
  d.remainderWindow ≤ d.metricScale + d.levySlack

def levyMetricRemainderReady (d : LevyMetricRemainderData) : Prop :=
  hasMetricScale d ∧ remainderWindowControlled d

def levyMetricRemainderBudget (d : LevyMetricRemainderData) : ℕ :=
  d.metricScale + d.remainderWindow + d.levySlack

theorem levyMetricRemainderReady.hasMetricScale
    {d : LevyMetricRemainderData}
    (h : levyMetricRemainderReady d) :
    hasMetricScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget (d : LevyMetricRemainderData) :
    d.remainderWindow ≤ levyMetricRemainderBudget d := by
  unfold levyMetricRemainderBudget
  omega

def sampleLevyMetricRemainderData : LevyMetricRemainderData :=
  { metricScale := 6, remainderWindow := 8, levySlack := 3 }

example : levyMetricRemainderReady sampleLevyMetricRemainderData := by
  norm_num [levyMetricRemainderReady, hasMetricScale]
  norm_num [remainderWindowControlled, sampleLevyMetricRemainderData]

example : levyMetricRemainderBudget sampleLevyMetricRemainderData = 17 := by
  native_decide

structure LevyMetricRemainderWindow where
  metricWindow : ℕ
  remainderWindow : ℕ
  levySlack : ℕ
  metricBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LevyMetricRemainderWindow.remainderControlled
    (w : LevyMetricRemainderWindow) : Prop :=
  w.remainderWindow ≤ w.metricWindow + w.levySlack + w.slack

def levyMetricRemainderWindowReady (w : LevyMetricRemainderWindow) : Prop :=
  0 < w.metricWindow ∧ w.remainderControlled ∧
    w.metricBudget ≤ w.metricWindow + w.remainderWindow + w.slack

def LevyMetricRemainderWindow.certificate (w : LevyMetricRemainderWindow) : ℕ :=
  w.metricWindow + w.remainderWindow + w.levySlack + w.metricBudget + w.slack

theorem levyMetricRemainder_metricBudget_le_certificate
    (w : LevyMetricRemainderWindow) :
    w.metricBudget ≤ w.certificate := by
  unfold LevyMetricRemainderWindow.certificate
  omega

def sampleLevyMetricRemainderWindow : LevyMetricRemainderWindow :=
  { metricWindow := 5, remainderWindow := 7, levySlack := 2, metricBudget := 14, slack := 2 }

example : levyMetricRemainderWindowReady sampleLevyMetricRemainderWindow := by
  norm_num [levyMetricRemainderWindowReady,
    LevyMetricRemainderWindow.remainderControlled, sampleLevyMetricRemainderWindow]


structure LevyMetricRemainderSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LevyMetricRemainderSchemasBudgetCertificate.controlled
    (c : LevyMetricRemainderSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LevyMetricRemainderSchemasBudgetCertificate.budgetControlled
    (c : LevyMetricRemainderSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LevyMetricRemainderSchemasBudgetCertificate.Ready
    (c : LevyMetricRemainderSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LevyMetricRemainderSchemasBudgetCertificate.size
    (c : LevyMetricRemainderSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem levyMetricRemainderSchemas_budgetCertificate_le_size
    (c : LevyMetricRemainderSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLevyMetricRemainderSchemasBudgetCertificate :
    LevyMetricRemainderSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLevyMetricRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LevyMetricRemainderSchemasBudgetCertificate.controlled,
      sampleLevyMetricRemainderSchemasBudgetCertificate]
  · norm_num [LevyMetricRemainderSchemasBudgetCertificate.budgetControlled,
      sampleLevyMetricRemainderSchemasBudgetCertificate]

example : sampleLevyMetricRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LevyMetricRemainderSchemasBudgetCertificate.controlled,
      sampleLevyMetricRemainderSchemasBudgetCertificate]
  · norm_num [LevyMetricRemainderSchemasBudgetCertificate.budgetControlled,
      sampleLevyMetricRemainderSchemasBudgetCertificate]

example :
    sampleLevyMetricRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLevyMetricRemainderSchemasBudgetCertificate.size := by
  apply levyMetricRemainderSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LevyMetricRemainderSchemasBudgetCertificate.controlled,
      sampleLevyMetricRemainderSchemasBudgetCertificate]
  · norm_num [LevyMetricRemainderSchemasBudgetCertificate.budgetControlled,
      sampleLevyMetricRemainderSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleLevyMetricRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLevyMetricRemainderSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LevyMetricRemainderSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLevyMetricRemainderSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLevyMetricRemainderSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.LevyMetricRemainderSchemas
