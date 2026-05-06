import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Marked parameter limit schemas.

This module records finite bookkeeping for marked parameter limits.
-/

namespace AnalyticCombinatorics.PartA.Ch3.MarkedParameterLimitSchemas

structure MarkedParameterLimitData where
  parameterMarks : ℕ
  limitWindow : ℕ
  analyticSlack : ℕ
deriving DecidableEq, Repr

def hasParameterMarks (d : MarkedParameterLimitData) : Prop :=
  0 < d.parameterMarks

def limitWindowControlled (d : MarkedParameterLimitData) : Prop :=
  d.limitWindow ≤ d.parameterMarks + d.analyticSlack

def markedParameterLimitReady (d : MarkedParameterLimitData) : Prop :=
  hasParameterMarks d ∧ limitWindowControlled d

def markedParameterLimitBudget (d : MarkedParameterLimitData) : ℕ :=
  d.parameterMarks + d.limitWindow + d.analyticSlack

theorem markedParameterLimitReady.hasParameterMarks
    {d : MarkedParameterLimitData}
    (h : markedParameterLimitReady d) :
    hasParameterMarks d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem limitWindow_le_budget (d : MarkedParameterLimitData) :
    d.limitWindow ≤ markedParameterLimitBudget d := by
  unfold markedParameterLimitBudget
  omega

def sampleMarkedParameterLimitData : MarkedParameterLimitData :=
  { parameterMarks := 6, limitWindow := 8, analyticSlack := 3 }

example : markedParameterLimitReady sampleMarkedParameterLimitData := by
  norm_num [markedParameterLimitReady, hasParameterMarks]
  norm_num [limitWindowControlled, sampleMarkedParameterLimitData]

example : markedParameterLimitBudget sampleMarkedParameterLimitData = 17 := by
  native_decide

structure MarkedParameterLimitBudgetCertificate where
  markWindow : ℕ
  limitWindow : ℕ
  analyticSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MarkedParameterLimitBudgetCertificate.controlled
    (c : MarkedParameterLimitBudgetCertificate) : Prop :=
  0 < c.markWindow ∧
    c.limitWindow ≤ c.markWindow + c.analyticSlackWindow + c.slack

def MarkedParameterLimitBudgetCertificate.budgetControlled
    (c : MarkedParameterLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.markWindow + c.limitWindow + c.analyticSlackWindow + c.slack

def MarkedParameterLimitBudgetCertificate.Ready
    (c : MarkedParameterLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MarkedParameterLimitBudgetCertificate.size
    (c : MarkedParameterLimitBudgetCertificate) : ℕ :=
  c.markWindow + c.limitWindow + c.analyticSlackWindow + c.slack

theorem markedParameterLimit_budgetCertificate_le_size
    (c : MarkedParameterLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMarkedParameterLimitBudgetCertificate :
    MarkedParameterLimitBudgetCertificate :=
  { markWindow := 6
    limitWindow := 8
    analyticSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMarkedParameterLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [MarkedParameterLimitBudgetCertificate.controlled,
      sampleMarkedParameterLimitBudgetCertificate]
  · norm_num [MarkedParameterLimitBudgetCertificate.budgetControlled,
      sampleMarkedParameterLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMarkedParameterLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleMarkedParameterLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMarkedParameterLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [MarkedParameterLimitBudgetCertificate.controlled,
      sampleMarkedParameterLimitBudgetCertificate]
  · norm_num [MarkedParameterLimitBudgetCertificate.budgetControlled,
      sampleMarkedParameterLimitBudgetCertificate]

example :
    sampleMarkedParameterLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleMarkedParameterLimitBudgetCertificate.size := by
  apply markedParameterLimit_budgetCertificate_le_size
  constructor
  · norm_num [MarkedParameterLimitBudgetCertificate.controlled,
      sampleMarkedParameterLimitBudgetCertificate]
  · norm_num [MarkedParameterLimitBudgetCertificate.budgetControlled,
      sampleMarkedParameterLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MarkedParameterLimitBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleMarkedParameterLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleMarkedParameterLimitBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.MarkedParameterLimitSchemas
