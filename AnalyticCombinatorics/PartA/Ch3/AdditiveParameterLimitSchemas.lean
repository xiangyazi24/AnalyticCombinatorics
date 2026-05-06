import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Additive parameter limit schemas.

This module records finite bookkeeping for additive parameter limits.
-/

namespace AnalyticCombinatorics.PartA.Ch3.AdditiveParameterLimitSchemas

structure AdditiveParameterLimitData where
  parameterCount : ℕ
  varianceWindow : ℕ
  limitSlack : ℕ
deriving DecidableEq, Repr

def hasParameterCount (d : AdditiveParameterLimitData) : Prop :=
  0 < d.parameterCount

def varianceWindowControlled (d : AdditiveParameterLimitData) : Prop :=
  d.varianceWindow ≤ d.parameterCount + d.limitSlack

def additiveParameterLimitReady (d : AdditiveParameterLimitData) : Prop :=
  hasParameterCount d ∧ varianceWindowControlled d

def additiveParameterLimitBudget (d : AdditiveParameterLimitData) : ℕ :=
  d.parameterCount + d.varianceWindow + d.limitSlack

theorem additiveParameterLimitReady.hasParameterCount
    {d : AdditiveParameterLimitData}
    (h : additiveParameterLimitReady d) :
    hasParameterCount d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem varianceWindow_le_budget (d : AdditiveParameterLimitData) :
    d.varianceWindow ≤ additiveParameterLimitBudget d := by
  unfold additiveParameterLimitBudget
  omega

def sampleAdditiveParameterLimitData : AdditiveParameterLimitData :=
  { parameterCount := 6, varianceWindow := 8, limitSlack := 3 }

example : additiveParameterLimitReady sampleAdditiveParameterLimitData := by
  norm_num [additiveParameterLimitReady, hasParameterCount]
  norm_num [varianceWindowControlled, sampleAdditiveParameterLimitData]

example : additiveParameterLimitBudget sampleAdditiveParameterLimitData = 17 := by
  native_decide

structure AdditiveParameterLimitBudgetCertificate where
  parameterWindow : ℕ
  varianceWindow : ℕ
  limitSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AdditiveParameterLimitBudgetCertificate.controlled
    (c : AdditiveParameterLimitBudgetCertificate) : Prop :=
  0 < c.parameterWindow ∧
    c.varianceWindow ≤ c.parameterWindow + c.limitSlackWindow + c.slack

def AdditiveParameterLimitBudgetCertificate.budgetControlled
    (c : AdditiveParameterLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.parameterWindow + c.varianceWindow + c.limitSlackWindow + c.slack

def AdditiveParameterLimitBudgetCertificate.Ready
    (c : AdditiveParameterLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AdditiveParameterLimitBudgetCertificate.size
    (c : AdditiveParameterLimitBudgetCertificate) : ℕ :=
  c.parameterWindow + c.varianceWindow + c.limitSlackWindow + c.slack

theorem additiveParameterLimit_budgetCertificate_le_size
    (c : AdditiveParameterLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAdditiveParameterLimitBudgetCertificate :
    AdditiveParameterLimitBudgetCertificate :=
  { parameterWindow := 6
    varianceWindow := 8
    limitSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAdditiveParameterLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [AdditiveParameterLimitBudgetCertificate.controlled,
      sampleAdditiveParameterLimitBudgetCertificate]
  · norm_num [AdditiveParameterLimitBudgetCertificate.budgetControlled,
      sampleAdditiveParameterLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAdditiveParameterLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleAdditiveParameterLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAdditiveParameterLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [AdditiveParameterLimitBudgetCertificate.controlled,
      sampleAdditiveParameterLimitBudgetCertificate]
  · norm_num [AdditiveParameterLimitBudgetCertificate.budgetControlled,
      sampleAdditiveParameterLimitBudgetCertificate]

example :
    sampleAdditiveParameterLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleAdditiveParameterLimitBudgetCertificate.size := by
  apply additiveParameterLimit_budgetCertificate_le_size
  constructor
  · norm_num [AdditiveParameterLimitBudgetCertificate.controlled,
      sampleAdditiveParameterLimitBudgetCertificate]
  · norm_num [AdditiveParameterLimitBudgetCertificate.budgetControlled,
      sampleAdditiveParameterLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AdditiveParameterLimitBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAdditiveParameterLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAdditiveParameterLimitBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.AdditiveParameterLimitSchemas
