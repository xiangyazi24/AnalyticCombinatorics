import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Joint parameter limit schemas.

This module records finite bookkeeping for joint parameter limits.
-/

namespace AnalyticCombinatorics.PartA.Ch3.JointParameterLimitSchemas

structure JointParameterLimitData where
  parameterCount : ℕ
  covarianceWindow : ℕ
  limitSlack : ℕ
deriving DecidableEq, Repr

def hasParameterCount (d : JointParameterLimitData) : Prop :=
  0 < d.parameterCount

def covarianceWindowControlled (d : JointParameterLimitData) : Prop :=
  d.covarianceWindow ≤ d.parameterCount + d.limitSlack

def jointParameterLimitReady (d : JointParameterLimitData) : Prop :=
  hasParameterCount d ∧ covarianceWindowControlled d

def jointParameterLimitBudget (d : JointParameterLimitData) : ℕ :=
  d.parameterCount + d.covarianceWindow + d.limitSlack

theorem jointParameterLimitReady.hasParameterCount
    {d : JointParameterLimitData}
    (h : jointParameterLimitReady d) :
    hasParameterCount d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem covarianceWindow_le_budget (d : JointParameterLimitData) :
    d.covarianceWindow ≤ jointParameterLimitBudget d := by
  unfold jointParameterLimitBudget
  omega

def sampleJointParameterLimitData : JointParameterLimitData :=
  { parameterCount := 6, covarianceWindow := 8, limitSlack := 3 }

example : jointParameterLimitReady sampleJointParameterLimitData := by
  norm_num [jointParameterLimitReady, hasParameterCount]
  norm_num [covarianceWindowControlled, sampleJointParameterLimitData]

example : jointParameterLimitBudget sampleJointParameterLimitData = 17 := by
  native_decide

structure JointParameterLimitBudgetCertificate where
  parameterWindow : ℕ
  covarianceWindow : ℕ
  limitSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def JointParameterLimitBudgetCertificate.controlled
    (c : JointParameterLimitBudgetCertificate) : Prop :=
  0 < c.parameterWindow ∧
    c.covarianceWindow ≤ c.parameterWindow + c.limitSlackWindow + c.slack

def JointParameterLimitBudgetCertificate.budgetControlled
    (c : JointParameterLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.parameterWindow + c.covarianceWindow + c.limitSlackWindow + c.slack

def JointParameterLimitBudgetCertificate.Ready
    (c : JointParameterLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def JointParameterLimitBudgetCertificate.size
    (c : JointParameterLimitBudgetCertificate) : ℕ :=
  c.parameterWindow + c.covarianceWindow + c.limitSlackWindow + c.slack

theorem jointParameterLimit_budgetCertificate_le_size
    (c : JointParameterLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleJointParameterLimitBudgetCertificate :
    JointParameterLimitBudgetCertificate :=
  { parameterWindow := 6
    covarianceWindow := 8
    limitSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleJointParameterLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [JointParameterLimitBudgetCertificate.controlled,
      sampleJointParameterLimitBudgetCertificate]
  · norm_num [JointParameterLimitBudgetCertificate.budgetControlled,
      sampleJointParameterLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleJointParameterLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleJointParameterLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleJointParameterLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [JointParameterLimitBudgetCertificate.controlled,
      sampleJointParameterLimitBudgetCertificate]
  · norm_num [JointParameterLimitBudgetCertificate.budgetControlled,
      sampleJointParameterLimitBudgetCertificate]

example :
    sampleJointParameterLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleJointParameterLimitBudgetCertificate.size := by
  apply jointParameterLimit_budgetCertificate_le_size
  constructor
  · norm_num [JointParameterLimitBudgetCertificate.controlled,
      sampleJointParameterLimitBudgetCertificate]
  · norm_num [JointParameterLimitBudgetCertificate.budgetControlled,
      sampleJointParameterLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List JointParameterLimitBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleJointParameterLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleJointParameterLimitBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.JointParameterLimitSchemas
