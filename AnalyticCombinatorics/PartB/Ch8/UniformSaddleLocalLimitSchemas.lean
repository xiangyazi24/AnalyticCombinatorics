import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform saddle local limit schemas.

This module records finite bookkeeping for saddle local limit windows.
-/

namespace AnalyticCombinatorics.PartB.Ch8.UniformSaddleLocalLimitSchemas

structure SaddleLocalLimitData where
  saddleVariance : ℕ
  localWindow : ℕ
  limitSlack : ℕ
deriving DecidableEq, Repr

def hasSaddleVariance (d : SaddleLocalLimitData) : Prop :=
  0 < d.saddleVariance

def localWindowControlled (d : SaddleLocalLimitData) : Prop :=
  d.localWindow ≤ d.saddleVariance + d.limitSlack

def saddleLocalLimitReady (d : SaddleLocalLimitData) : Prop :=
  hasSaddleVariance d ∧ localWindowControlled d

def saddleLocalLimitBudget (d : SaddleLocalLimitData) : ℕ :=
  d.saddleVariance + d.localWindow + d.limitSlack

theorem saddleLocalLimitReady.hasSaddleVariance
    {d : SaddleLocalLimitData}
    (h : saddleLocalLimitReady d) :
    hasSaddleVariance d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem localWindow_le_budget (d : SaddleLocalLimitData) :
    d.localWindow ≤ saddleLocalLimitBudget d := by
  unfold saddleLocalLimitBudget
  omega

def sampleSaddleLocalLimitData : SaddleLocalLimitData :=
  { saddleVariance := 6, localWindow := 8, limitSlack := 3 }

example : saddleLocalLimitReady sampleSaddleLocalLimitData := by
  norm_num [saddleLocalLimitReady, hasSaddleVariance]
  norm_num [localWindowControlled, sampleSaddleLocalLimitData]

example : saddleLocalLimitBudget sampleSaddleLocalLimitData = 17 := by
  native_decide

structure SaddleLocalLimitBudgetCertificate where
  saddleVarianceWindow : ℕ
  localWindow : ℕ
  limitSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleLocalLimitBudgetCertificate.controlled
    (c : SaddleLocalLimitBudgetCertificate) : Prop :=
  0 < c.saddleVarianceWindow ∧
    c.localWindow ≤ c.saddleVarianceWindow + c.limitSlackWindow + c.slack

def SaddleLocalLimitBudgetCertificate.budgetControlled
    (c : SaddleLocalLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleVarianceWindow + c.localWindow + c.limitSlackWindow + c.slack

def SaddleLocalLimitBudgetCertificate.Ready
    (c : SaddleLocalLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SaddleLocalLimitBudgetCertificate.size
    (c : SaddleLocalLimitBudgetCertificate) : ℕ :=
  c.saddleVarianceWindow + c.localWindow + c.limitSlackWindow + c.slack

theorem saddleLocalLimit_budgetCertificate_le_size
    (c : SaddleLocalLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSaddleLocalLimitBudgetCertificate :
    SaddleLocalLimitBudgetCertificate :=
  { saddleVarianceWindow := 6
    localWindow := 8
    limitSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSaddleLocalLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddleLocalLimitBudgetCertificate.controlled,
      sampleSaddleLocalLimitBudgetCertificate]
  · norm_num [SaddleLocalLimitBudgetCertificate.budgetControlled,
      sampleSaddleLocalLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddleLocalLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleLocalLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSaddleLocalLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddleLocalLimitBudgetCertificate.controlled,
      sampleSaddleLocalLimitBudgetCertificate]
  · norm_num [SaddleLocalLimitBudgetCertificate.budgetControlled,
      sampleSaddleLocalLimitBudgetCertificate]

example :
    sampleSaddleLocalLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleLocalLimitBudgetCertificate.size := by
  apply saddleLocalLimit_budgetCertificate_le_size
  constructor
  · norm_num [SaddleLocalLimitBudgetCertificate.controlled,
      sampleSaddleLocalLimitBudgetCertificate]
  · norm_num [SaddleLocalLimitBudgetCertificate.budgetControlled,
      sampleSaddleLocalLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SaddleLocalLimitBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSaddleLocalLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSaddleLocalLimitBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.UniformSaddleLocalLimitSchemas
