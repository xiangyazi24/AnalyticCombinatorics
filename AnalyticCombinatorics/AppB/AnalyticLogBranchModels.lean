import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic log branch models.

This module records finite bookkeeping for logarithm branch selections.
-/

namespace AnalyticCombinatorics.AppB.AnalyticLogBranchModels

structure LogBranchData where
  branchDomains : ℕ
  cutCount : ℕ
  branchSlack : ℕ
deriving DecidableEq, Repr

def hasBranchDomains (d : LogBranchData) : Prop :=
  0 < d.branchDomains

def cutCountControlled (d : LogBranchData) : Prop :=
  d.cutCount ≤ d.branchDomains + d.branchSlack

def logBranchReady (d : LogBranchData) : Prop :=
  hasBranchDomains d ∧ cutCountControlled d

def logBranchBudget (d : LogBranchData) : ℕ :=
  d.branchDomains + d.cutCount + d.branchSlack

theorem logBranchReady.hasBranchDomains {d : LogBranchData}
    (h : logBranchReady d) :
    hasBranchDomains d ∧ cutCountControlled d ∧
      d.cutCount ≤ logBranchBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold logBranchBudget
  omega

theorem cutCount_le_budget (d : LogBranchData) :
    d.cutCount ≤ logBranchBudget d := by
  unfold logBranchBudget
  omega

def sampleLogBranchData : LogBranchData :=
  { branchDomains := 5, cutCount := 7, branchSlack := 3 }

example : logBranchReady sampleLogBranchData := by
  norm_num [logBranchReady, hasBranchDomains]
  norm_num [cutCountControlled, sampleLogBranchData]

example : logBranchBudget sampleLogBranchData = 15 := by
  native_decide

structure LogBranchWindow where
  domainWindow : ℕ
  cutWindow : ℕ
  branchSlack : ℕ
  branchBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogBranchWindow.cutsControlled (w : LogBranchWindow) : Prop :=
  w.cutWindow ≤ w.domainWindow + w.branchSlack + w.slack

def logBranchWindowReady (w : LogBranchWindow) : Prop :=
  0 < w.domainWindow ∧ w.cutsControlled ∧
    w.branchBudget ≤ w.domainWindow + w.cutWindow + w.slack

def LogBranchWindow.certificate (w : LogBranchWindow) : ℕ :=
  w.domainWindow + w.cutWindow + w.branchSlack + w.branchBudget + w.slack

theorem logBranch_branchBudget_le_certificate (w : LogBranchWindow) :
    w.branchBudget ≤ w.certificate := by
  unfold LogBranchWindow.certificate
  omega

def sampleLogBranchWindow : LogBranchWindow :=
  { domainWindow := 4, cutWindow := 6, branchSlack := 2, branchBudget := 11, slack := 2 }

example : logBranchWindowReady sampleLogBranchWindow := by
  norm_num [logBranchWindowReady, LogBranchWindow.cutsControlled, sampleLogBranchWindow]


structure AnalyticLogBranchModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticLogBranchModelsBudgetCertificate.controlled
    (c : AnalyticLogBranchModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticLogBranchModelsBudgetCertificate.budgetControlled
    (c : AnalyticLogBranchModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticLogBranchModelsBudgetCertificate.Ready
    (c : AnalyticLogBranchModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticLogBranchModelsBudgetCertificate.size
    (c : AnalyticLogBranchModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticLogBranchModels_budgetCertificate_le_size
    (c : AnalyticLogBranchModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticLogBranchModelsBudgetCertificate :
    AnalyticLogBranchModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticLogBranchModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticLogBranchModelsBudgetCertificate.controlled,
      sampleAnalyticLogBranchModelsBudgetCertificate]
  · norm_num [AnalyticLogBranchModelsBudgetCertificate.budgetControlled,
      sampleAnalyticLogBranchModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticLogBranchModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticLogBranchModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticLogBranchModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticLogBranchModelsBudgetCertificate.controlled,
      sampleAnalyticLogBranchModelsBudgetCertificate]
  · norm_num [AnalyticLogBranchModelsBudgetCertificate.budgetControlled,
      sampleAnalyticLogBranchModelsBudgetCertificate]

example :
    sampleAnalyticLogBranchModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticLogBranchModelsBudgetCertificate.size := by
  apply analyticLogBranchModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticLogBranchModelsBudgetCertificate.controlled,
      sampleAnalyticLogBranchModelsBudgetCertificate]
  · norm_num [AnalyticLogBranchModelsBudgetCertificate.budgetControlled,
      sampleAnalyticLogBranchModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticLogBranchModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticLogBranchModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticLogBranchModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticLogBranchModels
