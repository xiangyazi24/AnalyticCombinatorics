import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic disk estimate models.

This module records a finite disk-estimate bookkeeping schema: a positive
disk radius supports an estimate order bounded by a boundary slack.
-/

namespace AnalyticCombinatorics.AppB.AnalyticDiskEstimateModels

structure DiskEstimateData where
  diskRadius : ℕ
  estimateOrder : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def hasDiskRadius (d : DiskEstimateData) : Prop :=
  0 < d.diskRadius

def estimateControlled (d : DiskEstimateData) : Prop :=
  d.estimateOrder ≤ d.diskRadius + d.boundarySlack

def diskEstimateReady (d : DiskEstimateData) : Prop :=
  hasDiskRadius d ∧ estimateControlled d

def diskEstimateBudget (d : DiskEstimateData) : ℕ :=
  d.diskRadius + d.estimateOrder + d.boundarySlack

theorem diskEstimateReady.hasDiskRadius {d : DiskEstimateData}
    (h : diskEstimateReady d) :
    hasDiskRadius d ∧ estimateControlled d ∧
      d.estimateOrder ≤ diskEstimateBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold diskEstimateBudget
  omega

theorem estimateOrder_le_budget (d : DiskEstimateData) :
    d.estimateOrder ≤ diskEstimateBudget d := by
  unfold diskEstimateBudget
  omega

def sampleDiskEstimateData : DiskEstimateData :=
  { diskRadius := 6, estimateOrder := 8, boundarySlack := 3 }

example : diskEstimateReady sampleDiskEstimateData := by
  norm_num [diskEstimateReady, hasDiskRadius]
  norm_num [estimateControlled, sampleDiskEstimateData]

example : diskEstimateBudget sampleDiskEstimateData = 17 := by
  native_decide

/-- Finite executable readiness audit for disk-estimate data. -/
def diskEstimateListReady (windows : List DiskEstimateData) : Bool :=
  windows.all fun d =>
    0 < d.diskRadius && d.estimateOrder ≤ d.diskRadius + d.boundarySlack

theorem diskEstimateList_readyWindow :
    diskEstimateListReady
      [{ diskRadius := 4, estimateOrder := 5, boundarySlack := 1 },
       { diskRadius := 6, estimateOrder := 8, boundarySlack := 3 }] = true := by
  unfold diskEstimateListReady
  native_decide


structure AnalyticDiskEstimateModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticDiskEstimateModelsBudgetCertificate.controlled
    (c : AnalyticDiskEstimateModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticDiskEstimateModelsBudgetCertificate.budgetControlled
    (c : AnalyticDiskEstimateModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticDiskEstimateModelsBudgetCertificate.Ready
    (c : AnalyticDiskEstimateModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticDiskEstimateModelsBudgetCertificate.size
    (c : AnalyticDiskEstimateModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticDiskEstimateModels_budgetCertificate_le_size
    (c : AnalyticDiskEstimateModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticDiskEstimateModelsBudgetCertificate :
    AnalyticDiskEstimateModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticDiskEstimateModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticDiskEstimateModelsBudgetCertificate.controlled,
      sampleAnalyticDiskEstimateModelsBudgetCertificate]
  · norm_num [AnalyticDiskEstimateModelsBudgetCertificate.budgetControlled,
      sampleAnalyticDiskEstimateModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticDiskEstimateModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticDiskEstimateModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticDiskEstimateModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticDiskEstimateModelsBudgetCertificate.controlled,
      sampleAnalyticDiskEstimateModelsBudgetCertificate]
  · norm_num [AnalyticDiskEstimateModelsBudgetCertificate.budgetControlled,
      sampleAnalyticDiskEstimateModelsBudgetCertificate]

example :
    sampleAnalyticDiskEstimateModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticDiskEstimateModelsBudgetCertificate.size := by
  apply analyticDiskEstimateModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticDiskEstimateModelsBudgetCertificate.controlled,
      sampleAnalyticDiskEstimateModelsBudgetCertificate]
  · norm_num [AnalyticDiskEstimateModelsBudgetCertificate.budgetControlled,
      sampleAnalyticDiskEstimateModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticDiskEstimateModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticDiskEstimateModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticDiskEstimateModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.AnalyticDiskEstimateModels
