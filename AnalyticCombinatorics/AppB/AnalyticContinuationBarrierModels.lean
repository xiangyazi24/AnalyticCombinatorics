import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic continuation barrier models.

This module records finite bookkeeping for continuation barriers.
-/

namespace AnalyticCombinatorics.AppB.AnalyticContinuationBarrierModels

structure ContinuationBarrierData where
  barrierCount : ℕ
  continuationDepth : ℕ
  barrierSlack : ℕ
deriving DecidableEq, Repr

def hasBarrierCount (d : ContinuationBarrierData) : Prop :=
  0 < d.barrierCount

def continuationDepthControlled (d : ContinuationBarrierData) : Prop :=
  d.continuationDepth ≤ d.barrierCount + d.barrierSlack

def continuationBarrierReady (d : ContinuationBarrierData) : Prop :=
  hasBarrierCount d ∧ continuationDepthControlled d

def continuationBarrierBudget (d : ContinuationBarrierData) : ℕ :=
  d.barrierCount + d.continuationDepth + d.barrierSlack

theorem continuationBarrierReady.hasBarrierCount
    {d : ContinuationBarrierData}
    (h : continuationBarrierReady d) :
    hasBarrierCount d ∧ continuationDepthControlled d ∧
      d.continuationDepth ≤ continuationBarrierBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold continuationBarrierBudget
  omega

theorem continuationDepth_le_budget (d : ContinuationBarrierData) :
    d.continuationDepth ≤ continuationBarrierBudget d := by
  unfold continuationBarrierBudget
  omega

def sampleContinuationBarrierData : ContinuationBarrierData :=
  { barrierCount := 6, continuationDepth := 8, barrierSlack := 3 }

example : continuationBarrierReady sampleContinuationBarrierData := by
  norm_num [continuationBarrierReady, hasBarrierCount]
  norm_num [continuationDepthControlled, sampleContinuationBarrierData]

example : continuationBarrierBudget sampleContinuationBarrierData = 17 := by
  native_decide

/-- Finite executable readiness audit for continuation-barrier data. -/
def continuationBarrierListReady (windows : List ContinuationBarrierData) : Bool :=
  windows.all fun d =>
    0 < d.barrierCount &&
      d.continuationDepth ≤ d.barrierCount + d.barrierSlack

theorem continuationBarrierList_readyWindow :
    continuationBarrierListReady
      [{ barrierCount := 4, continuationDepth := 5, barrierSlack := 1 },
       { barrierCount := 6, continuationDepth := 8, barrierSlack := 3 }] = true := by
  unfold continuationBarrierListReady
  native_decide


structure AnalyticContinuationBarrierModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticContinuationBarrierModelsBudgetCertificate.controlled
    (c : AnalyticContinuationBarrierModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticContinuationBarrierModelsBudgetCertificate.budgetControlled
    (c : AnalyticContinuationBarrierModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticContinuationBarrierModelsBudgetCertificate.Ready
    (c : AnalyticContinuationBarrierModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticContinuationBarrierModelsBudgetCertificate.size
    (c : AnalyticContinuationBarrierModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticContinuationBarrierModels_budgetCertificate_le_size
    (c : AnalyticContinuationBarrierModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticContinuationBarrierModelsBudgetCertificate :
    AnalyticContinuationBarrierModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticContinuationBarrierModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticContinuationBarrierModelsBudgetCertificate.controlled,
      sampleAnalyticContinuationBarrierModelsBudgetCertificate]
  · norm_num [AnalyticContinuationBarrierModelsBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationBarrierModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticContinuationBarrierModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticContinuationBarrierModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticContinuationBarrierModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticContinuationBarrierModelsBudgetCertificate.controlled,
      sampleAnalyticContinuationBarrierModelsBudgetCertificate]
  · norm_num [AnalyticContinuationBarrierModelsBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationBarrierModelsBudgetCertificate]

example :
    sampleAnalyticContinuationBarrierModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticContinuationBarrierModelsBudgetCertificate.size := by
  apply analyticContinuationBarrierModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticContinuationBarrierModelsBudgetCertificate.controlled,
      sampleAnalyticContinuationBarrierModelsBudgetCertificate]
  · norm_num [AnalyticContinuationBarrierModelsBudgetCertificate.budgetControlled,
      sampleAnalyticContinuationBarrierModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticContinuationBarrierModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticContinuationBarrierModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticContinuationBarrierModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.AnalyticContinuationBarrierModels
