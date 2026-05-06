import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform analytic continuation models.

The finite abstraction records path count, overlap budget, and radius
slack for uniform continuation.
-/

namespace AnalyticCombinatorics.AppB.UniformAnalyticContinuationModels

structure UniformAnalyticContinuationData where
  pathCount : ℕ
  overlapBudget : ℕ
  radiusSlack : ℕ
deriving DecidableEq, Repr

def pathCountPositive (d : UniformAnalyticContinuationData) : Prop :=
  0 < d.pathCount

def overlapsControlled (d : UniformAnalyticContinuationData) : Prop :=
  d.overlapBudget ≤ d.pathCount + d.radiusSlack

def uniformAnalyticContinuationReady
    (d : UniformAnalyticContinuationData) : Prop :=
  pathCountPositive d ∧ overlapsControlled d

def uniformAnalyticContinuationBudget
    (d : UniformAnalyticContinuationData) : ℕ :=
  d.pathCount + d.overlapBudget + d.radiusSlack

theorem uniformAnalyticContinuationReady.paths
    {d : UniformAnalyticContinuationData}
    (h : uniformAnalyticContinuationReady d) :
    pathCountPositive d ∧ overlapsControlled d ∧
      d.overlapBudget ≤ uniformAnalyticContinuationBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformAnalyticContinuationBudget
  omega

theorem overlapBudget_le_continuationBudget
    (d : UniformAnalyticContinuationData) :
    d.overlapBudget ≤ uniformAnalyticContinuationBudget d := by
  unfold uniformAnalyticContinuationBudget
  omega

def sampleUniformAnalyticContinuationData :
    UniformAnalyticContinuationData :=
  { pathCount := 5, overlapBudget := 7, radiusSlack := 3 }

example :
    uniformAnalyticContinuationReady
      sampleUniformAnalyticContinuationData := by
  norm_num [uniformAnalyticContinuationReady, pathCountPositive]
  norm_num [overlapsControlled, sampleUniformAnalyticContinuationData]

example :
    uniformAnalyticContinuationBudget
      sampleUniformAnalyticContinuationData = 15 := by
  native_decide


structure UniformAnalyticContinuationModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformAnalyticContinuationModelsBudgetCertificate.controlled
    (c : UniformAnalyticContinuationModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformAnalyticContinuationModelsBudgetCertificate.budgetControlled
    (c : UniformAnalyticContinuationModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformAnalyticContinuationModelsBudgetCertificate.Ready
    (c : UniformAnalyticContinuationModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformAnalyticContinuationModelsBudgetCertificate.size
    (c : UniformAnalyticContinuationModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformAnalyticContinuationModels_budgetCertificate_le_size
    (c : UniformAnalyticContinuationModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformAnalyticContinuationModelsBudgetCertificate :
    UniformAnalyticContinuationModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformAnalyticContinuationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformAnalyticContinuationModelsBudgetCertificate.controlled,
      sampleUniformAnalyticContinuationModelsBudgetCertificate]
  · norm_num [UniformAnalyticContinuationModelsBudgetCertificate.budgetControlled,
      sampleUniformAnalyticContinuationModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformAnalyticContinuationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformAnalyticContinuationModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformAnalyticContinuationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformAnalyticContinuationModelsBudgetCertificate.controlled,
      sampleUniformAnalyticContinuationModelsBudgetCertificate]
  · norm_num [UniformAnalyticContinuationModelsBudgetCertificate.budgetControlled,
      sampleUniformAnalyticContinuationModelsBudgetCertificate]

example :
    sampleUniformAnalyticContinuationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformAnalyticContinuationModelsBudgetCertificate.size := by
  apply uniformAnalyticContinuationModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformAnalyticContinuationModelsBudgetCertificate.controlled,
      sampleUniformAnalyticContinuationModelsBudgetCertificate]
  · norm_num [UniformAnalyticContinuationModelsBudgetCertificate.budgetControlled,
      sampleUniformAnalyticContinuationModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformAnalyticContinuationModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformAnalyticContinuationModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformAnalyticContinuationModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformAnalyticContinuationModels
