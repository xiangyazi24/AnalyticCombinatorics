import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Cauchy estimate models.

The finite schema records radius margin, derivative order, and uniform
bound slack.
-/

namespace AnalyticCombinatorics.AppB.UniformCauchyEstimateModels

structure UniformCauchyEstimateData where
  radiusMargin : ℕ
  derivativeOrder : ℕ
  boundSlack : ℕ
deriving DecidableEq, Repr

def radiusMarginPositive (d : UniformCauchyEstimateData) : Prop :=
  0 < d.radiusMargin

def derivativeOrderControlled (d : UniformCauchyEstimateData) : Prop :=
  d.derivativeOrder ≤ d.radiusMargin + d.boundSlack

def uniformCauchyEstimateReady (d : UniformCauchyEstimateData) : Prop :=
  radiusMarginPositive d ∧ derivativeOrderControlled d

def uniformCauchyEstimateBudget (d : UniformCauchyEstimateData) : ℕ :=
  d.radiusMargin + d.derivativeOrder + d.boundSlack

theorem uniformCauchyEstimateReady.radius
    {d : UniformCauchyEstimateData}
    (h : uniformCauchyEstimateReady d) :
    radiusMarginPositive d ∧ derivativeOrderControlled d ∧
      d.derivativeOrder ≤ uniformCauchyEstimateBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold uniformCauchyEstimateBudget
  omega

theorem derivativeOrder_le_cauchyEstimateBudget
    (d : UniformCauchyEstimateData) :
    d.derivativeOrder ≤ uniformCauchyEstimateBudget d := by
  unfold uniformCauchyEstimateBudget
  omega

def sampleUniformCauchyEstimateData : UniformCauchyEstimateData :=
  { radiusMargin := 6, derivativeOrder := 8, boundSlack := 3 }

example : uniformCauchyEstimateReady sampleUniformCauchyEstimateData := by
  norm_num [uniformCauchyEstimateReady, radiusMarginPositive]
  norm_num [derivativeOrderControlled, sampleUniformCauchyEstimateData]

example : uniformCauchyEstimateBudget sampleUniformCauchyEstimateData = 17 := by
  native_decide


structure UniformCauchyEstimateModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformCauchyEstimateModelsBudgetCertificate.controlled
    (c : UniformCauchyEstimateModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformCauchyEstimateModelsBudgetCertificate.budgetControlled
    (c : UniformCauchyEstimateModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformCauchyEstimateModelsBudgetCertificate.Ready
    (c : UniformCauchyEstimateModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformCauchyEstimateModelsBudgetCertificate.size
    (c : UniformCauchyEstimateModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformCauchyEstimateModels_budgetCertificate_le_size
    (c : UniformCauchyEstimateModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformCauchyEstimateModelsBudgetCertificate :
    UniformCauchyEstimateModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformCauchyEstimateModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformCauchyEstimateModelsBudgetCertificate.controlled,
      sampleUniformCauchyEstimateModelsBudgetCertificate]
  · norm_num [UniformCauchyEstimateModelsBudgetCertificate.budgetControlled,
      sampleUniformCauchyEstimateModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformCauchyEstimateModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformCauchyEstimateModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformCauchyEstimateModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformCauchyEstimateModelsBudgetCertificate.controlled,
      sampleUniformCauchyEstimateModelsBudgetCertificate]
  · norm_num [UniformCauchyEstimateModelsBudgetCertificate.budgetControlled,
      sampleUniformCauchyEstimateModelsBudgetCertificate]

example :
    sampleUniformCauchyEstimateModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformCauchyEstimateModelsBudgetCertificate.size := by
  apply uniformCauchyEstimateModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformCauchyEstimateModelsBudgetCertificate.controlled,
      sampleUniformCauchyEstimateModelsBudgetCertificate]
  · norm_num [UniformCauchyEstimateModelsBudgetCertificate.budgetControlled,
      sampleUniformCauchyEstimateModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformCauchyEstimateModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformCauchyEstimateModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformCauchyEstimateModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.UniformCauchyEstimateModels
