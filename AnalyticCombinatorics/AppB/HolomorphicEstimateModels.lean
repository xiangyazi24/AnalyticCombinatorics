import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Holomorphic estimate models.

The finite schema records domain margin, derivative budget, and norm
slack for holomorphic estimates.
-/

namespace AnalyticCombinatorics.AppB.HolomorphicEstimateModels

structure HolomorphicEstimateData where
  domainMargin : ℕ
  derivativeBudget : ℕ
  normSlack : ℕ
deriving DecidableEq, Repr

def domainMarginPositive (d : HolomorphicEstimateData) : Prop :=
  0 < d.domainMargin

def derivativeBudgetControlled (d : HolomorphicEstimateData) : Prop :=
  d.derivativeBudget ≤ d.domainMargin + d.normSlack

def holomorphicEstimateReady (d : HolomorphicEstimateData) : Prop :=
  domainMarginPositive d ∧ derivativeBudgetControlled d

def holomorphicEstimateBudget (d : HolomorphicEstimateData) : ℕ :=
  d.domainMargin + d.derivativeBudget + d.normSlack

theorem holomorphicEstimateReady.margin {d : HolomorphicEstimateData}
    (h : holomorphicEstimateReady d) :
    domainMarginPositive d ∧ derivativeBudgetControlled d ∧
      d.derivativeBudget ≤ holomorphicEstimateBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold holomorphicEstimateBudget
  omega

theorem derivativeBudget_le_holomorphicEstimateBudget
    (d : HolomorphicEstimateData) :
    d.derivativeBudget ≤ holomorphicEstimateBudget d := by
  unfold holomorphicEstimateBudget
  omega

def sampleHolomorphicEstimateData : HolomorphicEstimateData :=
  { domainMargin := 5, derivativeBudget := 7, normSlack := 3 }

example : holomorphicEstimateReady sampleHolomorphicEstimateData := by
  norm_num [holomorphicEstimateReady, domainMarginPositive]
  norm_num [derivativeBudgetControlled, sampleHolomorphicEstimateData]

example : holomorphicEstimateBudget sampleHolomorphicEstimateData = 15 := by
  native_decide


structure HolomorphicEstimateModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HolomorphicEstimateModelsBudgetCertificate.controlled
    (c : HolomorphicEstimateModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HolomorphicEstimateModelsBudgetCertificate.budgetControlled
    (c : HolomorphicEstimateModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HolomorphicEstimateModelsBudgetCertificate.Ready
    (c : HolomorphicEstimateModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HolomorphicEstimateModelsBudgetCertificate.size
    (c : HolomorphicEstimateModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem holomorphicEstimateModels_budgetCertificate_le_size
    (c : HolomorphicEstimateModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHolomorphicEstimateModelsBudgetCertificate :
    HolomorphicEstimateModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleHolomorphicEstimateModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [HolomorphicEstimateModelsBudgetCertificate.controlled,
      sampleHolomorphicEstimateModelsBudgetCertificate]
  · norm_num [HolomorphicEstimateModelsBudgetCertificate.budgetControlled,
      sampleHolomorphicEstimateModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHolomorphicEstimateModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleHolomorphicEstimateModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleHolomorphicEstimateModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [HolomorphicEstimateModelsBudgetCertificate.controlled,
      sampleHolomorphicEstimateModelsBudgetCertificate]
  · norm_num [HolomorphicEstimateModelsBudgetCertificate.budgetControlled,
      sampleHolomorphicEstimateModelsBudgetCertificate]

example :
    sampleHolomorphicEstimateModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleHolomorphicEstimateModelsBudgetCertificate.size := by
  apply holomorphicEstimateModels_budgetCertificate_le_size
  constructor
  · norm_num [HolomorphicEstimateModelsBudgetCertificate.controlled,
      sampleHolomorphicEstimateModelsBudgetCertificate]
  · norm_num [HolomorphicEstimateModelsBudgetCertificate.budgetControlled,
      sampleHolomorphicEstimateModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List HolomorphicEstimateModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHolomorphicEstimateModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHolomorphicEstimateModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.HolomorphicEstimateModels
