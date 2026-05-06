import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic normalization models.

The finite abstraction records normalizing scale, derivative budget, and
domain slack.
-/

namespace AnalyticCombinatorics.AppB.AnalyticNormalizationModels

structure AnalyticNormalizationData where
  normalizingScale : ℕ
  derivativeBudget : ℕ
  domainSlack : ℕ
deriving DecidableEq, Repr

def normalizingScalePositive (d : AnalyticNormalizationData) : Prop :=
  0 < d.normalizingScale

def derivativeBudgetControlled (d : AnalyticNormalizationData) : Prop :=
  d.derivativeBudget ≤ d.normalizingScale + d.domainSlack

def analyticNormalizationReady (d : AnalyticNormalizationData) : Prop :=
  normalizingScalePositive d ∧ derivativeBudgetControlled d

def analyticNormalizationBudget (d : AnalyticNormalizationData) : ℕ :=
  d.normalizingScale + d.derivativeBudget + d.domainSlack

theorem analyticNormalizationReady.scale
    {d : AnalyticNormalizationData}
    (h : analyticNormalizationReady d) :
    normalizingScalePositive d ∧ derivativeBudgetControlled d ∧
      d.derivativeBudget ≤ analyticNormalizationBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticNormalizationBudget
  omega

theorem derivativeBudget_le_normalizationBudget
    (d : AnalyticNormalizationData) :
    d.derivativeBudget ≤ analyticNormalizationBudget d := by
  unfold analyticNormalizationBudget
  omega

def sampleAnalyticNormalizationData : AnalyticNormalizationData :=
  { normalizingScale := 6, derivativeBudget := 8, domainSlack := 3 }

example : analyticNormalizationReady sampleAnalyticNormalizationData := by
  norm_num [analyticNormalizationReady, normalizingScalePositive]
  norm_num [derivativeBudgetControlled, sampleAnalyticNormalizationData]

example : analyticNormalizationBudget sampleAnalyticNormalizationData = 17 := by
  native_decide


structure AnalyticNormalizationModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticNormalizationModelsBudgetCertificate.controlled
    (c : AnalyticNormalizationModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticNormalizationModelsBudgetCertificate.budgetControlled
    (c : AnalyticNormalizationModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticNormalizationModelsBudgetCertificate.Ready
    (c : AnalyticNormalizationModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticNormalizationModelsBudgetCertificate.size
    (c : AnalyticNormalizationModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticNormalizationModels_budgetCertificate_le_size
    (c : AnalyticNormalizationModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticNormalizationModelsBudgetCertificate :
    AnalyticNormalizationModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticNormalizationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticNormalizationModelsBudgetCertificate.controlled,
      sampleAnalyticNormalizationModelsBudgetCertificate]
  · norm_num [AnalyticNormalizationModelsBudgetCertificate.budgetControlled,
      sampleAnalyticNormalizationModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticNormalizationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticNormalizationModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticNormalizationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticNormalizationModelsBudgetCertificate.controlled,
      sampleAnalyticNormalizationModelsBudgetCertificate]
  · norm_num [AnalyticNormalizationModelsBudgetCertificate.budgetControlled,
      sampleAnalyticNormalizationModelsBudgetCertificate]

example :
    sampleAnalyticNormalizationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticNormalizationModelsBudgetCertificate.size := by
  apply analyticNormalizationModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticNormalizationModelsBudgetCertificate.controlled,
      sampleAnalyticNormalizationModelsBudgetCertificate]
  · norm_num [AnalyticNormalizationModelsBudgetCertificate.budgetControlled,
      sampleAnalyticNormalizationModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticNormalizationModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticNormalizationModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticNormalizationModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticNormalizationModels
