import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic norm models.

The finite schema records norm scale, derivative budget, and domain
slack.
-/

namespace AnalyticCombinatorics.AppB.AnalyticNormModels

structure AnalyticNormData where
  normScale : ℕ
  derivativeBudget : ℕ
  domainSlack : ℕ
deriving DecidableEq, Repr

def normScalePositive (d : AnalyticNormData) : Prop :=
  0 < d.normScale

def derivativeControlled (d : AnalyticNormData) : Prop :=
  d.derivativeBudget ≤ d.normScale + d.domainSlack

def analyticNormReady (d : AnalyticNormData) : Prop :=
  normScalePositive d ∧ derivativeControlled d

def analyticNormBudget (d : AnalyticNormData) : ℕ :=
  d.normScale + d.derivativeBudget + d.domainSlack

theorem analyticNormReady.scale {d : AnalyticNormData}
    (h : analyticNormReady d) :
    normScalePositive d ∧ derivativeControlled d ∧
      d.derivativeBudget ≤ analyticNormBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticNormBudget
  omega

theorem derivativeBudget_le_normBudget (d : AnalyticNormData) :
    d.derivativeBudget ≤ analyticNormBudget d := by
  unfold analyticNormBudget
  omega

def sampleAnalyticNormData : AnalyticNormData :=
  { normScale := 4, derivativeBudget := 6, domainSlack := 3 }

example : analyticNormReady sampleAnalyticNormData := by
  norm_num [analyticNormReady, normScalePositive]
  norm_num [derivativeControlled, sampleAnalyticNormData]

example : analyticNormBudget sampleAnalyticNormData = 13 := by
  native_decide

/-- Finite executable readiness audit for analytic norm windows. -/
def analyticNormListReady (windows : List AnalyticNormData) : Bool :=
  windows.all fun d =>
    0 < d.normScale && d.derivativeBudget ≤ d.normScale + d.domainSlack

theorem analyticNormList_readyWindow :
    analyticNormListReady
      [{ normScale := 3, derivativeBudget := 4, domainSlack := 1 },
       { normScale := 4, derivativeBudget := 6, domainSlack := 3 }] = true := by
  unfold analyticNormListReady
  native_decide


structure AnalyticNormModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticNormModelsBudgetCertificate.controlled
    (c : AnalyticNormModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticNormModelsBudgetCertificate.budgetControlled
    (c : AnalyticNormModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticNormModelsBudgetCertificate.Ready
    (c : AnalyticNormModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticNormModelsBudgetCertificate.size
    (c : AnalyticNormModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticNormModels_budgetCertificate_le_size
    (c : AnalyticNormModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticNormModelsBudgetCertificate :
    AnalyticNormModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticNormModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticNormModelsBudgetCertificate.controlled,
      sampleAnalyticNormModelsBudgetCertificate]
  · norm_num [AnalyticNormModelsBudgetCertificate.budgetControlled,
      sampleAnalyticNormModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticNormModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticNormModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticNormModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticNormModelsBudgetCertificate.controlled,
      sampleAnalyticNormModelsBudgetCertificate]
  · norm_num [AnalyticNormModelsBudgetCertificate.budgetControlled,
      sampleAnalyticNormModelsBudgetCertificate]

example :
    sampleAnalyticNormModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticNormModelsBudgetCertificate.size := by
  apply analyticNormModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticNormModelsBudgetCertificate.controlled,
      sampleAnalyticNormModelsBudgetCertificate]
  · norm_num [AnalyticNormModelsBudgetCertificate.budgetControlled,
      sampleAnalyticNormModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticNormModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticNormModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticNormModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.AnalyticNormModels
