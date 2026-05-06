import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic kernel bound models.

The finite schema records kernel order, denominator margin, and contour
slack.
-/

namespace AnalyticCombinatorics.AppB.AnalyticKernelBoundModels

structure AnalyticKernelBoundData where
  kernelOrder : ℕ
  denominatorMargin : ℕ
  contourSlack : ℕ
deriving DecidableEq, Repr

def denominatorMarginPositive (d : AnalyticKernelBoundData) : Prop :=
  0 < d.denominatorMargin

def kernelOrderControlled (d : AnalyticKernelBoundData) : Prop :=
  d.kernelOrder ≤ d.denominatorMargin + d.contourSlack

def analyticKernelBoundReady (d : AnalyticKernelBoundData) : Prop :=
  denominatorMarginPositive d ∧ kernelOrderControlled d

def analyticKernelBoundBudget (d : AnalyticKernelBoundData) : ℕ :=
  d.kernelOrder + d.denominatorMargin + d.contourSlack

theorem analyticKernelBoundReady.denominator
    {d : AnalyticKernelBoundData}
    (h : analyticKernelBoundReady d) :
    denominatorMarginPositive d ∧ kernelOrderControlled d ∧
      d.kernelOrder ≤ analyticKernelBoundBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticKernelBoundBudget
  omega

theorem kernelOrder_le_kernelBoundBudget (d : AnalyticKernelBoundData) :
    d.kernelOrder ≤ analyticKernelBoundBudget d := by
  unfold analyticKernelBoundBudget
  omega

def sampleAnalyticKernelBoundData : AnalyticKernelBoundData :=
  { kernelOrder := 6, denominatorMargin := 4, contourSlack := 3 }

example : analyticKernelBoundReady sampleAnalyticKernelBoundData := by
  norm_num [analyticKernelBoundReady, denominatorMarginPositive]
  norm_num [kernelOrderControlled, sampleAnalyticKernelBoundData]

example : analyticKernelBoundBudget sampleAnalyticKernelBoundData = 13 := by
  native_decide


structure AnalyticKernelBoundModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticKernelBoundModelsBudgetCertificate.controlled
    (c : AnalyticKernelBoundModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticKernelBoundModelsBudgetCertificate.budgetControlled
    (c : AnalyticKernelBoundModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticKernelBoundModelsBudgetCertificate.Ready
    (c : AnalyticKernelBoundModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticKernelBoundModelsBudgetCertificate.size
    (c : AnalyticKernelBoundModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticKernelBoundModels_budgetCertificate_le_size
    (c : AnalyticKernelBoundModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticKernelBoundModelsBudgetCertificate :
    AnalyticKernelBoundModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticKernelBoundModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticKernelBoundModelsBudgetCertificate.controlled,
      sampleAnalyticKernelBoundModelsBudgetCertificate]
  · norm_num [AnalyticKernelBoundModelsBudgetCertificate.budgetControlled,
      sampleAnalyticKernelBoundModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticKernelBoundModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticKernelBoundModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticKernelBoundModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticKernelBoundModelsBudgetCertificate.controlled,
      sampleAnalyticKernelBoundModelsBudgetCertificate]
  · norm_num [AnalyticKernelBoundModelsBudgetCertificate.budgetControlled,
      sampleAnalyticKernelBoundModelsBudgetCertificate]

example :
    sampleAnalyticKernelBoundModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticKernelBoundModelsBudgetCertificate.size := by
  apply analyticKernelBoundModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticKernelBoundModelsBudgetCertificate.controlled,
      sampleAnalyticKernelBoundModelsBudgetCertificate]
  · norm_num [AnalyticKernelBoundModelsBudgetCertificate.budgetControlled,
      sampleAnalyticKernelBoundModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticKernelBoundModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticKernelBoundModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticKernelBoundModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticKernelBoundModels
