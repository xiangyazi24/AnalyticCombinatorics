import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic boundary layer models.

The finite abstraction records boundary thickness, analytic margin, and
patching slack.
-/

namespace AnalyticCombinatorics.AppB.AnalyticBoundaryLayerModels

structure AnalyticBoundaryLayerData where
  boundaryThickness : ℕ
  analyticMargin : ℕ
  patchSlack : ℕ
deriving DecidableEq, Repr

def analyticMarginPositive (d : AnalyticBoundaryLayerData) : Prop :=
  0 < d.analyticMargin

def thicknessControlled (d : AnalyticBoundaryLayerData) : Prop :=
  d.boundaryThickness ≤ d.analyticMargin + d.patchSlack

def analyticBoundaryLayerReady (d : AnalyticBoundaryLayerData) : Prop :=
  analyticMarginPositive d ∧ thicknessControlled d

def analyticBoundaryLayerBudget (d : AnalyticBoundaryLayerData) : ℕ :=
  d.boundaryThickness + d.analyticMargin + d.patchSlack

theorem analyticBoundaryLayerReady.margin
    {d : AnalyticBoundaryLayerData}
    (h : analyticBoundaryLayerReady d) :
    analyticMarginPositive d ∧ thicknessControlled d ∧
      d.boundaryThickness ≤ analyticBoundaryLayerBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticBoundaryLayerBudget
  omega

theorem thickness_le_boundaryLayerBudget
    (d : AnalyticBoundaryLayerData) :
    d.boundaryThickness ≤ analyticBoundaryLayerBudget d := by
  unfold analyticBoundaryLayerBudget
  omega

def sampleAnalyticBoundaryLayerData : AnalyticBoundaryLayerData :=
  { boundaryThickness := 6, analyticMargin := 4, patchSlack := 3 }

example : analyticBoundaryLayerReady sampleAnalyticBoundaryLayerData := by
  norm_num [analyticBoundaryLayerReady, analyticMarginPositive]
  norm_num [thicknessControlled, sampleAnalyticBoundaryLayerData]

example : analyticBoundaryLayerBudget sampleAnalyticBoundaryLayerData = 13 := by
  native_decide


structure AnalyticBoundaryLayerModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticBoundaryLayerModelsBudgetCertificate.controlled
    (c : AnalyticBoundaryLayerModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticBoundaryLayerModelsBudgetCertificate.budgetControlled
    (c : AnalyticBoundaryLayerModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticBoundaryLayerModelsBudgetCertificate.Ready
    (c : AnalyticBoundaryLayerModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticBoundaryLayerModelsBudgetCertificate.size
    (c : AnalyticBoundaryLayerModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticBoundaryLayerModels_budgetCertificate_le_size
    (c : AnalyticBoundaryLayerModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticBoundaryLayerModelsBudgetCertificate :
    AnalyticBoundaryLayerModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticBoundaryLayerModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticBoundaryLayerModelsBudgetCertificate.controlled,
      sampleAnalyticBoundaryLayerModelsBudgetCertificate]
  · norm_num [AnalyticBoundaryLayerModelsBudgetCertificate.budgetControlled,
      sampleAnalyticBoundaryLayerModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticBoundaryLayerModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticBoundaryLayerModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticBoundaryLayerModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticBoundaryLayerModelsBudgetCertificate.controlled,
      sampleAnalyticBoundaryLayerModelsBudgetCertificate]
  · norm_num [AnalyticBoundaryLayerModelsBudgetCertificate.budgetControlled,
      sampleAnalyticBoundaryLayerModelsBudgetCertificate]

example :
    sampleAnalyticBoundaryLayerModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticBoundaryLayerModelsBudgetCertificate.size := by
  apply analyticBoundaryLayerModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticBoundaryLayerModelsBudgetCertificate.controlled,
      sampleAnalyticBoundaryLayerModelsBudgetCertificate]
  · norm_num [AnalyticBoundaryLayerModelsBudgetCertificate.budgetControlled,
      sampleAnalyticBoundaryLayerModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticBoundaryLayerModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticBoundaryLayerModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticBoundaryLayerModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticBoundaryLayerModels
