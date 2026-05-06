import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic Riemann surface models.

This module records finite bookkeeping for Riemann surface charts.
-/

namespace AnalyticCombinatorics.AppB.AnalyticRiemannSurfaceModels

structure RiemannSurfaceData where
  chartCount : ℕ
  transitionCount : ℕ
  atlasSlack : ℕ
deriving DecidableEq, Repr

def hasChartCount (d : RiemannSurfaceData) : Prop :=
  0 < d.chartCount

def transitionCountControlled (d : RiemannSurfaceData) : Prop :=
  d.transitionCount ≤ d.chartCount + d.atlasSlack

def riemannSurfaceReady (d : RiemannSurfaceData) : Prop :=
  hasChartCount d ∧ transitionCountControlled d

def riemannSurfaceBudget (d : RiemannSurfaceData) : ℕ :=
  d.chartCount + d.transitionCount + d.atlasSlack

theorem riemannSurfaceReady.hasChartCount {d : RiemannSurfaceData}
    (h : riemannSurfaceReady d) :
    hasChartCount d ∧ transitionCountControlled d ∧
      d.transitionCount ≤ riemannSurfaceBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold riemannSurfaceBudget
  omega

theorem transitionCount_le_budget (d : RiemannSurfaceData) :
    d.transitionCount ≤ riemannSurfaceBudget d := by
  unfold riemannSurfaceBudget
  omega

def sampleRiemannSurfaceData : RiemannSurfaceData :=
  { chartCount := 6, transitionCount := 8, atlasSlack := 3 }

example : riemannSurfaceReady sampleRiemannSurfaceData := by
  norm_num [riemannSurfaceReady, hasChartCount]
  norm_num [transitionCountControlled, sampleRiemannSurfaceData]

example : riemannSurfaceBudget sampleRiemannSurfaceData = 17 := by
  native_decide

structure RiemannSurfaceWindow where
  chartWindow : ℕ
  transitionWindow : ℕ
  atlasSlack : ℕ
  atlasBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RiemannSurfaceWindow.transitionsControlled (w : RiemannSurfaceWindow) : Prop :=
  w.transitionWindow ≤ w.chartWindow + w.atlasSlack + w.slack

def riemannSurfaceWindowReady (w : RiemannSurfaceWindow) : Prop :=
  0 < w.chartWindow ∧ w.transitionsControlled ∧
    w.atlasBudget ≤ w.chartWindow + w.transitionWindow + w.slack

def RiemannSurfaceWindow.certificate (w : RiemannSurfaceWindow) : ℕ :=
  w.chartWindow + w.transitionWindow + w.atlasSlack + w.atlasBudget + w.slack

theorem riemannSurface_atlasBudget_le_certificate (w : RiemannSurfaceWindow) :
    w.atlasBudget ≤ w.certificate := by
  unfold RiemannSurfaceWindow.certificate
  omega

def sampleRiemannSurfaceWindow : RiemannSurfaceWindow :=
  { chartWindow := 5, transitionWindow := 7, atlasSlack := 2, atlasBudget := 14, slack := 2 }

example : riemannSurfaceWindowReady sampleRiemannSurfaceWindow := by
  norm_num [riemannSurfaceWindowReady, RiemannSurfaceWindow.transitionsControlled,
    sampleRiemannSurfaceWindow]


structure AnalyticRiemannSurfaceModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticRiemannSurfaceModelsBudgetCertificate.controlled
    (c : AnalyticRiemannSurfaceModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticRiemannSurfaceModelsBudgetCertificate.budgetControlled
    (c : AnalyticRiemannSurfaceModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticRiemannSurfaceModelsBudgetCertificate.Ready
    (c : AnalyticRiemannSurfaceModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticRiemannSurfaceModelsBudgetCertificate.size
    (c : AnalyticRiemannSurfaceModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticRiemannSurfaceModels_budgetCertificate_le_size
    (c : AnalyticRiemannSurfaceModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticRiemannSurfaceModelsBudgetCertificate :
    AnalyticRiemannSurfaceModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticRiemannSurfaceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticRiemannSurfaceModelsBudgetCertificate.controlled,
      sampleAnalyticRiemannSurfaceModelsBudgetCertificate]
  · norm_num [AnalyticRiemannSurfaceModelsBudgetCertificate.budgetControlled,
      sampleAnalyticRiemannSurfaceModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticRiemannSurfaceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticRiemannSurfaceModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticRiemannSurfaceModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticRiemannSurfaceModelsBudgetCertificate.controlled,
      sampleAnalyticRiemannSurfaceModelsBudgetCertificate]
  · norm_num [AnalyticRiemannSurfaceModelsBudgetCertificate.budgetControlled,
      sampleAnalyticRiemannSurfaceModelsBudgetCertificate]

example :
    sampleAnalyticRiemannSurfaceModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticRiemannSurfaceModelsBudgetCertificate.size := by
  apply analyticRiemannSurfaceModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticRiemannSurfaceModelsBudgetCertificate.controlled,
      sampleAnalyticRiemannSurfaceModelsBudgetCertificate]
  · norm_num [AnalyticRiemannSurfaceModelsBudgetCertificate.budgetControlled,
      sampleAnalyticRiemannSurfaceModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticRiemannSurfaceModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticRiemannSurfaceModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticRiemannSurfaceModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticRiemannSurfaceModels
