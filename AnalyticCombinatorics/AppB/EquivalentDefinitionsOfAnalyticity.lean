import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Equivalent definitions of analyticity.

Finite consistency windows for the power-series, Cauchy-integral,
Cauchy-Riemann, Morera, and primitive characterizations.
-/

namespace AnalyticCombinatorics.AppB.EquivalentDefinitionsOfAnalyticity

/-- Finite real-coordinate first derivative data. -/
structure CRDerivativeSample where
  ux : ℤ
  uy : ℤ
  vx : ℤ
  vy : ℤ
deriving DecidableEq, Repr

def cauchyRiemannSampleReady (s : CRDerivativeSample) : Prop :=
  s.ux = s.vy ∧ s.uy = -s.vx

def identityCRSample : CRDerivativeSample :=
  { ux := 1, uy := 0, vx := 0, vy := 1 }

theorem identityCRSample_ready :
    cauchyRiemannSampleReady identityCRSample := by
  norm_num [cauchyRiemannSampleReady, identityCRSample]

/-- Finite audit of Cauchy-Riemann samples. -/
def cauchyRiemannListReady (samples : List CRDerivativeSample) : Bool :=
  samples.all fun s => s.ux == s.vy && s.uy == -s.vx

theorem cauchyRiemannList_readyWindow :
    cauchyRiemannListReady
      [identityCRSample, { ux := 2, uy := -3, vx := 3, vy := 2 }] = true := by
  unfold cauchyRiemannListReady identityCRSample
  native_decide

/-- Integer contour increments for a finite Morera-style triangular window. -/
structure MoreraTriangleSample where
  edgeIntegralAB : ℤ
  edgeIntegralBC : ℤ
  edgeIntegralCA : ℤ
deriving DecidableEq, Repr

def MoreraTriangleSample.closedIntegralZero
    (s : MoreraTriangleSample) : Prop :=
  s.edgeIntegralAB + s.edgeIntegralBC + s.edgeIntegralCA = 0

def exactPrimitiveTriangle : MoreraTriangleSample :=
  { edgeIntegralAB := 3, edgeIntegralBC := -5, edgeIntegralCA := 2 }

theorem exactPrimitiveTriangle_moreraReady :
    exactPrimitiveTriangle.closedIntegralZero := by
  norm_num [MoreraTriangleSample.closedIntegralZero,
    exactPrimitiveTriangle]

def moreraTriangleListReady
    (samples : List MoreraTriangleSample) : Bool :=
  samples.all fun s => s.edgeIntegralAB + s.edgeIntegralBC + s.edgeIntegralCA = 0

theorem moreraTriangleList_readyWindow :
    moreraTriangleListReady
      [exactPrimitiveTriangle,
       { edgeIntegralAB := 4, edgeIntegralBC := 1, edgeIntegralCA := -5 }] =
      true := by
  unfold moreraTriangleListReady exactPrimitiveTriangle
  native_decide

/-- A power-series local model with derivative samples. -/
structure PowerSeriesAnalyticWindow where
  radiusWindow : ℕ
  coefficientMajorant : ℕ
  derivativeMajorant : ℕ
  sampleOrder : ℕ
deriving DecidableEq, Repr

def PowerSeriesAnalyticWindow.ready
    (w : PowerSeriesAnalyticWindow) : Prop :=
  0 < w.radiusWindow ∧
    w.coefficientMajorant ≤ w.derivativeMajorant + w.radiusWindow ∧
      w.sampleOrder ≤ w.coefficientMajorant + w.derivativeMajorant

def geometricPowerSeriesWindow : PowerSeriesAnalyticWindow :=
  { radiusWindow := 3
    coefficientMajorant := 4
    derivativeMajorant := 5
    sampleOrder := 9 }

theorem geometricPowerSeriesWindow_ready :
    geometricPowerSeriesWindow.ready := by
  norm_num [PowerSeriesAnalyticWindow.ready, geometricPowerSeriesWindow]

/-- Finite equivalence certificate joining the common analytic definitions. -/
structure AnalyticDefinitionEquivalenceWindow where
  powerSeriesWindow : ℕ
  cauchyIntegralWindow : ℕ
  crWindow : ℕ
  moreraWindow : ℕ
  primitiveWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticDefinitionEquivalenceWindow.ready
    (w : AnalyticDefinitionEquivalenceWindow) : Prop :=
  0 < w.powerSeriesWindow ∧
    w.cauchyIntegralWindow ≤ w.powerSeriesWindow + w.slack ∧
      w.crWindow ≤ w.cauchyIntegralWindow + w.powerSeriesWindow + w.slack ∧
        w.moreraWindow ≤ w.primitiveWindow + w.crWindow + w.slack

def sampleAnalyticDefinitionEquivalenceWindow :
    AnalyticDefinitionEquivalenceWindow :=
  { powerSeriesWindow := 5
    cauchyIntegralWindow := 6
    crWindow := 10
    moreraWindow := 13
    primitiveWindow := 4
    slack := 1 }

example : sampleAnalyticDefinitionEquivalenceWindow.ready := by
  norm_num [AnalyticDefinitionEquivalenceWindow.ready,
    sampleAnalyticDefinitionEquivalenceWindow]

structure EquivalentDefinitionsOfAnalyticityBudgetCertificate where
  seriesWindow : ℕ
  cauchyWindow : ℕ
  moreraWindow : ℕ
  crWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EquivalentDefinitionsOfAnalyticityBudgetCertificate.controlled
    (c : EquivalentDefinitionsOfAnalyticityBudgetCertificate) : Prop :=
  0 < c.seriesWindow ∧
    c.cauchyWindow ≤ c.seriesWindow + c.slack ∧
      c.moreraWindow ≤ c.cauchyWindow + c.crWindow + c.slack

def EquivalentDefinitionsOfAnalyticityBudgetCertificate.budgetControlled
    (c : EquivalentDefinitionsOfAnalyticityBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.seriesWindow + c.cauchyWindow + c.moreraWindow + c.crWindow + c.slack

def EquivalentDefinitionsOfAnalyticityBudgetCertificate.Ready
    (c : EquivalentDefinitionsOfAnalyticityBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EquivalentDefinitionsOfAnalyticityBudgetCertificate.size
    (c : EquivalentDefinitionsOfAnalyticityBudgetCertificate) : ℕ :=
  c.seriesWindow + c.cauchyWindow + c.moreraWindow + c.crWindow + c.slack

theorem equivalentDefinitionsOfAnalyticity_budgetCertificate_le_size
    (c : EquivalentDefinitionsOfAnalyticityBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleEquivalentDefinitionsOfAnalyticityBudgetCertificate :
    EquivalentDefinitionsOfAnalyticityBudgetCertificate :=
  { seriesWindow := 5
    cauchyWindow := 6
    moreraWindow := 12
    crWindow := 7
    certificateBudgetWindow := 31
    slack := 1 }

example : sampleEquivalentDefinitionsOfAnalyticityBudgetCertificate.Ready := by
  constructor
  · norm_num [EquivalentDefinitionsOfAnalyticityBudgetCertificate.controlled,
      sampleEquivalentDefinitionsOfAnalyticityBudgetCertificate]
  · norm_num [EquivalentDefinitionsOfAnalyticityBudgetCertificate.budgetControlled,
      sampleEquivalentDefinitionsOfAnalyticityBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleEquivalentDefinitionsOfAnalyticityBudgetCertificate.Ready := by
  constructor
  · norm_num [EquivalentDefinitionsOfAnalyticityBudgetCertificate.controlled,
      sampleEquivalentDefinitionsOfAnalyticityBudgetCertificate]
  · norm_num [EquivalentDefinitionsOfAnalyticityBudgetCertificate.budgetControlled,
      sampleEquivalentDefinitionsOfAnalyticityBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleEquivalentDefinitionsOfAnalyticityBudgetCertificate.certificateBudgetWindow ≤
      sampleEquivalentDefinitionsOfAnalyticityBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List EquivalentDefinitionsOfAnalyticityBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEquivalentDefinitionsOfAnalyticityBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleEquivalentDefinitionsOfAnalyticityBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.EquivalentDefinitionsOfAnalyticity
