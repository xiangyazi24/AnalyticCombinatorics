import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random metric space limit schemas.

The finite record stores point count, diameter scale, and distortion
slack.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomMetricSpaceLimitSchemas

structure RandomMetricSpaceData where
  pointCount : ℕ
  diameterScale : ℕ
  distortionSlack : ℕ
deriving DecidableEq, Repr

def pointCountPositive (d : RandomMetricSpaceData) : Prop :=
  0 < d.pointCount

def diameterScaleControlled (d : RandomMetricSpaceData) : Prop :=
  d.diameterScale ≤ d.pointCount + d.distortionSlack

def randomMetricSpaceReady (d : RandomMetricSpaceData) : Prop :=
  pointCountPositive d ∧ diameterScaleControlled d

def randomMetricSpaceBudget (d : RandomMetricSpaceData) : ℕ :=
  d.pointCount + d.diameterScale + d.distortionSlack

theorem randomMetricSpaceReady.points {d : RandomMetricSpaceData}
    (h : randomMetricSpaceReady d) :
    pointCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem diameterScale_le_randomMetricBudget
    (d : RandomMetricSpaceData) :
    d.diameterScale ≤ randomMetricSpaceBudget d := by
  unfold randomMetricSpaceBudget
  omega

def sampleRandomMetricSpaceData : RandomMetricSpaceData :=
  { pointCount := 9, diameterScale := 11, distortionSlack := 3 }

example : randomMetricSpaceReady sampleRandomMetricSpaceData := by
  norm_num [randomMetricSpaceReady, pointCountPositive]
  norm_num [diameterScaleControlled, sampleRandomMetricSpaceData]

example : randomMetricSpaceBudget sampleRandomMetricSpaceData = 23 := by
  native_decide

/-- Finite executable readiness audit for random metric-space windows. -/
def randomMetricSpaceListReady
    (windows : List RandomMetricSpaceData) : Bool :=
  windows.all fun d =>
    0 < d.pointCount && d.diameterScale ≤ d.pointCount + d.distortionSlack

theorem randomMetricSpaceList_readyWindow :
    randomMetricSpaceListReady
      [{ pointCount := 5, diameterScale := 6, distortionSlack := 1 },
       { pointCount := 9, diameterScale := 11, distortionSlack := 3 }] = true := by
  unfold randomMetricSpaceListReady
  native_decide

structure RandomMetricSpaceBudgetCertificate where
  pointCountWindow : ℕ
  diameterScaleWindow : ℕ
  distortionSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomMetricSpaceBudgetCertificate.controlled
    (c : RandomMetricSpaceBudgetCertificate) : Prop :=
  0 < c.pointCountWindow ∧
    c.diameterScaleWindow ≤ c.pointCountWindow + c.distortionSlackWindow + c.slack

def RandomMetricSpaceBudgetCertificate.budgetControlled
    (c : RandomMetricSpaceBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.pointCountWindow + c.diameterScaleWindow + c.distortionSlackWindow + c.slack

def RandomMetricSpaceBudgetCertificate.Ready
    (c : RandomMetricSpaceBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomMetricSpaceBudgetCertificate.size
    (c : RandomMetricSpaceBudgetCertificate) : ℕ :=
  c.pointCountWindow + c.diameterScaleWindow + c.distortionSlackWindow + c.slack

theorem randomMetricSpace_budgetCertificate_le_size
    (c : RandomMetricSpaceBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomMetricSpaceBudgetCertificate :
    RandomMetricSpaceBudgetCertificate :=
  { pointCountWindow := 9
    diameterScaleWindow := 11
    distortionSlackWindow := 3
    certificateBudgetWindow := 24
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomMetricSpaceBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomMetricSpaceBudgetCertificate.controlled,
      sampleRandomMetricSpaceBudgetCertificate]
  · norm_num [RandomMetricSpaceBudgetCertificate.budgetControlled,
      sampleRandomMetricSpaceBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomMetricSpaceBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomMetricSpaceBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomMetricSpaceBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomMetricSpaceBudgetCertificate.controlled,
      sampleRandomMetricSpaceBudgetCertificate]
  · norm_num [RandomMetricSpaceBudgetCertificate.budgetControlled,
      sampleRandomMetricSpaceBudgetCertificate]

example :
    sampleRandomMetricSpaceBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomMetricSpaceBudgetCertificate.size := by
  apply randomMetricSpace_budgetCertificate_le_size
  constructor
  · norm_num [RandomMetricSpaceBudgetCertificate.controlled,
      sampleRandomMetricSpaceBudgetCertificate]
  · norm_num [RandomMetricSpaceBudgetCertificate.budgetControlled,
      sampleRandomMetricSpaceBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomMetricSpaceBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomMetricSpaceBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomMetricSpaceBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomMetricSpaceLimitSchemas
