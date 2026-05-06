import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random geometric graph limit schemas.

The finite schema records points, radius scale, and boundary slack for
random geometric graph limits.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomGeometricGraphLimitSchemas

structure RandomGeometricGraphData where
  pointCount : ℕ
  radiusScale : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def pointCountPositive (d : RandomGeometricGraphData) : Prop :=
  0 < d.pointCount

def radiusControlled (d : RandomGeometricGraphData) : Prop :=
  d.radiusScale ≤ d.pointCount + d.boundarySlack

def randomGeometricGraphReady (d : RandomGeometricGraphData) : Prop :=
  pointCountPositive d ∧ radiusControlled d

def randomGeometricGraphBudget (d : RandomGeometricGraphData) : ℕ :=
  d.pointCount + d.radiusScale + d.boundarySlack

theorem randomGeometricGraphReady.points {d : RandomGeometricGraphData}
    (h : randomGeometricGraphReady d) :
    pointCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem radiusScale_le_randomGeometricBudget
    (d : RandomGeometricGraphData) :
    d.radiusScale ≤ randomGeometricGraphBudget d := by
  unfold randomGeometricGraphBudget
  omega

def sampleRandomGeometricGraphData : RandomGeometricGraphData :=
  { pointCount := 9, radiusScale := 11, boundarySlack := 3 }

example : randomGeometricGraphReady sampleRandomGeometricGraphData := by
  norm_num [randomGeometricGraphReady, pointCountPositive]
  norm_num [radiusControlled, sampleRandomGeometricGraphData]

example : randomGeometricGraphBudget sampleRandomGeometricGraphData = 23 := by
  native_decide

/-- Finite executable readiness audit for random geometric graph windows. -/
def randomGeometricGraphListReady
    (windows : List RandomGeometricGraphData) : Bool :=
  windows.all fun d =>
    0 < d.pointCount && d.radiusScale ≤ d.pointCount + d.boundarySlack

theorem randomGeometricGraphList_readyWindow :
    randomGeometricGraphListReady
      [{ pointCount := 5, radiusScale := 6, boundarySlack := 1 },
       { pointCount := 9, radiusScale := 11, boundarySlack := 3 }] = true := by
  unfold randomGeometricGraphListReady
  native_decide

structure RandomGeometricGraphBudgetCertificate where
  pointCountWindow : ℕ
  radiusScaleWindow : ℕ
  boundarySlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomGeometricGraphBudgetCertificate.controlled
    (c : RandomGeometricGraphBudgetCertificate) : Prop :=
  0 < c.pointCountWindow ∧
    c.radiusScaleWindow ≤ c.pointCountWindow + c.boundarySlackWindow + c.slack

def RandomGeometricGraphBudgetCertificate.budgetControlled
    (c : RandomGeometricGraphBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.pointCountWindow + c.radiusScaleWindow + c.boundarySlackWindow + c.slack

def RandomGeometricGraphBudgetCertificate.Ready
    (c : RandomGeometricGraphBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomGeometricGraphBudgetCertificate.size
    (c : RandomGeometricGraphBudgetCertificate) : ℕ :=
  c.pointCountWindow + c.radiusScaleWindow + c.boundarySlackWindow + c.slack

theorem randomGeometricGraph_budgetCertificate_le_size
    (c : RandomGeometricGraphBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomGeometricGraphBudgetCertificate :
    RandomGeometricGraphBudgetCertificate :=
  { pointCountWindow := 9
    radiusScaleWindow := 11
    boundarySlackWindow := 3
    certificateBudgetWindow := 24
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomGeometricGraphBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomGeometricGraphBudgetCertificate.controlled,
      sampleRandomGeometricGraphBudgetCertificate]
  · norm_num [RandomGeometricGraphBudgetCertificate.budgetControlled,
      sampleRandomGeometricGraphBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomGeometricGraphBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomGeometricGraphBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomGeometricGraphBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomGeometricGraphBudgetCertificate.controlled,
      sampleRandomGeometricGraphBudgetCertificate]
  · norm_num [RandomGeometricGraphBudgetCertificate.budgetControlled,
      sampleRandomGeometricGraphBudgetCertificate]

example :
    sampleRandomGeometricGraphBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomGeometricGraphBudgetCertificate.size := by
  apply randomGeometricGraph_budgetCertificate_le_size
  constructor
  · norm_num [RandomGeometricGraphBudgetCertificate.controlled,
      sampleRandomGeometricGraphBudgetCertificate]
  · norm_num [RandomGeometricGraphBudgetCertificate.budgetControlled,
      sampleRandomGeometricGraphBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomGeometricGraphBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomGeometricGraphBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomGeometricGraphBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomGeometricGraphLimitSchemas
