import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multivariate critical-cone schemas.

Finite normal-cone and direction-cone bookkeeping for multivariate
coefficient asymptotics.
-/

namespace AnalyticCombinatorics.PartB.Ch9.MultivariateCriticalConeSchemas

/-- A rational slope interval `[lowerNumerator/lowerDenominator,
upperNumerator/upperDenominator]` for bivariate directions. -/
structure DirectionCone where
  lowerNumerator : ℕ
  lowerDenominator : ℕ
  upperNumerator : ℕ
  upperDenominator : ℕ
deriving DecidableEq, Repr

def DirectionCone.denominatorsPositive (cone : DirectionCone) : Prop :=
  0 < cone.lowerDenominator ∧ 0 < cone.upperDenominator

def DirectionCone.ordered (cone : DirectionCone) : Prop :=
  cone.lowerNumerator * cone.upperDenominator ≤
    cone.upperNumerator * cone.lowerDenominator

def DirectionCone.ready (cone : DirectionCone) : Prop :=
  cone.denominatorsPositive ∧ cone.ordered

/-- Direction `(x,y)` has slope in the cone. -/
def DirectionCone.containsDirection
    (cone : DirectionCone) (x y : ℕ) : Prop :=
  cone.lowerNumerator * x ≤ cone.lowerDenominator * y ∧
    cone.upperDenominator * y ≤ cone.upperNumerator * x

def broadDiagonalCone : DirectionCone :=
  { lowerNumerator := 1
    lowerDenominator := 2
    upperNumerator := 2
    upperDenominator := 1 }

theorem broadDiagonalCone_ready :
    broadDiagonalCone.ready := by
  norm_num [DirectionCone.ready, DirectionCone.denominatorsPositive,
    DirectionCone.ordered, broadDiagonalCone]

theorem broadDiagonalCone_contains_diagonal :
    broadDiagonalCone.containsDirection 1 1 := by
  norm_num [DirectionCone.containsDirection, broadDiagonalCone]

/-- Boolean audit for finite direction samples. -/
def directionConeSamplesReady
    (cone : DirectionCone) (samples : List (ℕ × ℕ)) : Bool :=
  samples.all fun sample =>
    cone.lowerNumerator * sample.1 ≤ cone.lowerDenominator * sample.2 &&
      cone.upperDenominator * sample.2 ≤ cone.upperNumerator * sample.1

theorem broadDiagonalCone_sampleWindow :
    directionConeSamplesReady broadDiagonalCone
      [(1, 1), (2, 1), (3, 2), (2, 3), (4, 5)] = true := by
  unfold directionConeSamplesReady broadDiagonalCone
  native_decide

/-- A finite critical direction window with gradient and Hessian data. -/
structure CriticalConeWindow where
  directionX : ℕ
  directionY : ℕ
  gradientX : ℕ
  gradientY : ℕ
  hessianDeterminant : ℕ
  coneSlack : ℕ
deriving DecidableEq, Repr

def CriticalConeWindow.directionPositive
    (w : CriticalConeWindow) : Prop :=
  0 < w.directionX ∧ 0 < w.directionY

def CriticalConeWindow.criticalBalanced
    (w : CriticalConeWindow) : Prop :=
  w.directionX * w.gradientY = w.directionY * w.gradientX

def CriticalConeWindow.nonDegenerate
    (w : CriticalConeWindow) : Prop :=
  0 < w.hessianDeterminant

def CriticalConeWindow.slackControlled
    (w : CriticalConeWindow) : Prop :=
  w.coneSlack ≤ w.directionX + w.directionY + w.hessianDeterminant

def CriticalConeWindow.ready
    (w : CriticalConeWindow) : Prop :=
  w.directionPositive ∧ w.criticalBalanced ∧
    w.nonDegenerate ∧ w.slackControlled

def diagonalCriticalConeWindow : CriticalConeWindow :=
  { directionX := 1
    directionY := 1
    gradientX := 2
    gradientY := 2
    hessianDeterminant := 3
    coneSlack := 1 }

theorem diagonalCriticalConeWindow_ready :
    diagonalCriticalConeWindow.ready := by
  norm_num [CriticalConeWindow.ready,
    CriticalConeWindow.directionPositive,
    CriticalConeWindow.criticalBalanced,
    CriticalConeWindow.nonDegenerate,
    CriticalConeWindow.slackControlled,
    diagonalCriticalConeWindow]

/-- Normal-cone certificate: the critical direction lies in the direction cone. -/
def normalConeContainsCriticalDirection
    (cone : DirectionCone) (w : CriticalConeWindow) : Prop :=
  cone.ready ∧ w.ready ∧
    cone.containsDirection w.directionX w.directionY

theorem broadCone_contains_diagonalCriticalWindow :
    normalConeContainsCriticalDirection
      broadDiagonalCone diagonalCriticalConeWindow := by
  constructor
  · exact broadDiagonalCone_ready
  constructor
  · exact diagonalCriticalConeWindow_ready
  · exact broadDiagonalCone_contains_diagonal

example :
    normalConeContainsCriticalDirection
      broadDiagonalCone diagonalCriticalConeWindow := by
  exact broadCone_contains_diagonalCriticalWindow

/-- Finite executable audit for critical cone windows. -/
def criticalConeWindowListReady
    (data : List CriticalConeWindow) : Bool :=
  data.all fun w =>
    0 < w.directionX &&
      0 < w.directionY &&
        w.directionX * w.gradientY == w.directionY * w.gradientX &&
          0 < w.hessianDeterminant &&
            w.coneSlack ≤ w.directionX + w.directionY + w.hessianDeterminant

theorem criticalConeWindowList_readyWindow :
    criticalConeWindowListReady
      [diagonalCriticalConeWindow,
       { directionX := 2, directionY := 3, gradientX := 4,
         gradientY := 6, hessianDeterminant := 5, coneSlack := 3 }] =
      true := by
  unfold criticalConeWindowListReady diagonalCriticalConeWindow
  native_decide

example :
    criticalConeWindowListReady [diagonalCriticalConeWindow] = true := by
  unfold criticalConeWindowListReady diagonalCriticalConeWindow
  native_decide

structure MultivariateCriticalConeSchemasBudgetCertificate where
  coneWindow : ℕ
  directionWindow : ℕ
  hessianWindow : ℕ
  normalConeWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultivariateCriticalConeSchemasBudgetCertificate.controlled
    (c : MultivariateCriticalConeSchemasBudgetCertificate) : Prop :=
  0 < c.coneWindow ∧
    0 < c.hessianWindow ∧
      c.normalConeWindow ≤ c.coneWindow + c.directionWindow + c.slack

def MultivariateCriticalConeSchemasBudgetCertificate.budgetControlled
    (c : MultivariateCriticalConeSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.coneWindow + c.directionWindow + c.hessianWindow +
      c.normalConeWindow + c.slack

def MultivariateCriticalConeSchemasBudgetCertificate.Ready
    (c : MultivariateCriticalConeSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultivariateCriticalConeSchemasBudgetCertificate.size
    (c : MultivariateCriticalConeSchemasBudgetCertificate) : ℕ :=
  c.coneWindow + c.directionWindow + c.hessianWindow +
    c.normalConeWindow + c.slack

theorem multivariateCriticalConeSchemas_budgetCertificate_le_size
    (c : MultivariateCriticalConeSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleMultivariateCriticalConeSchemasBudgetCertificate :
    MultivariateCriticalConeSchemasBudgetCertificate :=
  { coneWindow := 5
    directionWindow := 6
    hessianWindow := 7
    normalConeWindow := 12
    certificateBudgetWindow := 31
    slack := 1 }

example : sampleMultivariateCriticalConeSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivariateCriticalConeSchemasBudgetCertificate.controlled,
      sampleMultivariateCriticalConeSchemasBudgetCertificate]
  · norm_num [MultivariateCriticalConeSchemasBudgetCertificate.budgetControlled,
      sampleMultivariateCriticalConeSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMultivariateCriticalConeSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivariateCriticalConeSchemasBudgetCertificate.controlled,
      sampleMultivariateCriticalConeSchemasBudgetCertificate]
  · norm_num [MultivariateCriticalConeSchemasBudgetCertificate.budgetControlled,
      sampleMultivariateCriticalConeSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultivariateCriticalConeSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMultivariateCriticalConeSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MultivariateCriticalConeSchemasBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultivariateCriticalConeSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleMultivariateCriticalConeSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.MultivariateCriticalConeSchemas
