import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multivariate smooth-point schemas.

Finite bookkeeping for the smooth minimal critical-point case in
multivariate analytic combinatorics.
-/

namespace AnalyticCombinatorics.PartB.Ch9.MultivariateSmoothPointSchemas

/-- A two-variable smooth critical point, represented by positive rational
coordinates with a shared denominator and an integer Hessian data. -/
structure SmoothCriticalPoint where
  xNumerator : ℕ
  yNumerator : ℕ
  commonDenominator : ℕ
  directionX : ℕ
  directionY : ℕ
  hessianMinor : ℕ
deriving DecidableEq, Repr

def SmoothCriticalPoint.positiveCoordinates
    (p : SmoothCriticalPoint) : Prop :=
  0 < p.xNumerator ∧ 0 < p.yNumerator ∧ 0 < p.commonDenominator

def SmoothCriticalPoint.directionBalanced
    (p : SmoothCriticalPoint) : Prop :=
  p.directionX * p.yNumerator = p.directionY * p.xNumerator

def SmoothCriticalPoint.ready
    (p : SmoothCriticalPoint) : Prop :=
  p.positiveCoordinates ∧ p.directionBalanced ∧ 0 < p.hessianMinor

def diagonalBinaryCriticalPoint : SmoothCriticalPoint :=
  { xNumerator := 1
    yNumerator := 1
    commonDenominator := 2
    directionX := 1
    directionY := 1
    hessianMinor := 2 }

theorem diagonalBinaryCriticalPoint_ready :
    diagonalBinaryCriticalPoint.ready := by
  norm_num [SmoothCriticalPoint.ready,
    SmoothCriticalPoint.positiveCoordinates,
    SmoothCriticalPoint.directionBalanced,
    diagonalBinaryCriticalPoint]

/-- Boolean readiness audit for a finite list of smooth critical points. -/
def smoothCriticalPointListReady
    (data : List SmoothCriticalPoint) : Bool :=
  data.all fun p =>
    0 < p.xNumerator &&
      0 < p.yNumerator &&
        0 < p.commonDenominator &&
          p.directionX * p.yNumerator == p.directionY * p.xNumerator &&
            0 < p.hessianMinor

theorem smoothCriticalPointList_readyWindow :
    smoothCriticalPointListReady
      [diagonalBinaryCriticalPoint,
       { xNumerator := 2, yNumerator := 3, commonDenominator := 5,
         directionX := 2, directionY := 3, hessianMinor := 7 }] =
      true := by
  unfold smoothCriticalPointListReady diagonalBinaryCriticalPoint
  native_decide

/-- A finite Cauchy torus window centered on a critical point radius. -/
structure CauchyTorusWindow where
  pointRadiusX : ℕ
  pointRadiusY : ℕ
  contourRadiusX : ℕ
  contourRadiusY : ℕ
  denominator : ℕ
deriving DecidableEq, Repr

def CauchyTorusWindow.centered (w : CauchyTorusWindow) : Prop :=
  w.pointRadiusX = w.contourRadiusX ∧ w.pointRadiusY = w.contourRadiusY

def CauchyTorusWindow.ready (w : CauchyTorusWindow) : Prop :=
  0 < w.denominator ∧ w.centered

def diagonalBinaryTorusWindow : CauchyTorusWindow :=
  { pointRadiusX := 1
    pointRadiusY := 1
    contourRadiusX := 1
    contourRadiusY := 1
    denominator := 2 }

theorem diagonalBinaryTorusWindow_ready :
    diagonalBinaryTorusWindow.ready := by
  norm_num [CauchyTorusWindow.ready, CauchyTorusWindow.centered,
    diagonalBinaryTorusWindow]

/-- A sample radius used to rule out smaller positive points in a finite audit. -/
structure TorusRadiusSample where
  radiusX : ℕ
  radiusY : ℕ
deriving DecidableEq, Repr

def notStrictlyInside
    (p : SmoothCriticalPoint) (s : TorusRadiusSample) : Bool :=
  ! (s.radiusX < p.xNumerator && s.radiusY < p.yNumerator)

/-- Finite minimality certificate: no sampled torus radius lies strictly inside. -/
def finiteMinimalityCheck
    (p : SmoothCriticalPoint) (samples : List TorusRadiusSample) : Bool :=
  samples.all (notStrictlyInside p)

theorem diagonalBinary_minimalityWindow :
    finiteMinimalityCheck diagonalBinaryCriticalPoint
      [{ radiusX := 1, radiusY := 1 },
       { radiusX := 1, radiusY := 2 },
       { radiusX := 2, radiusY := 1 }] = true := by
  unfold finiteMinimalityCheck notStrictlyInside diagonalBinaryCriticalPoint
  native_decide

/-- Diagonal coefficients of `1 / (1 - x - y)`. -/
def binaryDiagonalCoeff (n : ℕ) : ℕ :=
  (2 * n).choose n

example : binaryDiagonalCoeff 5 = 252 := by
  native_decide

theorem binaryDiagonalCoeff_samples :
    (List.range 8).map binaryDiagonalCoeff =
      [1, 2, 6, 20, 70, 252, 924, 3432] := by
  native_decide

/-- Finite ratio window for consecutive diagonal coefficients. -/
def binaryDiagonalRatioWindow
    (lower upper N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    lower * binaryDiagonalCoeff n ≤ binaryDiagonalCoeff (n + 1) &&
      binaryDiagonalCoeff (n + 1) ≤ upper * binaryDiagonalCoeff n

theorem binaryDiagonal_ratioWindow :
    binaryDiagonalRatioWindow 2 4 10 = true := by
  unfold binaryDiagonalRatioWindow binaryDiagonalCoeff
  native_decide

example : binaryDiagonalRatioWindow 2 4 5 = true := by
  unfold binaryDiagonalRatioWindow binaryDiagonalCoeff
  native_decide

structure MultivariateSmoothPointSchemasBudgetCertificate where
  smoothWindow : ℕ
  minimalityWindow : ℕ
  torusWindow : ℕ
  hessianWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultivariateSmoothPointSchemasBudgetCertificate.controlled
    (c : MultivariateSmoothPointSchemasBudgetCertificate) : Prop :=
  0 < c.smoothWindow ∧
    0 < c.hessianWindow ∧
      c.minimalityWindow ≤ c.smoothWindow + c.torusWindow + c.slack

def MultivariateSmoothPointSchemasBudgetCertificate.budgetControlled
    (c : MultivariateSmoothPointSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.smoothWindow + c.minimalityWindow + c.torusWindow +
      c.hessianWindow + c.slack

def MultivariateSmoothPointSchemasBudgetCertificate.Ready
    (c : MultivariateSmoothPointSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultivariateSmoothPointSchemasBudgetCertificate.size
    (c : MultivariateSmoothPointSchemasBudgetCertificate) : ℕ :=
  c.smoothWindow + c.minimalityWindow + c.torusWindow +
    c.hessianWindow + c.slack

theorem multivariateSmoothPointSchemas_budgetCertificate_le_size
    (c : MultivariateSmoothPointSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleMultivariateSmoothPointSchemasBudgetCertificate :
    MultivariateSmoothPointSchemasBudgetCertificate :=
  { smoothWindow := 4
    minimalityWindow := 5
    torusWindow := 6
    hessianWindow := 7
    certificateBudgetWindow := 23
    slack := 1 }

example : sampleMultivariateSmoothPointSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivariateSmoothPointSchemasBudgetCertificate.controlled,
      sampleMultivariateSmoothPointSchemasBudgetCertificate]
  · norm_num [MultivariateSmoothPointSchemasBudgetCertificate.budgetControlled,
      sampleMultivariateSmoothPointSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMultivariateSmoothPointSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivariateSmoothPointSchemasBudgetCertificate.controlled,
      sampleMultivariateSmoothPointSchemasBudgetCertificate]
  · norm_num [MultivariateSmoothPointSchemasBudgetCertificate.budgetControlled,
      sampleMultivariateSmoothPointSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultivariateSmoothPointSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMultivariateSmoothPointSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MultivariateSmoothPointSchemasBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultivariateSmoothPointSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleMultivariateSmoothPointSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.MultivariateSmoothPointSchemas
