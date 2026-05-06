import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Hankel contours

Finite keyhole-contour descriptors and residue-budget certificates for Hankel
contour transfer arguments.
-/

namespace AnalyticCombinatorics.Asymptotics.HankelContours

/-- A finite keyhole contour is modeled by two rays and a small circle. -/
structure HankelContourData where
  outerRadius : ℕ
  innerRadius : ℕ
  raySeparation : ℕ
  circleSegments : ℕ
deriving DecidableEq, Repr

def HankelContourData.geometryControlled (d : HankelContourData) : Prop :=
  0 < d.innerRadius ∧
    d.innerRadius ≤ d.outerRadius ∧
      0 < d.raySeparation ∧ 0 < d.circleSegments

def sampleHankelContourData : HankelContourData :=
  { outerRadius := 12
    innerRadius := 2
    raySeparation := 3
    circleSegments := 8 }

example : sampleHankelContourData.geometryControlled := by
  norm_num [HankelContourData.geometryControlled, sampleHankelContourData]

/-- Combinatorial count for the number of contour pieces. -/
def hankelContourPieceCount (d : HankelContourData) : ℕ :=
  2 * d.raySeparation + d.circleSegments

theorem hankelContourPieceCount_sample :
    hankelContourPieceCount sampleHankelContourData = 14 := by
  native_decide

/-- Simple cleared-denominator jump factor across the cut. -/
def hankelJumpProxy (upper lower : ℚ) : ℚ :=
  upper - lower

theorem hankelJumpProxy_samples :
    hankelJumpProxy 3 1 = 2 ∧
      hankelJumpProxy (1 / 2) (-1 / 2) = 1 := by
  native_decide

/-- Boolean audit for finite Hankel contour data. -/
def hankelContourDataListReady (data : List HankelContourData) : Bool :=
  data.all fun d =>
    0 < d.innerRadius &&
      d.innerRadius ≤ d.outerRadius &&
        0 < d.raySeparation && 0 < d.circleSegments

theorem hankelContourDataList_readyWindow :
    hankelContourDataListReady
      [sampleHankelContourData,
       { outerRadius := 5, innerRadius := 1, raySeparation := 2,
         circleSegments := 4 }] = true := by
  unfold hankelContourDataListReady sampleHankelContourData
  native_decide

/-- A finite window for Hankel contour estimates. -/
structure HankelContourWindow where
  contourWindow : ℕ
  indentationWindow : ℕ
  jumpWindow : ℕ
  remainderWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HankelContourWindow.controlled (w : HankelContourWindow) : Prop :=
  0 < w.contourWindow ∧
    0 < w.indentationWindow ∧
      w.remainderWindow ≤ w.contourWindow + w.jumpWindow + w.slack

def HankelContourWindow.ready (w : HankelContourWindow) : Prop :=
  w.controlled

def sampleHankelContourWindow : HankelContourWindow :=
  { contourWindow := 6
    indentationWindow := 2
    jumpWindow := 5
    remainderWindow := 12
    slack := 1 }

example : sampleHankelContourWindow.ready := by
  norm_num [HankelContourWindow.ready, HankelContourWindow.controlled,
    sampleHankelContourWindow]

def hankelContourWindowListReady (data : List HankelContourWindow) : Bool :=
  data.all fun w =>
    0 < w.contourWindow &&
      0 < w.indentationWindow &&
        w.remainderWindow ≤ w.contourWindow + w.jumpWindow + w.slack

theorem hankelContourWindowList_readyWindow :
    hankelContourWindowListReady
      [sampleHankelContourWindow,
       { contourWindow := 4, indentationWindow := 1, jumpWindow := 3,
         remainderWindow := 7, slack := 0 }] = true := by
  unfold hankelContourWindowListReady sampleHankelContourWindow
  native_decide

/-- Budget certificate for a finite Hankel-contour proof. -/
structure HankelContourBudgetCertificate where
  contourWindow : ℕ
  indentationWindow : ℕ
  jumpWindow : ℕ
  remainderWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HankelContourBudgetCertificate.controlled
    (c : HankelContourBudgetCertificate) : Prop :=
  0 < c.contourWindow ∧
    0 < c.indentationWindow ∧
      c.remainderWindow ≤ c.contourWindow + c.jumpWindow + c.slack

def HankelContourBudgetCertificate.budgetControlled
    (c : HankelContourBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.contourWindow + c.indentationWindow + c.jumpWindow +
      c.remainderWindow + c.slack

def HankelContourBudgetCertificate.Ready
    (c : HankelContourBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HankelContourBudgetCertificate.size
    (c : HankelContourBudgetCertificate) : ℕ :=
  c.contourWindow + c.indentationWindow + c.jumpWindow +
    c.remainderWindow + c.slack

theorem hankelContour_budgetCertificate_le_size
    (c : HankelContourBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleHankelContourBudgetCertificate :
    HankelContourBudgetCertificate :=
  { contourWindow := 6
    indentationWindow := 2
    jumpWindow := 5
    remainderWindow := 12
    certificateBudgetWindow := 26
    slack := 1 }

example : sampleHankelContourBudgetCertificate.Ready := by
  constructor
  · norm_num [HankelContourBudgetCertificate.controlled,
      sampleHankelContourBudgetCertificate]
  · norm_num [HankelContourBudgetCertificate.budgetControlled,
      sampleHankelContourBudgetCertificate]

/-- Finite executable readiness audit for Hankel-contour budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleHankelContourBudgetCertificate.Ready := by
  constructor
  · norm_num [HankelContourBudgetCertificate.controlled,
      sampleHankelContourBudgetCertificate]
  · norm_num [HankelContourBudgetCertificate.budgetControlled,
      sampleHankelContourBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHankelContourBudgetCertificate.certificateBudgetWindow ≤
      sampleHankelContourBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List HankelContourBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleHankelContourBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleHankelContourBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.HankelContours
