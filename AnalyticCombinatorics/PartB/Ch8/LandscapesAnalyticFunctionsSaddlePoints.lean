import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Landscapes of analytic functions and saddle points.
-/

namespace AnalyticCombinatorics.PartB.Ch8.LandscapesAnalyticFunctionsSaddlePoints

/-- Discrete landscape height for a quadratic analytic phase. -/
def phaseLandscape (center n : ℕ) : ℤ :=
  ((n : ℤ) - (center : ℤ)) ^ 2

/-- Finite check that a saddle is the sampled valley of the landscape. -/
def sampledValleyCheck (center N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => phaseLandscape center center ≤ phaseLandscape center n

/-- Finite contour-height envelope around a saddle. -/
def contourEnvelopeCheck (center height N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => phaseLandscape center n ≤ (height : ℤ)

def SaddleLandscapeWindow (center height N : ℕ) : Prop :=
  sampledValleyCheck center N = true ∧ contourEnvelopeCheck center height N = true

theorem quadraticLandscape_window :
    SaddleLandscapeWindow 5 49 12 := by
  unfold SaddleLandscapeWindow sampledValleyCheck contourEnvelopeCheck
    phaseLandscape
  native_decide

/-- Finite symmetry audit for equal-height points around a quadratic saddle. -/
def landscapeSymmetryCheck (center width : ℕ) : Bool :=
  (List.range (width + 1)).all fun d =>
    phaseLandscape center (center + d) =
      phaseLandscape center (center - d)

theorem quadraticLandscape_symmetryWindow :
    landscapeSymmetryCheck 7 7 = true := by
  unfold landscapeSymmetryCheck phaseLandscape
  native_decide

structure LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate where
  analyticWindow : ℕ
  contourWindow : ℕ
  saddleWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate.controlled
    (c : LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate) : Prop :=
  0 < c.analyticWindow ∧
    c.saddleWindow ≤ c.analyticWindow + c.contourWindow + c.slack

def LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate.budgetControlled
    (c : LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.analyticWindow + c.contourWindow + c.saddleWindow + c.slack

def LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate.Ready
    (c : LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate.size
    (c : LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate) : ℕ :=
  c.analyticWindow + c.contourWindow + c.saddleWindow + c.slack

theorem landscapesAnalyticFunctionsSaddlePoints_budgetCertificate_le_size
    (c : LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleLandscapesAnalyticFunctionsSaddlePointsBudgetCertificate :
    LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate :=
  { analyticWindow := 5
    contourWindow := 4
    saddleWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

example :
    sampleLandscapesAnalyticFunctionsSaddlePointsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate.controlled,
        sampleLandscapesAnalyticFunctionsSaddlePointsBudgetCertificate]
  · norm_num
      [LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate.budgetControlled,
        sampleLandscapesAnalyticFunctionsSaddlePointsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleLandscapesAnalyticFunctionsSaddlePointsBudgetCertificate.Ready := by
  constructor
  · norm_num [LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate.controlled,
      sampleLandscapesAnalyticFunctionsSaddlePointsBudgetCertificate]
  · norm_num [LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate.budgetControlled,
      sampleLandscapesAnalyticFunctionsSaddlePointsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLandscapesAnalyticFunctionsSaddlePointsBudgetCertificate.certificateBudgetWindow ≤
      sampleLandscapesAnalyticFunctionsSaddlePointsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List LandscapesAnalyticFunctionsSaddlePointsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLandscapesAnalyticFunctionsSaddlePointsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleLandscapesAnalyticFunctionsSaddlePointsBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleLandscapesAnalyticFunctionsSaddlePointsBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch8.LandscapesAnalyticFunctionsSaddlePoints
