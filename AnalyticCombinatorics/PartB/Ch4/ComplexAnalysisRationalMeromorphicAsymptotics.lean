import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Complex analysis, rational and meromorphic asymptotics

Chapter-level finite roadmap certificates linking analytic, rational, and
meromorphic windows.
-/

namespace AnalyticCombinatorics.PartB.Ch4.ComplexAnalysisRationalMeromorphicAsymptotics

/-- Coefficients of a simple rational pole with integer inverse radius. -/
def simplePoleCoeff (radiusInv n : ℕ) : ℕ :=
  radiusInv ^ n

theorem simplePoleCoeff_zero (radiusInv : ℕ) :
    simplePoleCoeff radiusInv 0 = 1 := by
  simp [simplePoleCoeff]

theorem simplePoleCoeff_succ (radiusInv n : ℕ) :
    simplePoleCoeff radiusInv (n + 1) =
      radiusInv * simplePoleCoeff radiusInv n := by
  simp [simplePoleCoeff, pow_succ, Nat.mul_comm]

/-- Coefficients of a double pole at the same radius. -/
def doublePoleCoeff (radiusInv n : ℕ) : ℕ :=
  (n + 1) * radiusInv ^ n

theorem doublePoleCoeff_zero (radiusInv : ℕ) :
    doublePoleCoeff radiusInv 0 = 1 := by
  simp [doublePoleCoeff]

def rationalDominanceCheck (coeff : ℕ → ℕ) (radiusInv bound N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => coeff n ≤ bound * simplePoleCoeff radiusInv n

theorem rationalDominance_geometric :
    rationalDominanceCheck (fun n => 2 ^ n) 2 1 12 = true := by
  unfold rationalDominanceCheck simplePoleCoeff
  native_decide

structure ChapterFourRoadmapWindow where
  analyticWindow : ℕ
  rationalWindow : ℕ
  meromorphicWindow : ℕ
  localizationWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ChapterFourRoadmapWindow.ready
    (w : ChapterFourRoadmapWindow) : Prop :=
  0 < w.analyticWindow ∧
    w.rationalWindow ≤ w.analyticWindow + w.slack ∧
      w.meromorphicWindow ≤ w.rationalWindow + w.localizationWindow + w.slack

def sampleChapterFourRoadmapWindow : ChapterFourRoadmapWindow :=
  { analyticWindow := 5
    rationalWindow := 6
    meromorphicWindow := 10
    localizationWindow := 4
    slack := 1 }

example : sampleChapterFourRoadmapWindow.ready := by
  norm_num [ChapterFourRoadmapWindow.ready, sampleChapterFourRoadmapWindow]

def chapterFourRoadmapWindowListReady
    (data : List ChapterFourRoadmapWindow) : Bool :=
  data.all fun w =>
    0 < w.analyticWindow &&
      w.rationalWindow ≤ w.analyticWindow + w.slack &&
        w.meromorphicWindow ≤ w.rationalWindow + w.localizationWindow + w.slack

theorem chapterFourRoadmapWindowList_readyWindow :
    chapterFourRoadmapWindowListReady
      [sampleChapterFourRoadmapWindow,
       { analyticWindow := 3, rationalWindow := 3,
         meromorphicWindow := 5, localizationWindow := 2, slack := 0 }] =
        true := by
  unfold chapterFourRoadmapWindowListReady sampleChapterFourRoadmapWindow
  native_decide

structure ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate where
  analyticWindow : ℕ
  rationalWindow : ℕ
  meromorphicWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate.controlled
    (c : ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate) :
    Prop :=
  0 < c.analyticWindow ∧
    c.rationalWindow ≤ c.analyticWindow + c.slack ∧
      c.meromorphicWindow ≤ c.analyticWindow + c.rationalWindow + c.slack

def ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate.budgetControlled
    (c : ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate) :
    Prop :=
  c.certificateBudgetWindow ≤
    c.analyticWindow + c.rationalWindow + c.meromorphicWindow + c.slack

def ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate.Ready
    (c : ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate) :
    Prop :=
  c.controlled ∧ c.budgetControlled

def ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate.size
    (c : ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate) :
    ℕ :=
  c.analyticWindow + c.rationalWindow + c.meromorphicWindow + c.slack

theorem complexAnalysisRationalMeromorphicAsymptotics_budgetCertificate_le_size
    (c : ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate :
    ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate :=
  { analyticWindow := 5
    rationalWindow := 6
    meromorphicWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example :
    sampleComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate.controlled,
        sampleComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate]
  · norm_num
      [ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate.budgetControlled,
        sampleComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate.controlled,
      sampleComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate]
  · norm_num [ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate.budgetControlled,
      sampleComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data :
      List ComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate] =
        true := by
  unfold budgetCertificateListReady
    sampleComplexAnalysisRationalMeromorphicAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.ComplexAnalysisRationalMeromorphicAsymptotics
