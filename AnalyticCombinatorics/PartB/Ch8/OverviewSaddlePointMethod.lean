import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Overview of the saddle-point method.
-/

namespace AnalyticCombinatorics.PartB.Ch8.OverviewSaddlePointMethod

/-- Discrete quadratic phase centered at a saddle. -/
def quadraticPhase (center n : ℕ) : ℤ :=
  ((n : ℤ) - (center : ℤ)) ^ 2

/-- Finite audit that the selected saddle minimizes the phase. -/
def saddleMinimizesCheck (phase : ℕ → ℤ) (center N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => phase center ≤ phase n

/-- Finite Gaussian envelope around the saddle. -/
def gaussianEnvelopeCheck (center radius N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    quadraticPhase center n ≤ (radius + center) ^ 2

def SaddleOverviewWindow (center radius N : ℕ) : Prop :=
  saddleMinimizesCheck (quadraticPhase center) center N = true ∧
    gaussianEnvelopeCheck center radius N = true

theorem quadraticSaddle_overviewWindow :
    SaddleOverviewWindow 5 8 12 := by
  unfold SaddleOverviewWindow saddleMinimizesCheck gaussianEnvelopeCheck
    quadraticPhase
  native_decide

/-- Finite symmetry audit around a quadratic saddle. -/
def saddleSymmetryCheck (center width : ℕ) : Bool :=
  (List.range (width + 1)).all fun d =>
    quadraticPhase center (center + d) = quadraticPhase center (center - d)

theorem quadraticSaddle_symmetryWindow :
    saddleSymmetryCheck 6 6 = true := by
  unfold saddleSymmetryCheck quadraticPhase
  native_decide

structure OverviewSaddlePointMethodBudgetCertificate where
  setupWindow : ℕ
  saddleWindow : ℕ
  gaussianWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def OverviewSaddlePointMethodBudgetCertificate.controlled
    (c : OverviewSaddlePointMethodBudgetCertificate) : Prop :=
  0 < c.setupWindow ∧
    c.gaussianWindow ≤ c.setupWindow + c.saddleWindow + c.slack

def OverviewSaddlePointMethodBudgetCertificate.budgetControlled
    (c : OverviewSaddlePointMethodBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.setupWindow + c.saddleWindow + c.gaussianWindow + c.slack

def OverviewSaddlePointMethodBudgetCertificate.Ready
    (c : OverviewSaddlePointMethodBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def OverviewSaddlePointMethodBudgetCertificate.size
    (c : OverviewSaddlePointMethodBudgetCertificate) : ℕ :=
  c.setupWindow + c.saddleWindow + c.gaussianWindow + c.slack

theorem overviewSaddlePointMethod_budgetCertificate_le_size
    (c : OverviewSaddlePointMethodBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleOverviewSaddlePointMethodBudgetCertificate :
    OverviewSaddlePointMethodBudgetCertificate :=
  { setupWindow := 4
    saddleWindow := 5
    gaussianWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleOverviewSaddlePointMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [OverviewSaddlePointMethodBudgetCertificate.controlled,
      sampleOverviewSaddlePointMethodBudgetCertificate]
  · norm_num [OverviewSaddlePointMethodBudgetCertificate.budgetControlled,
      sampleOverviewSaddlePointMethodBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleOverviewSaddlePointMethodBudgetCertificate.certificateBudgetWindow ≤
      sampleOverviewSaddlePointMethodBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleOverviewSaddlePointMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [OverviewSaddlePointMethodBudgetCertificate.controlled,
      sampleOverviewSaddlePointMethodBudgetCertificate]
  · norm_num [OverviewSaddlePointMethodBudgetCertificate.budgetControlled,
      sampleOverviewSaddlePointMethodBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List OverviewSaddlePointMethodBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleOverviewSaddlePointMethodBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleOverviewSaddlePointMethodBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleOverviewSaddlePointMethodBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch8.OverviewSaddlePointMethod
