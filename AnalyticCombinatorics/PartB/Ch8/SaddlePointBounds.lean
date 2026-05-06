import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Saddle-point bounds.
-/

namespace AnalyticCombinatorics.PartB.Ch8.SaddlePointBounds

/-- Coefficient bound of a geometric majorant. -/
def geometricMajorantCoeff (radius n : ℕ) : ℕ :=
  radius ^ n

/-- Finite Cauchy/saddle bound audit against a majorant sequence. -/
def saddleBoundCheck (coeff majorant : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => coeff n ≤ majorant n

def binomialRowCoeff (m n : ℕ) : ℕ :=
  m.choose n

def SaddleBoundWindow (m radius N : ℕ) : Prop :=
  saddleBoundCheck (binomialRowCoeff m) (geometricMajorantCoeff radius) N = true

theorem binomialRow_saddleBoundWindow :
    SaddleBoundWindow 8 8 8 := by
  unfold SaddleBoundWindow saddleBoundCheck binomialRowCoeff
    geometricMajorantCoeff
  native_decide

/-- Discrete distance from a saddle index. -/
def saddleDistance (center n : ℕ) : ℕ :=
  if n ≤ center then center - n else n - center

/-- Finite audit that quadratic tails dominate a sampled threshold. -/
def quadraticTailCheck (center width N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    width ≤ saddleDistance center n →
      width * width ≤ saddleDistance center n * saddleDistance center n

theorem quadraticTail_saddleBoundWindow :
    quadraticTailCheck 5 3 12 = true := by
  unfold quadraticTailCheck saddleDistance
  native_decide

example : geometricMajorantCoeff 3 4 = 81 := by
  unfold geometricMajorantCoeff
  native_decide

example : saddleDistance 5 2 = 3 := by
  unfold saddleDistance
  native_decide

structure SaddlePointBoundsBudgetCertificate where
  radiusWindow : ℕ
  majorantWindow : ℕ
  boundWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddlePointBoundsBudgetCertificate.controlled
    (c : SaddlePointBoundsBudgetCertificate) : Prop :=
  0 < c.radiusWindow ∧
    c.boundWindow ≤ c.radiusWindow + c.majorantWindow + c.slack

def SaddlePointBoundsBudgetCertificate.budgetControlled
    (c : SaddlePointBoundsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.radiusWindow + c.majorantWindow + c.boundWindow + c.slack

def SaddlePointBoundsBudgetCertificate.Ready
    (c : SaddlePointBoundsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SaddlePointBoundsBudgetCertificate.size
    (c : SaddlePointBoundsBudgetCertificate) : ℕ :=
  c.radiusWindow + c.majorantWindow + c.boundWindow + c.slack

theorem saddlePointBounds_budgetCertificate_le_size
    (c : SaddlePointBoundsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSaddlePointBoundsBudgetCertificate :
    SaddlePointBoundsBudgetCertificate :=
  { radiusWindow := 5
    majorantWindow := 4
    boundWindow := 8
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSaddlePointBoundsBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddlePointBoundsBudgetCertificate.controlled,
      sampleSaddlePointBoundsBudgetCertificate]
  · norm_num [SaddlePointBoundsBudgetCertificate.budgetControlled,
      sampleSaddlePointBoundsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddlePointBoundsBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddlePointBoundsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSaddlePointBoundsBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddlePointBoundsBudgetCertificate.controlled,
      sampleSaddlePointBoundsBudgetCertificate]
  · norm_num [SaddlePointBoundsBudgetCertificate.budgetControlled,
      sampleSaddlePointBoundsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SaddlePointBoundsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSaddlePointBoundsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSaddlePointBoundsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.SaddlePointBounds
