import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix C: convergence in law.

Finite test-function and metric windows for weak convergence certificates.
-/

namespace AnalyticCombinatorics.AppC.ConvergenceInLaw

/-- Bounded test-function discrepancy over a finite support. -/
def testFunctionDiscrepancy
    (massA massB test : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun total k => total + (massA k - massB k) * test k) 0

theorem testFunctionDiscrepancy_self
    (mass test : ℕ → ℚ) (N : ℕ) :
    testFunctionDiscrepancy mass mass test N = 0 := by
  simp [testFunctionDiscrepancy]

/-- Finite weak-convergence audit for a list of sampled test functions. -/
def testDiscrepancyZeroCheck
    (massA massB : ℕ → ℚ) (tests : List (ℕ → ℚ)) (N : ℕ) : Bool :=
  tests.all fun test => testFunctionDiscrepancy massA massB test N = 0

theorem testDiscrepancyZeroCheck_self
    (mass : ℕ → ℚ) (tests : List (ℕ → ℚ)) (N : ℕ) :
    testDiscrepancyZeroCheck mass mass tests N = true := by
  simp [testDiscrepancyZeroCheck, testFunctionDiscrepancy_self]

def pointMassZero : ℕ → ℚ
  | 0 => 1
  | _ => 0

def constantTest (_ : ℕ) : ℚ :=
  1

def identityTest (n : ℕ) : ℚ :=
  n

theorem identicalMeasures_convergenceWindow :
    testDiscrepancyZeroCheck pointMassZero pointMassZero
      [constantTest, identityTest] 4 = true := by
  unfold testDiscrepancyZeroCheck testFunctionDiscrepancy
    pointMassZero constantTest identityTest
  native_decide

structure ConvergenceInLawWindow where
  testFunctionCount : ℕ
  metricWindow : ℕ
  tightnessWindow : ℕ
  convergenceSlack : ℕ
deriving DecidableEq, Repr

def convergenceInLawReady (w : ConvergenceInLawWindow) : Prop :=
  0 < w.testFunctionCount ∧
    w.metricWindow ≤ w.testFunctionCount + w.tightnessWindow + w.convergenceSlack

def convergenceInLawBudget (w : ConvergenceInLawWindow) : ℕ :=
  w.testFunctionCount + w.metricWindow + w.tightnessWindow + w.convergenceSlack

theorem metricWindow_le_budget (w : ConvergenceInLawWindow) :
    w.metricWindow ≤ convergenceInLawBudget w := by
  unfold convergenceInLawBudget
  omega

def sampleConvergenceInLawWindow : ConvergenceInLawWindow :=
  { testFunctionCount := 5
    metricWindow := 7
    tightnessWindow := 2
    convergenceSlack := 1 }

example : convergenceInLawReady sampleConvergenceInLawWindow := by
  norm_num [convergenceInLawReady, sampleConvergenceInLawWindow]

structure ConvergenceInLawBudgetCertificate where
  testWindow : ℕ
  metricWindow : ℕ
  tightnessWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConvergenceInLawBudgetCertificate.controlled
    (c : ConvergenceInLawBudgetCertificate) : Prop :=
  0 < c.testWindow ∧
    c.metricWindow ≤ c.testWindow + c.tightnessWindow + c.slack

def ConvergenceInLawBudgetCertificate.budgetControlled
    (c : ConvergenceInLawBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.testWindow + c.metricWindow + c.tightnessWindow + c.slack

def ConvergenceInLawBudgetCertificate.Ready
    (c : ConvergenceInLawBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ConvergenceInLawBudgetCertificate.size
    (c : ConvergenceInLawBudgetCertificate) : ℕ :=
  c.testWindow + c.metricWindow + c.tightnessWindow + c.slack

theorem convergenceInLaw_budgetCertificate_le_size
    (c : ConvergenceInLawBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleConvergenceInLawBudgetCertificate :
    ConvergenceInLawBudgetCertificate :=
  { testWindow := 5
    metricWindow := 7
    tightnessWindow := 2
    certificateBudgetWindow := 15
    slack := 1 }

example : sampleConvergenceInLawBudgetCertificate.Ready := by
  constructor
  · norm_num [ConvergenceInLawBudgetCertificate.controlled,
      sampleConvergenceInLawBudgetCertificate]
  · norm_num [ConvergenceInLawBudgetCertificate.budgetControlled,
      sampleConvergenceInLawBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleConvergenceInLawBudgetCertificate.Ready := by
  constructor
  · norm_num [ConvergenceInLawBudgetCertificate.controlled,
      sampleConvergenceInLawBudgetCertificate]
  · norm_num [ConvergenceInLawBudgetCertificate.budgetControlled,
      sampleConvergenceInLawBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleConvergenceInLawBudgetCertificate.certificateBudgetWindow ≤
      sampleConvergenceInLawBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ConvergenceInLawBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleConvergenceInLawBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleConvergenceInLawBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ConvergenceInLaw
