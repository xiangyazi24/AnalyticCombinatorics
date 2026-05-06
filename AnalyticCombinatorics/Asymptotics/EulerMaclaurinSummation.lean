import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Euler-Maclaurin summation

Finite summation, endpoint-correction, and remainder-window bookkeeping for
Euler-Maclaurin summation.
-/

namespace AnalyticCombinatorics.Asymptotics.EulerMaclaurinSummation

open Finset

/-- Sum of a finite sequence over `0, ..., n - 1`. -/
def prefixSumRat (f : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ range n, f k

def affineRat (slope intercept : ℚ) (n : ℕ) : ℚ :=
  slope * (n : ℚ) + intercept

def squareRat (n : ℕ) : ℚ :=
  (n : ℚ) ^ 2

theorem prefixSumRat_affine_samples :
    prefixSumRat (affineRat 1 0) 5 = 10 ∧
      prefixSumRat (affineRat 2 1) 4 = 16 ∧
        prefixSumRat squareRat 5 = 30 := by
  native_decide

/-- Trapezoidal endpoint correction over the integer interval `[0, n]`. -/
def endpointCorrection (f : ℕ → ℚ) (n : ℕ) : ℚ :=
  (f 0 + f n) / 2

theorem endpointCorrection_samples :
    endpointCorrection (affineRat 1 0) 10 = 5 ∧
      endpointCorrection squareRat 4 = 8 := by
  native_decide

/-- Integral estimate for affine data on `[0, n]`. -/
def affineIntegralProxy (slope intercept : ℚ) (n : ℕ) : ℚ :=
  slope * (n : ℚ) ^ 2 / 2 + intercept * (n : ℚ)

/-- First Euler-Maclaurin estimate for sums over `0, ..., n`. -/
def firstEulerMaclaurinProxy (slope intercept : ℚ) (n : ℕ) : ℚ :=
  affineIntegralProxy slope intercept n +
    endpointCorrection (affineRat slope intercept) n

theorem firstEulerMaclaurinProxy_affine_samples :
    firstEulerMaclaurinProxy 1 0 4 = 10 ∧
      firstEulerMaclaurinProxy 2 1 3 = 16 := by
  native_decide

/-- Bernoulli correction coefficient table for the first even corrections. -/
def bernoulliEvenCorrection : Fin 5 → ℚ :=
  ![1 / 6, -1 / 30, 1 / 42, -1 / 30, 5 / 66]

theorem bernoulliEvenCorrection_samples :
    bernoulliEvenCorrection 0 = 1 / 6 ∧
      bernoulliEvenCorrection 1 = -1 / 30 ∧
        bernoulliEvenCorrection 3 = -1 / 30 := by
  native_decide

/-- Window data for a finite Euler-Maclaurin summation certificate. -/
structure EulerMaclaurinSummationWindow where
  summationWindow : ℕ
  endpointWindow : ℕ
  derivativeWindow : ℕ
  remainderWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EulerMaclaurinSummationWindow.controlled
    (w : EulerMaclaurinSummationWindow) : Prop :=
  0 < w.summationWindow ∧
    w.endpointWindow ≤ w.summationWindow + w.slack ∧
      w.remainderWindow ≤ w.derivativeWindow + w.endpointWindow + w.slack

def EulerMaclaurinSummationWindow.ready
    (w : EulerMaclaurinSummationWindow) : Prop :=
  w.controlled

def sampleEulerMaclaurinSummationWindow :
    EulerMaclaurinSummationWindow :=
  { summationWindow := 8
    endpointWindow := 5
    derivativeWindow := 4
    remainderWindow := 10
    slack := 1 }

example : sampleEulerMaclaurinSummationWindow.ready := by
  norm_num [EulerMaclaurinSummationWindow.ready,
    EulerMaclaurinSummationWindow.controlled,
    sampleEulerMaclaurinSummationWindow]

/-- Boolean audit for finite Euler-Maclaurin summation windows. -/
def eulerMaclaurinSummationWindowListReady
    (data : List EulerMaclaurinSummationWindow) : Bool :=
  data.all fun w =>
    0 < w.summationWindow &&
      w.endpointWindow ≤ w.summationWindow + w.slack &&
        w.remainderWindow ≤ w.derivativeWindow + w.endpointWindow + w.slack

theorem eulerMaclaurinSummationWindowList_readyWindow :
    eulerMaclaurinSummationWindowListReady
      [sampleEulerMaclaurinSummationWindow,
       { summationWindow := 4, endpointWindow := 4, derivativeWindow := 3,
         remainderWindow := 7, slack := 0 }] = true := by
  unfold eulerMaclaurinSummationWindowListReady
    sampleEulerMaclaurinSummationWindow
  native_decide

/-- Budget certificate for a finite Euler-Maclaurin summation proof. -/
structure EulerMaclaurinSummationBudgetCertificate where
  summationWindow : ℕ
  endpointWindow : ℕ
  derivativeWindow : ℕ
  remainderWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EulerMaclaurinSummationBudgetCertificate.controlled
    (c : EulerMaclaurinSummationBudgetCertificate) : Prop :=
  0 < c.summationWindow ∧
    c.endpointWindow ≤ c.summationWindow + c.slack ∧
      c.remainderWindow ≤ c.derivativeWindow + c.endpointWindow + c.slack

def EulerMaclaurinSummationBudgetCertificate.budgetControlled
    (c : EulerMaclaurinSummationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.summationWindow + c.endpointWindow + c.derivativeWindow +
      c.remainderWindow + c.slack

def EulerMaclaurinSummationBudgetCertificate.Ready
    (c : EulerMaclaurinSummationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EulerMaclaurinSummationBudgetCertificate.size
    (c : EulerMaclaurinSummationBudgetCertificate) : ℕ :=
  c.summationWindow + c.endpointWindow + c.derivativeWindow +
    c.remainderWindow + c.slack

theorem eulerMaclaurinSummation_budgetCertificate_le_size
    (c : EulerMaclaurinSummationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleEulerMaclaurinSummationBudgetCertificate :
    EulerMaclaurinSummationBudgetCertificate :=
  { summationWindow := 8
    endpointWindow := 5
    derivativeWindow := 4
    remainderWindow := 10
    certificateBudgetWindow := 28
    slack := 1 }

example : sampleEulerMaclaurinSummationBudgetCertificate.Ready := by
  constructor
  · norm_num [EulerMaclaurinSummationBudgetCertificate.controlled,
      sampleEulerMaclaurinSummationBudgetCertificate]
  · norm_num [EulerMaclaurinSummationBudgetCertificate.budgetControlled,
      sampleEulerMaclaurinSummationBudgetCertificate]

/-- Finite executable readiness audit for summation budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleEulerMaclaurinSummationBudgetCertificate.Ready := by
  constructor
  · norm_num [EulerMaclaurinSummationBudgetCertificate.controlled,
      sampleEulerMaclaurinSummationBudgetCertificate]
  · norm_num [EulerMaclaurinSummationBudgetCertificate.budgetControlled,
      sampleEulerMaclaurinSummationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleEulerMaclaurinSummationBudgetCertificate.certificateBudgetWindow ≤
      sampleEulerMaclaurinSummationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List EulerMaclaurinSummationBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEulerMaclaurinSummationBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleEulerMaclaurinSummationBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.EulerMaclaurinSummation
