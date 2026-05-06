import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Poisson-Charlier expansion.

Finite Charlier-polynomial correction and depoissonization expansion windows.
-/

namespace AnalyticCombinatorics.Asymptotics.PoissonCharlierExpansion

/-- Falling factorial, used in finite Charlier polynomial coefficients. -/
def fallingFactorial : ℕ → ℕ → ℕ
  | _n, 0 => 1
  | 0, _k + 1 => 0
  | n + 1, k + 1 => (n + 1) * fallingFactorial n k

theorem fallingFactorial_samples :
    (List.range 6).map (fallingFactorial 5) = [1, 5, 20, 60, 120, 120] := by
  native_decide

/-- First Charlier correction polynomial in a finite centered variable. -/
def charlierOne (n lambda : ℕ) : ℤ :=
  (n : ℤ) - (lambda : ℤ)

/-- Second Charlier correction polynomial in finite integer form. -/
def charlierTwo (n lambda : ℕ) : ℤ :=
  ((n : ℤ) - (lambda : ℤ)) ^ 2 - (n : ℤ)

theorem charlier_central_samples :
    charlierOne 5 5 = 0 ∧
      charlierTwo 5 5 = -5 ∧
        charlierOne 7 5 = 2 ∧
          charlierTwo 7 5 = -3 := by
  native_decide

example : charlierOne 9 5 = 4 := by
  native_decide

example : charlierTwo 9 5 = 7 := by
  native_decide

/-- A finite Poisson-Charlier expansion truncation descriptor. -/
structure PoissonCharlierExpansionWindow where
  poissonWindow : ℕ
  charlierOrder : ℕ
  coefficientWindow : ℕ
  remainderWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonCharlierExpansionWindow.orderReady
    (w : PoissonCharlierExpansionWindow) : Prop :=
  0 < w.poissonWindow ∧ 0 < w.charlierOrder

def PoissonCharlierExpansionWindow.remainderControlled
    (w : PoissonCharlierExpansionWindow) : Prop :=
  w.remainderWindow ≤ w.poissonWindow + w.coefficientWindow + w.slack

def PoissonCharlierExpansionWindow.ready
    (w : PoissonCharlierExpansionWindow) : Prop :=
  w.orderReady ∧ w.remainderControlled

def samplePoissonCharlierExpansionWindow :
    PoissonCharlierExpansionWindow :=
  { poissonWindow := 8
    charlierOrder := 2
    coefficientWindow := 5
    remainderWindow := 14
    slack := 1 }

theorem samplePoissonCharlierExpansionWindow_ready :
    samplePoissonCharlierExpansionWindow.ready := by
  norm_num [PoissonCharlierExpansionWindow.ready,
    PoissonCharlierExpansionWindow.orderReady,
    PoissonCharlierExpansionWindow.remainderControlled,
    samplePoissonCharlierExpansionWindow]

/-- Boolean audit for finite expansion windows. -/
def poissonCharlierExpansionWindowListReady
    (data : List PoissonCharlierExpansionWindow) : Bool :=
  data.all fun w =>
    0 < w.poissonWindow &&
      0 < w.charlierOrder &&
        w.remainderWindow ≤ w.poissonWindow + w.coefficientWindow + w.slack

theorem poissonCharlierExpansionWindowList_readyWindow :
    poissonCharlierExpansionWindowListReady
      [samplePoissonCharlierExpansionWindow,
       { poissonWindow := 6, charlierOrder := 3, coefficientWindow := 4,
         remainderWindow := 10, slack := 0 }] = true := by
  unfold poissonCharlierExpansionWindowListReady
    samplePoissonCharlierExpansionWindow
  native_decide

/-- Finite expansion value from the first two Charlier corrections. -/
def poissonCharlierExpansionProxy
    (base first second n lambda : ℤ) : ℤ :=
  base + first * (n - lambda) + second * ((n - lambda) ^ 2 - n)

theorem poissonCharlierExpansionProxy_samples :
    poissonCharlierExpansionProxy 10 3 1 5 5 = 5 ∧
      poissonCharlierExpansionProxy 10 3 1 7 5 = 13 := by
  native_decide

structure PoissonCharlierExpansionBudgetCertificate where
  poissonWindow : ℕ
  charlierWindow : ℕ
  coefficientWindow : ℕ
  remainderWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonCharlierExpansionBudgetCertificate.controlled
    (c : PoissonCharlierExpansionBudgetCertificate) : Prop :=
  0 < c.poissonWindow ∧
    0 < c.charlierWindow ∧
      c.remainderWindow ≤ c.poissonWindow + c.coefficientWindow + c.slack

def PoissonCharlierExpansionBudgetCertificate.budgetControlled
    (c : PoissonCharlierExpansionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.poissonWindow + c.charlierWindow + c.coefficientWindow +
      c.remainderWindow + c.slack

def PoissonCharlierExpansionBudgetCertificate.Ready
    (c : PoissonCharlierExpansionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PoissonCharlierExpansionBudgetCertificate.size
    (c : PoissonCharlierExpansionBudgetCertificate) : ℕ :=
  c.poissonWindow + c.charlierWindow + c.coefficientWindow +
    c.remainderWindow + c.slack

theorem poissonCharlierExpansion_budgetCertificate_le_size
    (c : PoissonCharlierExpansionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def samplePoissonCharlierExpansionBudgetCertificate :
    PoissonCharlierExpansionBudgetCertificate :=
  { poissonWindow := 8
    charlierWindow := 2
    coefficientWindow := 5
    remainderWindow := 14
    certificateBudgetWindow := 30
    slack := 1 }

example : samplePoissonCharlierExpansionBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonCharlierExpansionBudgetCertificate.controlled,
      samplePoissonCharlierExpansionBudgetCertificate]
  · norm_num [PoissonCharlierExpansionBudgetCertificate.budgetControlled,
      samplePoissonCharlierExpansionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePoissonCharlierExpansionBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonCharlierExpansionBudgetCertificate.controlled,
      samplePoissonCharlierExpansionBudgetCertificate]
  · norm_num [PoissonCharlierExpansionBudgetCertificate.budgetControlled,
      samplePoissonCharlierExpansionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePoissonCharlierExpansionBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonCharlierExpansionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List PoissonCharlierExpansionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePoissonCharlierExpansionBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    samplePoissonCharlierExpansionBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.PoissonCharlierExpansion
