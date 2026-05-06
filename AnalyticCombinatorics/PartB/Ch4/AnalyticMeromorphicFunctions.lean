import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic functions and meromorphic functions.
-/

namespace AnalyticCombinatorics.PartB.Ch4.AnalyticMeromorphicFunctions

/-- Geometric coefficient model for a simple pole. -/
def geometricPoleCoeff (base n : ℕ) : ℕ :=
  base ^ n

/-- Finite Cauchy-style coefficient envelope. -/
def coefficientEnvelopeCheck
    (coeff envelope : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => coeff n ≤ envelope n

/-- Finite pole-order descriptor. -/
structure PoleWindow where
  order : ℕ
  residueScale : ℕ
deriving DecidableEq, Repr

def PoleWindow.valid (w : PoleWindow) : Prop :=
  0 < w.order ∧ 0 < w.residueScale

/-- Finite analytic/meromorphic statement form. -/
def MeromorphicCoefficientWindow
    (coeff envelope : ℕ → ℕ) (N : ℕ) : Prop :=
  coefficientEnvelopeCheck coeff envelope N = true

theorem geometricPole_meromorphicWindow :
    MeromorphicCoefficientWindow (geometricPoleCoeff 2) (geometricPoleCoeff 2) 16 := by
  unfold MeromorphicCoefficientWindow coefficientEnvelopeCheck geometricPoleCoeff
  native_decide

theorem simplePoleWindow_valid :
    PoleWindow.valid { order := 1, residueScale := 1 } := by
  norm_num [PoleWindow.valid]

/-- Finite recurrence audit for coefficients of a simple meromorphic pole. -/
def geometricPoleRatioCheck (base N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    geometricPoleCoeff base (n + 1) = base * geometricPoleCoeff base n

theorem geometricPole_ratioWindow :
    geometricPoleRatioCheck 3 16 = true := by
  unfold geometricPoleRatioCheck geometricPoleCoeff
  native_decide

example : geometricPoleCoeff 3 4 = 81 := by
  unfold geometricPoleCoeff
  native_decide

example : geometricPoleRatioCheck 2 5 = true := by
  unfold geometricPoleRatioCheck geometricPoleCoeff
  native_decide

structure AnalyticMeromorphicFunctionsBudgetCertificate where
  analyticWindow : ℕ
  poleWindow : ℕ
  meromorphicWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticMeromorphicFunctionsBudgetCertificate.controlled
    (c : AnalyticMeromorphicFunctionsBudgetCertificate) : Prop :=
  0 < c.analyticWindow ∧
    c.meromorphicWindow ≤ c.analyticWindow + c.poleWindow + c.slack

def AnalyticMeromorphicFunctionsBudgetCertificate.budgetControlled
    (c : AnalyticMeromorphicFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.analyticWindow + c.poleWindow + c.meromorphicWindow + c.slack

def AnalyticMeromorphicFunctionsBudgetCertificate.Ready
    (c : AnalyticMeromorphicFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticMeromorphicFunctionsBudgetCertificate.size
    (c : AnalyticMeromorphicFunctionsBudgetCertificate) : ℕ :=
  c.analyticWindow + c.poleWindow + c.meromorphicWindow + c.slack

theorem analyticMeromorphicFunctions_budgetCertificate_le_size
    (c : AnalyticMeromorphicFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAnalyticMeromorphicFunctionsBudgetCertificate :
    AnalyticMeromorphicFunctionsBudgetCertificate :=
  { analyticWindow := 5
    poleWindow := 6
    meromorphicWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticMeromorphicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticMeromorphicFunctionsBudgetCertificate.controlled,
      sampleAnalyticMeromorphicFunctionsBudgetCertificate]
  · norm_num [AnalyticMeromorphicFunctionsBudgetCertificate.budgetControlled,
      sampleAnalyticMeromorphicFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticMeromorphicFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticMeromorphicFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticMeromorphicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticMeromorphicFunctionsBudgetCertificate.controlled,
      sampleAnalyticMeromorphicFunctionsBudgetCertificate]
  · norm_num [AnalyticMeromorphicFunctionsBudgetCertificate.budgetControlled,
      sampleAnalyticMeromorphicFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticMeromorphicFunctionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAnalyticMeromorphicFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAnalyticMeromorphicFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.AnalyticMeromorphicFunctions
