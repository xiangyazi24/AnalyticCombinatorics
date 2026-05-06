import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix A: formal power series.

Finite coefficient-window bookkeeping for addition, product, composition, and
truncation.
-/

namespace AnalyticCombinatorics.AppA.FormalPowerSeries

/-- Coefficient of a finite Cauchy product. -/
def cauchyProductCoeff (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + a k * b (n - k)) 0

/-- Truncated sum of coefficients. -/
def truncatedSeriesSum (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + a n) 0

theorem cauchyProduct_constant_samples :
    cauchyProductCoeff (fun _ => 1) (fun _ => 1) 0 = 1 ∧
    cauchyProductCoeff (fun _ => 1) (fun _ => 1) 3 = 4 ∧
    truncatedSeriesSum (fun _ => 1) 5 = 6 := by
  unfold cauchyProductCoeff truncatedSeriesSum
  native_decide

def convolutionLength (leftTerms rightTerms : ℕ) : ℕ :=
  leftTerms + rightTerms - 1

theorem convolutionLength_samples :
    convolutionLength 3 4 = 6 ∧
    convolutionLength 1 5 = 5 := by
  native_decide

structure FormalPowerSeriesWindow where
  coefficientDepth : ℕ
  operationArity : ℕ
  truncationWindow : ℕ
  seriesSlack : ℕ
deriving DecidableEq, Repr

def formalPowerSeriesReady (w : FormalPowerSeriesWindow) : Prop :=
  0 < w.coefficientDepth ∧
    w.truncationWindow ≤ w.coefficientDepth * (w.operationArity + 1) + w.seriesSlack

def formalPowerSeriesBudget (w : FormalPowerSeriesWindow) : ℕ :=
  w.coefficientDepth + w.operationArity + w.truncationWindow + w.seriesSlack

theorem truncationWindow_le_budget
    (w : FormalPowerSeriesWindow) :
    w.truncationWindow ≤ formalPowerSeriesBudget w + w.coefficientDepth * w.operationArity := by
  unfold formalPowerSeriesBudget
  omega

def sampleFormalPowerSeriesWindow : FormalPowerSeriesWindow :=
  { coefficientDepth := 4, operationArity := 2, truncationWindow := 10,
    seriesSlack := 2 }

example : formalPowerSeriesReady sampleFormalPowerSeriesWindow := by
  norm_num [formalPowerSeriesReady, sampleFormalPowerSeriesWindow]

structure FormalPowerSeriesBudgetCertificate where
  coefficientWindow : ℕ
  operationWindow : ℕ
  truncationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FormalPowerSeriesBudgetCertificate.controlled
    (c : FormalPowerSeriesBudgetCertificate) : Prop :=
  0 < c.coefficientWindow ∧
    c.truncationWindow ≤ c.coefficientWindow * (c.operationWindow + 1) + c.slack

def FormalPowerSeriesBudgetCertificate.budgetControlled
    (c : FormalPowerSeriesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.coefficientWindow + c.operationWindow + c.truncationWindow + c.slack

def FormalPowerSeriesBudgetCertificate.Ready
    (c : FormalPowerSeriesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FormalPowerSeriesBudgetCertificate.size
    (c : FormalPowerSeriesBudgetCertificate) : ℕ :=
  c.coefficientWindow + c.operationWindow + c.truncationWindow + c.slack

theorem formalPowerSeries_budgetCertificate_le_size
    (c : FormalPowerSeriesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleFormalPowerSeriesBudgetCertificate :
    FormalPowerSeriesBudgetCertificate :=
  { coefficientWindow := 4
    operationWindow := 2
    truncationWindow := 10
    certificateBudgetWindow := 17
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFormalPowerSeriesBudgetCertificate.Ready := by
  constructor
  · norm_num [FormalPowerSeriesBudgetCertificate.controlled,
      sampleFormalPowerSeriesBudgetCertificate]
  · norm_num [FormalPowerSeriesBudgetCertificate.budgetControlled,
      sampleFormalPowerSeriesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFormalPowerSeriesBudgetCertificate.certificateBudgetWindow ≤
      sampleFormalPowerSeriesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFormalPowerSeriesBudgetCertificate.Ready := by
  constructor
  · norm_num [FormalPowerSeriesBudgetCertificate.controlled,
      sampleFormalPowerSeriesBudgetCertificate]
  · norm_num [FormalPowerSeriesBudgetCertificate.budgetControlled,
      sampleFormalPowerSeriesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FormalPowerSeriesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleFormalPowerSeriesBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleFormalPowerSeriesBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FormalPowerSeries
