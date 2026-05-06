import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Coefficient asymptotics for the standard scale.

Finite bookkeeping for algebraic-logarithmic coefficient scales.
-/

namespace AnalyticCombinatorics.PartB.Ch6.StandardScaleCoefficientAsymptotics

/-- Algebraic standard-scale model `n^alpha`. -/
def algebraicScaleCoeff (alpha n : ℕ) : ℕ :=
  (n + 1) ^ alpha

/-- Logarithmic scale used for finite algebraic-logarithmic windows. -/
def logScaleProxy (beta n : ℕ) : ℕ :=
  (Nat.log2 (n + 2) + 1) ^ beta

/-- Combined algebraic-logarithmic coefficient-scale model. -/
def standardScaleCoeff (alpha beta n : ℕ) : ℕ :=
  algebraicScaleCoeff alpha n * logScaleProxy beta n

/-- Finite monotonicity audit for standard-scale proxies. -/
def standardScaleMonotoneCheck (alpha beta N : ℕ) : Bool :=
  (List.range N).all fun n =>
    standardScaleCoeff alpha beta n ≤ standardScaleCoeff alpha beta (n + 1)

theorem standardScaleCoeff_samples :
    standardScaleCoeff 2 1 0 = 2 ∧
    standardScaleCoeff 2 1 1 = 8 ∧
    standardScaleCoeff 2 1 2 = 27 := by
  unfold standardScaleCoeff algebraicScaleCoeff logScaleProxy
  native_decide

theorem standardScale_monotoneWindow :
    standardScaleMonotoneCheck 2 1 24 = true := by
  unfold standardScaleMonotoneCheck standardScaleCoeff algebraicScaleCoeff
    logScaleProxy
  native_decide

structure StandardScaleWindow where
  algebraicDepth : ℕ
  logarithmicDepth : ℕ
  coefficientWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def standardScaleReady (w : StandardScaleWindow) : Prop :=
  0 < w.algebraicDepth ∧
    w.coefficientWindow ≤ w.algebraicDepth + w.logarithmicDepth + w.slack

def standardScaleBudget (w : StandardScaleWindow) : ℕ :=
  w.algebraicDepth + w.logarithmicDepth + w.coefficientWindow + w.slack

theorem coefficientWindow_le_standardScaleBudget
    (w : StandardScaleWindow) :
    w.coefficientWindow ≤ standardScaleBudget w := by
  unfold standardScaleBudget
  omega

def sampleStandardScaleWindow : StandardScaleWindow :=
  { algebraicDepth := 5, logarithmicDepth := 4, coefficientWindow := 8, slack := 1 }

example : standardScaleReady sampleStandardScaleWindow := by
  norm_num [standardScaleReady, sampleStandardScaleWindow]

structure StandardScaleCoefficientAsymptoticsBudgetCertificate where
  scaleWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StandardScaleCoefficientAsymptoticsBudgetCertificate.controlled
    (c : StandardScaleCoefficientAsymptoticsBudgetCertificate) : Prop :=
  0 < c.scaleWindow ∧ c.coefficientWindow ≤ c.scaleWindow + c.slack

def StandardScaleCoefficientAsymptoticsBudgetCertificate.budgetControlled
    (c : StandardScaleCoefficientAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.scaleWindow + c.coefficientWindow + c.slack

def StandardScaleCoefficientAsymptoticsBudgetCertificate.Ready
    (c : StandardScaleCoefficientAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StandardScaleCoefficientAsymptoticsBudgetCertificate.size
    (c : StandardScaleCoefficientAsymptoticsBudgetCertificate) : ℕ :=
  c.scaleWindow + c.coefficientWindow + c.slack

theorem standardScaleCoefficientAsymptotics_budgetCertificate_le_size
    (c : StandardScaleCoefficientAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleStandardScaleCoefficientAsymptoticsBudgetCertificate :
    StandardScaleCoefficientAsymptoticsBudgetCertificate :=
  { scaleWindow := 7
    coefficientWindow := 8
    certificateBudgetWindow := 16
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleStandardScaleCoefficientAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [StandardScaleCoefficientAsymptoticsBudgetCertificate.controlled,
      sampleStandardScaleCoefficientAsymptoticsBudgetCertificate]
  · norm_num [StandardScaleCoefficientAsymptoticsBudgetCertificate.budgetControlled,
      sampleStandardScaleCoefficientAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleStandardScaleCoefficientAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleStandardScaleCoefficientAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleStandardScaleCoefficientAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [StandardScaleCoefficientAsymptoticsBudgetCertificate.controlled,
      sampleStandardScaleCoefficientAsymptoticsBudgetCertificate]
  · norm_num [StandardScaleCoefficientAsymptoticsBudgetCertificate.budgetControlled,
      sampleStandardScaleCoefficientAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List StandardScaleCoefficientAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleStandardScaleCoefficientAsymptoticsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleStandardScaleCoefficientAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.StandardScaleCoefficientAsymptotics
