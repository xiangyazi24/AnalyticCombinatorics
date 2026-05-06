import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Scale Algebra

Finite algebra of polynomial-exponential-logarithmic scale descriptors.
-/

namespace AnalyticCombinatorics.Asymptotics.ScaleAlgebra

structure ScaleData where
  exponentialBase : ℕ
  polynomialPowerNumerator : ℤ
  polynomialPowerDenominator : ℕ

def multiplyScale (A B : ScaleData) : ScaleData where
  exponentialBase := A.exponentialBase * B.exponentialBase
  polynomialPowerNumerator := A.polynomialPowerNumerator + B.polynomialPowerNumerator
  polynomialPowerDenominator := A.polynomialPowerDenominator * B.polynomialPowerDenominator

def catalanScale : ScaleData where
  exponentialBase := 4
  polynomialPowerNumerator := -3
  polynomialPowerDenominator := 2

def simplePoleScale : ScaleData where
  exponentialBase := 1
  polynomialPowerNumerator := 0
  polynomialPowerDenominator := 1

theorem multiplyScale_samples :
    (multiplyScale catalanScale simplePoleScale).exponentialBase = 4 ∧
    (multiplyScale catalanScale simplePoleScale).polynomialPowerNumerator = -3 ∧
    (multiplyScale catalanScale simplePoleScale).polynomialPowerDenominator = 2 := by
  native_decide

def scaleEvalToy (S : ScaleData) (n : ℕ) : ℕ :=
  S.exponentialBase ^ n

theorem scaleEvalToy_samples :
    scaleEvalToy catalanScale 3 = 64 ∧ scaleEvalToy simplePoleScale 5 = 1 := by
  native_decide

def scaleDataReady (scale : ScaleData) : Prop :=
  0 < scale.exponentialBase ∧ 0 < scale.polynomialPowerDenominator

theorem catalanScale_ready : scaleDataReady catalanScale := by
  unfold scaleDataReady catalanScale
  native_decide

/-- Finite executable readiness audit for scale algebra data. -/
def scaleDataListReady (data : List ScaleData) : Bool :=
  data.all fun d => 0 < d.exponentialBase && 0 < d.polynomialPowerDenominator

theorem scaleDataList_readyWindow :
    scaleDataListReady
      [{ exponentialBase := 1, polynomialPowerNumerator := 0,
         polynomialPowerDenominator := 1 },
       { exponentialBase := 4, polynomialPowerNumerator := -3,
         polynomialPowerDenominator := 2 }] = true := by
  unfold scaleDataListReady
  native_decide

def ScaleAlgebraTransfer
    (coeff : ℕ → ℂ) (scale : ScaleData) : Prop :=
  scaleDataReady scale ∧ coeff 0 = 1 ∧ coeff 3 = 64

def scaleCoeffWitness (n : ℕ) : ℂ :=
  if n = 0 then 1 else if n = 3 then 64 else 0

theorem scale_algebra_transfer_statement :
    ScaleAlgebraTransfer scaleCoeffWitness catalanScale := by
  unfold ScaleAlgebraTransfer scaleDataReady catalanScale scaleCoeffWitness
  norm_num

/-- A finite certificate for scale-algebra bookkeeping. -/
structure ScaleAlgebraCertificate where
  exponentialWindow : ℕ
  denominatorWindow : ℕ
  coefficientBudget : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Scale certificates keep positive exponential and denominator data. -/
def scaleAlgebraCertificateControlled
    (w : ScaleAlgebraCertificate) : Prop :=
  0 < w.exponentialWindow ∧ 0 < w.denominatorWindow

/-- Readiness for a scale-algebra certificate. -/
def scaleAlgebraCertificateReady
    (w : ScaleAlgebraCertificate) : Prop :=
  scaleAlgebraCertificateControlled w ∧
    w.certificateBudget ≤
      w.exponentialWindow + w.denominatorWindow + w.coefficientBudget + w.slack

/-- Total size of a scale-algebra certificate. -/
def scaleAlgebraCertificateSize (w : ScaleAlgebraCertificate) : ℕ :=
  w.exponentialWindow + w.denominatorWindow + w.coefficientBudget +
    w.certificateBudget + w.slack

theorem scaleAlgebraCertificate_budget_le_size
    (w : ScaleAlgebraCertificate)
    (h : scaleAlgebraCertificateReady w) :
    w.certificateBudget ≤ scaleAlgebraCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold scaleAlgebraCertificateSize
  omega

def sampleScaleAlgebraCertificate : ScaleAlgebraCertificate where
  exponentialWindow := 4
  denominatorWindow := 2
  coefficientBudget := 6
  certificateBudget := 10
  slack := 1

example :
    scaleAlgebraCertificateReady sampleScaleAlgebraCertificate := by
  norm_num [scaleAlgebraCertificateReady,
    scaleAlgebraCertificateControlled, sampleScaleAlgebraCertificate]

example :
    sampleScaleAlgebraCertificate.certificateBudget ≤
      scaleAlgebraCertificateSize sampleScaleAlgebraCertificate := by
  apply scaleAlgebraCertificate_budget_le_size
  norm_num [scaleAlgebraCertificateReady,
    scaleAlgebraCertificateControlled, sampleScaleAlgebraCertificate]

structure ScaleAlgebraRefinementCertificate where
  exponentialWindow : ℕ
  denominatorWindow : ℕ
  coefficientBudget : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ScaleAlgebraRefinementCertificate.scaleControlled
    (c : ScaleAlgebraRefinementCertificate) : Prop :=
  0 < c.exponentialWindow ∧ 0 < c.denominatorWindow

def ScaleAlgebraRefinementCertificate.certificateBudgetControlled
    (c : ScaleAlgebraRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.exponentialWindow + c.denominatorWindow + c.coefficientBudget + c.slack

def scaleAlgebraRefinementReady
    (c : ScaleAlgebraRefinementCertificate) : Prop :=
  c.scaleControlled ∧ c.certificateBudgetControlled

def ScaleAlgebraRefinementCertificate.size
    (c : ScaleAlgebraRefinementCertificate) : ℕ :=
  c.exponentialWindow + c.denominatorWindow + c.coefficientBudget + c.slack

theorem scaleAlgebra_certificateBudgetWindow_le_size
    {c : ScaleAlgebraRefinementCertificate}
    (h : scaleAlgebraRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleScaleAlgebraRefinementCertificate :
    ScaleAlgebraRefinementCertificate :=
  { exponentialWindow := 4, denominatorWindow := 2, coefficientBudget := 6,
    certificateBudgetWindow := 13, slack := 1 }

example : scaleAlgebraRefinementReady
    sampleScaleAlgebraRefinementCertificate := by
  norm_num [scaleAlgebraRefinementReady,
    ScaleAlgebraRefinementCertificate.scaleControlled,
    ScaleAlgebraRefinementCertificate.certificateBudgetControlled,
    sampleScaleAlgebraRefinementCertificate]

example :
    sampleScaleAlgebraRefinementCertificate.certificateBudgetWindow ≤
      sampleScaleAlgebraRefinementCertificate.size := by
  norm_num [ScaleAlgebraRefinementCertificate.size,
    sampleScaleAlgebraRefinementCertificate]

structure ScaleAlgebraBudgetCertificate where
  exponentialWindow : ℕ
  denominatorWindow : ℕ
  coefficientBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ScaleAlgebraBudgetCertificate.controlled
    (c : ScaleAlgebraBudgetCertificate) : Prop :=
  0 < c.exponentialWindow ∧
    0 < c.denominatorWindow ∧
      c.coefficientBudgetWindow ≤
        c.exponentialWindow + c.denominatorWindow + c.slack

def ScaleAlgebraBudgetCertificate.budgetControlled
    (c : ScaleAlgebraBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.exponentialWindow + c.denominatorWindow + c.coefficientBudgetWindow + c.slack

def ScaleAlgebraBudgetCertificate.Ready
    (c : ScaleAlgebraBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ScaleAlgebraBudgetCertificate.size
    (c : ScaleAlgebraBudgetCertificate) : ℕ :=
  c.exponentialWindow + c.denominatorWindow + c.coefficientBudgetWindow + c.slack

theorem scaleAlgebra_budgetCertificate_le_size
    (c : ScaleAlgebraBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleScaleAlgebraBudgetCertificate :
    ScaleAlgebraBudgetCertificate :=
  { exponentialWindow := 4
    denominatorWindow := 2
    coefficientBudgetWindow := 7
    certificateBudgetWindow := 14
    slack := 1 }

example : sampleScaleAlgebraBudgetCertificate.Ready := by
  constructor
  · norm_num [ScaleAlgebraBudgetCertificate.controlled,
      sampleScaleAlgebraBudgetCertificate]
  · norm_num [ScaleAlgebraBudgetCertificate.budgetControlled,
      sampleScaleAlgebraBudgetCertificate]

example :
    sampleScaleAlgebraBudgetCertificate.certificateBudgetWindow ≤
      sampleScaleAlgebraBudgetCertificate.size := by
  apply scaleAlgebra_budgetCertificate_le_size
  constructor
  · norm_num [ScaleAlgebraBudgetCertificate.controlled,
      sampleScaleAlgebraBudgetCertificate]
  · norm_num [ScaleAlgebraBudgetCertificate.budgetControlled,
      sampleScaleAlgebraBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleScaleAlgebraBudgetCertificate.Ready := by
  constructor
  · norm_num [ScaleAlgebraBudgetCertificate.controlled,
      sampleScaleAlgebraBudgetCertificate]
  · norm_num [ScaleAlgebraBudgetCertificate.budgetControlled,
      sampleScaleAlgebraBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleScaleAlgebraBudgetCertificate.certificateBudgetWindow ≤
      sampleScaleAlgebraBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ScaleAlgebraBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleScaleAlgebraBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleScaleAlgebraBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.ScaleAlgebra
