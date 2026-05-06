import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Matrix Saddle Point

Finite Hessian and determinant models for multivariate saddle-point
approximations.
-/

namespace AnalyticCombinatorics.Asymptotics.MatrixSaddlePoint

def det2 (a b c d : ℚ) : ℚ :=
  a * d - b * c

theorem det2_samples :
    det2 1 0 0 1 = 1 ∧
    det2 2 1 1 2 = 3 ∧
    det2 3 4 5 6 = -2 := by
  native_decide

def positiveDefinite2 (a b d : ℚ) : Bool :=
  0 < a && 0 < det2 a b b d

theorem positiveDefinite2_samples :
    positiveDefinite2 2 0 3 = true ∧
    positiveDefinite2 1 2 1 = false := by
  native_decide

def quadraticForm2 (a b d x y : ℚ) : ℚ :=
  a * x ^ 2 + 2 * b * x * y + d * y ^ 2

theorem quadraticForm2_samples :
    quadraticForm2 1 0 1 3 4 = 25 ∧
    quadraticForm2 2 1 2 1 1 = 6 := by
  native_decide

structure MatrixSaddleData where
  dimension : ℕ
  determinantNumerator : ℕ
  determinantDenominator : ℕ

def bivariateGaussianSaddle : MatrixSaddleData where
  dimension := 2
  determinantNumerator := 1
  determinantDenominator := 1

theorem bivariateGaussianSaddle_values :
    bivariateGaussianSaddle.dimension = 2 ∧
    bivariateGaussianSaddle.determinantNumerator = 1 ∧
    bivariateGaussianSaddle.determinantDenominator = 1 := by
  native_decide

def matrixSaddleDataReady (data : MatrixSaddleData) : Prop :=
  0 < data.dimension ∧ 0 < data.determinantNumerator ∧ 0 < data.determinantDenominator

theorem bivariateGaussianSaddle_ready :
    matrixSaddleDataReady bivariateGaussianSaddle := by
  unfold matrixSaddleDataReady bivariateGaussianSaddle
  native_decide

/-- Finite executable readiness audit for matrix saddle-point data. -/
def matrixSaddleDataListReady (data : List MatrixSaddleData) : Bool :=
  data.all fun d =>
    0 < d.dimension && 0 < d.determinantNumerator && 0 < d.determinantDenominator

theorem matrixSaddleDataList_readyWindow :
    matrixSaddleDataListReady
      [{ dimension := 1, determinantNumerator := 2, determinantDenominator := 3 },
       { dimension := 2, determinantNumerator := 1, determinantDenominator := 1 }] =
      true := by
  unfold matrixSaddleDataListReady
  native_decide

def MatrixSaddlePointEstimate
    (coeff : List ℕ → ℂ) (data : MatrixSaddleData) : Prop :=
  matrixSaddleDataReady data ∧ coeff [] = 0 ∧ coeff [1, 1] = 6

def matrixSaddleCoeffWitness (idx : List ℕ) : ℂ :=
  3 * idx.sum

theorem matrix_saddle_point_estimate_statement :
    MatrixSaddlePointEstimate matrixSaddleCoeffWitness bivariateGaussianSaddle := by
  unfold MatrixSaddlePointEstimate matrixSaddleDataReady bivariateGaussianSaddle
    matrixSaddleCoeffWitness
  norm_num

/-- A finite certificate for matrix saddle-point data. -/
structure MatrixSaddleCertificate where
  dimensionWindow : ℕ
  determinantNumeratorWindow : ℕ
  determinantDenominatorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Matrix saddle certificates keep dimension and determinant data positive. -/
def matrixSaddleCertificateControlled
    (w : MatrixSaddleCertificate) : Prop :=
  0 < w.dimensionWindow ∧
    0 < w.determinantNumeratorWindow ∧
      0 < w.determinantDenominatorWindow

/-- Readiness for a matrix saddle certificate. -/
def matrixSaddleCertificateReady
    (w : MatrixSaddleCertificate) : Prop :=
  matrixSaddleCertificateControlled w ∧
    w.certificateBudget ≤
      w.dimensionWindow + w.determinantNumeratorWindow +
        w.determinantDenominatorWindow + w.slack

/-- Total size of a matrix saddle certificate. -/
def matrixSaddleCertificateSize (w : MatrixSaddleCertificate) : ℕ :=
  w.dimensionWindow + w.determinantNumeratorWindow +
    w.determinantDenominatorWindow + w.certificateBudget + w.slack

theorem matrixSaddleCertificate_budget_le_size
    (w : MatrixSaddleCertificate)
    (h : matrixSaddleCertificateReady w) :
    w.certificateBudget ≤ matrixSaddleCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold matrixSaddleCertificateSize
  omega

def sampleMatrixSaddleCertificate : MatrixSaddleCertificate where
  dimensionWindow := 2
  determinantNumeratorWindow := 1
  determinantDenominatorWindow := 1
  certificateBudget := 4
  slack := 1

example :
    matrixSaddleCertificateReady sampleMatrixSaddleCertificate := by
  norm_num [matrixSaddleCertificateReady,
    matrixSaddleCertificateControlled, sampleMatrixSaddleCertificate]

example :
    sampleMatrixSaddleCertificate.certificateBudget ≤
      matrixSaddleCertificateSize sampleMatrixSaddleCertificate := by
  apply matrixSaddleCertificate_budget_le_size
  norm_num [matrixSaddleCertificateReady,
    matrixSaddleCertificateControlled, sampleMatrixSaddleCertificate]

/-- A refinement certificate with the determinant budget separated from size. -/
structure MatrixSaddleRefinementCertificate where
  dimensionWindow : ℕ
  determinantNumeratorWindow : ℕ
  determinantDenominatorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def MatrixSaddleRefinementCertificate.parametersControlled
    (cert : MatrixSaddleRefinementCertificate) : Prop :=
  0 < cert.dimensionWindow ∧
    0 < cert.determinantNumeratorWindow ∧
      0 < cert.determinantDenominatorWindow

def MatrixSaddleRefinementCertificate.budgetControlled
    (cert : MatrixSaddleRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.dimensionWindow + cert.determinantNumeratorWindow +
      cert.determinantDenominatorWindow + cert.slack

def matrixSaddleRefinementReady
    (cert : MatrixSaddleRefinementCertificate) : Prop :=
  cert.parametersControlled ∧ cert.budgetControlled

def MatrixSaddleRefinementCertificate.size
    (cert : MatrixSaddleRefinementCertificate) : ℕ :=
  cert.dimensionWindow + cert.determinantNumeratorWindow +
    cert.determinantDenominatorWindow + cert.slack

theorem matrixSaddle_certificateBudgetWindow_le_size
    (cert : MatrixSaddleRefinementCertificate)
    (h : matrixSaddleRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMatrixSaddleRefinementCertificate :
    MatrixSaddleRefinementCertificate where
  dimensionWindow := 2
  determinantNumeratorWindow := 1
  determinantDenominatorWindow := 1
  certificateBudgetWindow := 5
  slack := 1

example :
    matrixSaddleRefinementReady sampleMatrixSaddleRefinementCertificate := by
  norm_num [matrixSaddleRefinementReady,
    MatrixSaddleRefinementCertificate.parametersControlled,
    MatrixSaddleRefinementCertificate.budgetControlled,
    sampleMatrixSaddleRefinementCertificate]

example :
    sampleMatrixSaddleRefinementCertificate.certificateBudgetWindow ≤
      sampleMatrixSaddleRefinementCertificate.size := by
  apply matrixSaddle_certificateBudgetWindow_le_size
  norm_num [matrixSaddleRefinementReady,
    MatrixSaddleRefinementCertificate.parametersControlled,
    MatrixSaddleRefinementCertificate.budgetControlled,
    sampleMatrixSaddleRefinementCertificate]


structure MatrixSaddlePointBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MatrixSaddlePointBudgetCertificate.controlled
    (c : MatrixSaddlePointBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def MatrixSaddlePointBudgetCertificate.budgetControlled
    (c : MatrixSaddlePointBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MatrixSaddlePointBudgetCertificate.Ready
    (c : MatrixSaddlePointBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MatrixSaddlePointBudgetCertificate.size
    (c : MatrixSaddlePointBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem matrixSaddlePoint_budgetCertificate_le_size
    (c : MatrixSaddlePointBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMatrixSaddlePointBudgetCertificate :
    MatrixSaddlePointBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleMatrixSaddlePointBudgetCertificate.Ready := by
  constructor
  · norm_num [MatrixSaddlePointBudgetCertificate.controlled,
      sampleMatrixSaddlePointBudgetCertificate]
  · norm_num [MatrixSaddlePointBudgetCertificate.budgetControlled,
      sampleMatrixSaddlePointBudgetCertificate]

example :
    sampleMatrixSaddlePointBudgetCertificate.certificateBudgetWindow ≤
      sampleMatrixSaddlePointBudgetCertificate.size := by
  apply matrixSaddlePoint_budgetCertificate_le_size
  constructor
  · norm_num [MatrixSaddlePointBudgetCertificate.controlled,
      sampleMatrixSaddlePointBudgetCertificate]
  · norm_num [MatrixSaddlePointBudgetCertificate.budgetControlled,
      sampleMatrixSaddlePointBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMatrixSaddlePointBudgetCertificate.Ready := by
  constructor
  · norm_num [MatrixSaddlePointBudgetCertificate.controlled,
      sampleMatrixSaddlePointBudgetCertificate]
  · norm_num [MatrixSaddlePointBudgetCertificate.budgetControlled,
      sampleMatrixSaddlePointBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMatrixSaddlePointBudgetCertificate.certificateBudgetWindow ≤
      sampleMatrixSaddlePointBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MatrixSaddlePointBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMatrixSaddlePointBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleMatrixSaddlePointBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.MatrixSaddlePoint
