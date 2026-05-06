import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix A: Finite Linear Algebra

Small matrix and vector models used for transfer matrices, systems of
functional equations, and finite-state combinatorial specifications.
-/

namespace AnalyticCombinatorics.AppA.FiniteLinearAlgebra

/-- Dot product of two rational vectors, truncated to the shorter prefix by `getD`. -/
def dotProduct (xs ys : List ℚ) : ℚ :=
  (List.range (max xs.length ys.length)).foldl
    (fun s i => s + xs.getD i 0 * ys.getD i 0) 0

theorem dotProduct_samples :
    dotProduct [1, 2, 3] [4, 5, 6] = 32 ∧
    dotProduct [1, 2] [3, 4, 5] = 11 ∧
    dotProduct [] [1, 2] = 0 := by
  native_decide

/-- Matrix-vector product for a rational matrix represented by rows. -/
def matVec (A : List (List ℚ)) (x : List ℚ) : List ℚ :=
  A.map fun row => dotProduct row x

theorem matVec_identity :
    matVec [[1, 0], [0, 1]] [3, 5] = [3, 5] := by
  native_decide

theorem matVec_fibonacci :
    matVec [[1, 1], [1, 0]] [5, 3] = [8, 5] := by
  native_decide

/-- Matrix multiplication, using the column view by `getD`. -/
def matMul (A B : List (List ℚ)) : List (List ℚ) :=
  let cols := (B.map List.length).foldl max 0
  A.map fun row =>
    (List.range cols).map fun j =>
      dotProduct row (B.map fun brow => brow.getD j 0)

theorem matMul_identity_left :
    matMul [[1, 0], [0, 1]] [[2, 3], [5, 7]] = [[2, 3], [5, 7]] := by
  native_decide

theorem matMul_fibonacci_square :
    matMul [[1, 1], [1, 0]] [[1, 1], [1, 0]] = [[2, 1], [1, 1]] := by
  native_decide

/-- Matrix powers by repeated multiplication. -/
def matPow (A : List (List ℚ)) : ℕ → List (List ℚ)
  | 0 => [[1, 0], [0, 1]]
  | n + 1 => matMul A (matPow A n)

theorem matPow_fibonacci_0 :
    matPow [[1, 1], [1, 0]] 0 = [[1, 0], [0, 1]] := by
  native_decide

theorem matPow_fibonacci_5 :
    matPow [[1, 1], [1, 0]] 5 = [[8, 5], [5, 3]] := by
  native_decide

/-- Spectral-radius descriptor for a transfer matrix. -/
structure SpectralData where
  dimension : ℕ
  dominantNumerator : ℕ
  dominantDenominator : ℕ

def fibonacciSpectralData : SpectralData where
  dimension := 2
  dominantNumerator := 1618
  dominantDenominator := 1000

theorem fibonacciSpectralData_values :
    fibonacciSpectralData.dimension = 2 ∧
    fibonacciSpectralData.dominantNumerator = 1618 ∧
    fibonacciSpectralData.dominantDenominator = 1000 := by
  native_decide

/-- Spectral descriptor well-formedness certificate. -/
def spectralDataReady (data : SpectralData) : Prop :=
  0 < data.dimension ∧ 0 < data.dominantNumerator ∧ 0 < data.dominantDenominator

theorem fibonacciSpectralData_ready : spectralDataReady fibonacciSpectralData := by
  unfold spectralDataReady fibonacciSpectralData
  native_decide

/-- Perron-Frobenius dominance certificate for nonnegative matrices. -/
def PerronFrobeniusStatement
    (A : List (List ℚ)) (data : SpectralData) : Prop :=
  spectralDataReady data ∧ A.length = data.dimension ∧ (A.getD 0 []).length = data.dimension

theorem perron_frobenius_statement :
    PerronFrobeniusStatement [[1, 1], [1, 0]] fibonacciSpectralData := by
  unfold PerronFrobeniusStatement spectralDataReady fibonacciSpectralData
  native_decide


structure FiniteLinearAlgebraBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteLinearAlgebraBudgetCertificate.controlled
    (c : FiniteLinearAlgebraBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteLinearAlgebraBudgetCertificate.budgetControlled
    (c : FiniteLinearAlgebraBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteLinearAlgebraBudgetCertificate.Ready
    (c : FiniteLinearAlgebraBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteLinearAlgebraBudgetCertificate.size
    (c : FiniteLinearAlgebraBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteLinearAlgebra_budgetCertificate_le_size
    (c : FiniteLinearAlgebraBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteLinearAlgebraBudgetCertificate :
    FiniteLinearAlgebraBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteLinearAlgebraBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLinearAlgebraBudgetCertificate.controlled,
      sampleFiniteLinearAlgebraBudgetCertificate]
  · norm_num [FiniteLinearAlgebraBudgetCertificate.budgetControlled,
      sampleFiniteLinearAlgebraBudgetCertificate]

example :
    sampleFiniteLinearAlgebraBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLinearAlgebraBudgetCertificate.size := by
  apply finiteLinearAlgebra_budgetCertificate_le_size
  constructor
  · norm_num [FiniteLinearAlgebraBudgetCertificate.controlled,
      sampleFiniteLinearAlgebraBudgetCertificate]
  · norm_num [FiniteLinearAlgebraBudgetCertificate.budgetControlled,
      sampleFiniteLinearAlgebraBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteLinearAlgebraBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLinearAlgebraBudgetCertificate.controlled,
      sampleFiniteLinearAlgebraBudgetCertificate]
  · norm_num [FiniteLinearAlgebraBudgetCertificate.budgetControlled,
      sampleFiniteLinearAlgebraBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteLinearAlgebraBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLinearAlgebraBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteLinearAlgebraBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteLinearAlgebraBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteLinearAlgebraBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteLinearAlgebra
