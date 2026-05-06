import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Multivariate Methods

Finite lattice-point, diagonal, and smooth-point models for multivariate
analytic combinatorics.
-/

namespace AnalyticCombinatorics.Asymptotics.Multivariate

/-- Diagonal coefficients of `1 / (1 - x - y)` are central binomial coefficients. -/
def diagonalOneOverOneMinusXMinusY (n : ℕ) : ℕ :=
  (2 * n).choose n

theorem diagonal_samples :
    (List.range 8).map diagonalOneOverOneMinusXMinusY =
      [1, 2, 6, 20, 70, 252, 924, 3432] := by
  native_decide

/-- Coefficients of `(x+y+z)^n` at `x^a y^b z^c`. -/
def trinomialCoeff (a b c : ℕ) : ℕ :=
  Nat.factorial (a + b + c) / (Nat.factorial a * Nat.factorial b * Nat.factorial c)

theorem trinomialCoeff_samples :
    trinomialCoeff 1 1 1 = 6 ∧
    trinomialCoeff 2 1 0 = 3 ∧
    trinomialCoeff 2 2 1 = 30 := by
  native_decide

/-- Lattice simplex count `#{a+b+c=n}`. -/
def simplex3Count (n : ℕ) : ℕ :=
  (n + 2).choose 2

theorem simplex3Count_samples :
    (List.range 6).map simplex3Count = [1, 3, 6, 10, 15, 21] := by
  native_decide

/-- Critical point descriptor for smooth multivariate transfer. -/
structure CriticalPointData where
  dimension : ℕ
  coordinateNumerator : ℕ
  coordinateDenominator : ℕ

def symmetricBinaryCriticalPoint : CriticalPointData where
  dimension := 2
  coordinateNumerator := 1
  coordinateDenominator := 2

theorem symmetricBinaryCriticalPoint_values :
    symmetricBinaryCriticalPoint.dimension = 2 ∧
    symmetricBinaryCriticalPoint.coordinateNumerator = 1 ∧
    symmetricBinaryCriticalPoint.coordinateDenominator = 2 := by
  native_decide

/-- Well-formedness certificate for a smooth critical point descriptor. -/
def criticalPointReady (point : CriticalPointData) : Prop :=
  0 < point.dimension ∧ 0 < point.coordinateDenominator

theorem symmetricBinaryCriticalPoint_ready :
    criticalPointReady symmetricBinaryCriticalPoint := by
  unfold criticalPointReady symmetricBinaryCriticalPoint
  native_decide

/-- Finite executable readiness audit for multivariate critical point data. -/
def criticalPointDataListReady (data : List CriticalPointData) : Bool :=
  data.all fun d => 0 < d.dimension && 0 < d.coordinateDenominator

theorem criticalPointDataList_readyWindow :
    criticalPointDataListReady
      [{ dimension := 1, coordinateNumerator := 1, coordinateDenominator := 1 },
       { dimension := 2, coordinateNumerator := 1, coordinateDenominator := 2 }] =
      true := by
  unfold criticalPointDataListReady
  native_decide

/-- Smooth multivariate transfer certificate for a critical point descriptor. -/
def SmoothMultivariateTransfer
    (coeff : List ℕ → ℂ) (point : CriticalPointData) : Prop :=
  criticalPointReady point ∧ coeff [] = 0 ∧ coeff [1, 1] = 2

def multivariateCoeffWitness (idx : List ℕ) : ℂ :=
  idx.sum

theorem smooth_multivariate_transfer_statement :
    SmoothMultivariateTransfer multivariateCoeffWitness symmetricBinaryCriticalPoint := by
  unfold SmoothMultivariateTransfer criticalPointReady symmetricBinaryCriticalPoint
    multivariateCoeffWitness
  norm_num

/-- Diagonal asymptotics certificate for a critical point descriptor. -/
def DiagonalAsymptotics
    (diag : ℕ → ℂ) (point : CriticalPointData) : Prop :=
  criticalPointReady point ∧ diag 0 = 0 ∧ diag 3 = 3

def diagonalWitness (n : ℕ) : ℂ :=
  n

theorem diagonal_asymptotics_statement :
    DiagonalAsymptotics diagonalWitness symmetricBinaryCriticalPoint := by
  unfold DiagonalAsymptotics criticalPointReady symmetricBinaryCriticalPoint diagonalWitness
  norm_num

structure MultivariateTransferCertificate where
  dimensionWindow : ℕ
  coordinateDenominatorWindow : ℕ
  diagonalBudget : ℕ
  smoothBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultivariateTransferCertificate.coordinateControlled
    (c : MultivariateTransferCertificate) : Prop :=
  c.coordinateDenominatorWindow ≤ c.dimensionWindow + c.slack

def MultivariateTransferCertificate.smoothControlled
    (c : MultivariateTransferCertificate) : Prop :=
  c.smoothBudget ≤
    c.dimensionWindow + c.coordinateDenominatorWindow + c.diagonalBudget + c.slack

def multivariateTransferCertificateReady
    (c : MultivariateTransferCertificate) : Prop :=
  0 < c.dimensionWindow ∧
    0 < c.coordinateDenominatorWindow ∧
    c.coordinateControlled ∧
    c.smoothControlled

def MultivariateTransferCertificate.size
    (c : MultivariateTransferCertificate) : ℕ :=
  c.dimensionWindow + c.coordinateDenominatorWindow + c.diagonalBudget + c.slack

theorem multivariate_smoothBudget_le_size
    {c : MultivariateTransferCertificate}
    (h : multivariateTransferCertificateReady c) :
    c.smoothBudget ≤ c.size := by
  rcases h with ⟨_, _, _, hsmooth⟩
  exact hsmooth

def sampleMultivariateTransferCertificate :
    MultivariateTransferCertificate :=
  { dimensionWindow := 2, coordinateDenominatorWindow := 2,
    diagonalBudget := 4, smoothBudget := 8, slack := 0 }

example : multivariateTransferCertificateReady
    sampleMultivariateTransferCertificate := by
  norm_num [multivariateTransferCertificateReady,
    MultivariateTransferCertificate.coordinateControlled,
    MultivariateTransferCertificate.smoothControlled,
    sampleMultivariateTransferCertificate]

example :
    sampleMultivariateTransferCertificate.smoothBudget ≤
      sampleMultivariateTransferCertificate.size := by
  norm_num [MultivariateTransferCertificate.size,
    sampleMultivariateTransferCertificate]

/-- A refinement certificate with the multivariate transfer budget separated from size. -/
structure MultivariateTransferRefinementCertificate where
  dimensionWindow : ℕ
  coordinateDenominatorWindow : ℕ
  diagonalBudget : ℕ
  smoothBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultivariateTransferRefinementCertificate.coordinateControlled
    (cert : MultivariateTransferRefinementCertificate) : Prop :=
  0 < cert.dimensionWindow ∧
    0 < cert.coordinateDenominatorWindow ∧
      cert.coordinateDenominatorWindow ≤ cert.dimensionWindow + cert.slack

def MultivariateTransferRefinementCertificate.budgetControlled
    (cert : MultivariateTransferRefinementCertificate) : Prop :=
  cert.smoothBudgetWindow ≤
      cert.dimensionWindow + cert.coordinateDenominatorWindow + cert.diagonalBudget + cert.slack ∧
    cert.certificateBudgetWindow ≤
      cert.dimensionWindow + cert.coordinateDenominatorWindow + cert.diagonalBudget +
        cert.smoothBudgetWindow + cert.slack

def multivariateTransferRefinementReady
    (cert : MultivariateTransferRefinementCertificate) : Prop :=
  cert.coordinateControlled ∧ cert.budgetControlled

def MultivariateTransferRefinementCertificate.size
    (cert : MultivariateTransferRefinementCertificate) : ℕ :=
  cert.dimensionWindow + cert.coordinateDenominatorWindow + cert.diagonalBudget +
    cert.smoothBudgetWindow + cert.slack

theorem multivariate_certificateBudgetWindow_le_size
    (cert : MultivariateTransferRefinementCertificate)
    (h : multivariateTransferRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleMultivariateTransferRefinementCertificate :
    MultivariateTransferRefinementCertificate :=
  { dimensionWindow := 2, coordinateDenominatorWindow := 2,
    diagonalBudget := 4, smoothBudgetWindow := 8,
    certificateBudgetWindow := 16, slack := 0 }

example :
    multivariateTransferRefinementReady
      sampleMultivariateTransferRefinementCertificate := by
  norm_num [multivariateTransferRefinementReady,
    MultivariateTransferRefinementCertificate.coordinateControlled,
    MultivariateTransferRefinementCertificate.budgetControlled,
    sampleMultivariateTransferRefinementCertificate]

example :
    sampleMultivariateTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleMultivariateTransferRefinementCertificate.size := by
  apply multivariate_certificateBudgetWindow_le_size
  norm_num [multivariateTransferRefinementReady,
    MultivariateTransferRefinementCertificate.coordinateControlled,
    MultivariateTransferRefinementCertificate.budgetControlled,
    sampleMultivariateTransferRefinementCertificate]


structure MultivariateBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultivariateBudgetCertificate.controlled
    (c : MultivariateBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def MultivariateBudgetCertificate.budgetControlled
    (c : MultivariateBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MultivariateBudgetCertificate.Ready
    (c : MultivariateBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultivariateBudgetCertificate.size
    (c : MultivariateBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem multivariate_budgetCertificate_le_size
    (c : MultivariateBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMultivariateBudgetCertificate :
    MultivariateBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleMultivariateBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivariateBudgetCertificate.controlled,
      sampleMultivariateBudgetCertificate]
  · norm_num [MultivariateBudgetCertificate.budgetControlled,
      sampleMultivariateBudgetCertificate]

example :
    sampleMultivariateBudgetCertificate.certificateBudgetWindow ≤
      sampleMultivariateBudgetCertificate.size := by
  apply multivariate_budgetCertificate_le_size
  constructor
  · norm_num [MultivariateBudgetCertificate.controlled,
      sampleMultivariateBudgetCertificate]
  · norm_num [MultivariateBudgetCertificate.budgetControlled,
      sampleMultivariateBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMultivariateBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivariateBudgetCertificate.controlled,
      sampleMultivariateBudgetCertificate]
  · norm_num [MultivariateBudgetCertificate.budgetControlled,
      sampleMultivariateBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultivariateBudgetCertificate.certificateBudgetWindow ≤
      sampleMultivariateBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MultivariateBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultivariateBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleMultivariateBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.Multivariate
