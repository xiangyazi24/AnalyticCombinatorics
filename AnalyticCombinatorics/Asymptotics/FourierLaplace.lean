import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Fourier-Laplace Method

Finite characteristic-function and lattice-period models.
-/

namespace AnalyticCombinatorics.Asymptotics.FourierLaplace

def parityCharacter (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n

theorem parityCharacter_samples :
    (List.range 8).map parityCharacter = [1, -1, 1, -1, 1, -1, 1, -1] := by
  native_decide

def latticeSpanCheck (support : List ℕ) (span : ℕ) : Bool :=
  span ≠ 0 && support.all fun x => span ∣ x

theorem latticeSpanCheck_samples :
    latticeSpanCheck [0, 2, 4, 6] 2 = true ∧
    latticeSpanCheck [0, 2, 3] 2 = false := by
  native_decide

def characteristicToy (p q : ℚ) (parity : ℕ) : ℚ :=
  p + q * ((-1 : ℚ) ^ parity)

theorem characteristicToy_samples :
    characteristicToy (1 / 2) (1 / 2) 0 = 1 ∧
    characteristicToy (1 / 2) (1 / 2) 1 = 0 := by
  native_decide

structure FourierLaplaceData where
  latticeSpan : ℕ
  varianceNumerator : ℕ
  varianceDenominator : ℕ

def parityFourierData : FourierLaplaceData where
  latticeSpan := 2
  varianceNumerator := 1
  varianceDenominator := 1

theorem parityFourierData_values :
    parityFourierData.latticeSpan = 2 ∧
    parityFourierData.varianceNumerator = 1 ∧
    parityFourierData.varianceDenominator = 1 := by
  native_decide

def fourierLaplaceDataReady (data : FourierLaplaceData) : Prop :=
  0 < data.latticeSpan ∧ 0 < data.varianceNumerator ∧ 0 < data.varianceDenominator

theorem parityFourierData_ready : fourierLaplaceDataReady parityFourierData := by
  unfold fourierLaplaceDataReady parityFourierData
  native_decide

/-- Finite executable readiness audit for Fourier-Laplace data windows. -/
def fourierLaplaceDataListReady (data : List FourierLaplaceData) : Bool :=
  data.all fun d =>
    0 < d.latticeSpan && 0 < d.varianceNumerator && 0 < d.varianceDenominator

theorem fourierLaplaceDataList_readyWindow :
    fourierLaplaceDataListReady
      [{ latticeSpan := 1, varianceNumerator := 2, varianceDenominator := 3 },
       { latticeSpan := 2, varianceNumerator := 1, varianceDenominator := 1 }] =
      true := by
  unfold fourierLaplaceDataListReady
  native_decide

def FourierLaplaceLocalLimit
    (mass : ℕ → ℕ → ℚ) (data : FourierLaplaceData) : Prop :=
  fourierLaplaceDataReady data ∧ mass 0 0 = 1 ∧ mass 0 1 = 0

def fourierMassWitness (_n parity : ℕ) : ℚ :=
  characteristicToy (1 / 2) (1 / 2) parity

theorem fourier_laplace_local_limit_statement :
    FourierLaplaceLocalLimit fourierMassWitness parityFourierData := by
  unfold FourierLaplaceLocalLimit fourierLaplaceDataReady parityFourierData
    fourierMassWitness characteristicToy
  native_decide

/-- A finite certificate for Fourier-Laplace local-limit data. -/
structure FourierLaplaceCertificate where
  latticeWindow : ℕ
  varianceNumeratorWindow : ℕ
  varianceDenominatorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Fourier-Laplace certificates keep lattice and variance data positive. -/
def fourierLaplaceCertificateControlled
    (w : FourierLaplaceCertificate) : Prop :=
  0 < w.latticeWindow ∧
    0 < w.varianceNumeratorWindow ∧
      0 < w.varianceDenominatorWindow

/-- Readiness for a Fourier-Laplace certificate. -/
def fourierLaplaceCertificateReady
    (w : FourierLaplaceCertificate) : Prop :=
  fourierLaplaceCertificateControlled w ∧
    w.certificateBudget ≤
      w.latticeWindow + w.varianceNumeratorWindow +
        w.varianceDenominatorWindow + w.slack

/-- Total size of a Fourier-Laplace certificate. -/
def fourierLaplaceCertificateSize
    (w : FourierLaplaceCertificate) : ℕ :=
  w.latticeWindow + w.varianceNumeratorWindow +
    w.varianceDenominatorWindow + w.certificateBudget + w.slack

theorem fourierLaplaceCertificate_budget_le_size
    (w : FourierLaplaceCertificate)
    (h : fourierLaplaceCertificateReady w) :
    w.certificateBudget ≤ fourierLaplaceCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold fourierLaplaceCertificateSize
  omega

def sampleFourierLaplaceCertificate : FourierLaplaceCertificate where
  latticeWindow := 2
  varianceNumeratorWindow := 1
  varianceDenominatorWindow := 1
  certificateBudget := 4
  slack := 1

example :
    fourierLaplaceCertificateReady sampleFourierLaplaceCertificate := by
  norm_num [fourierLaplaceCertificateReady,
    fourierLaplaceCertificateControlled, sampleFourierLaplaceCertificate]

example :
    sampleFourierLaplaceCertificate.certificateBudget ≤
      fourierLaplaceCertificateSize sampleFourierLaplaceCertificate := by
  apply fourierLaplaceCertificate_budget_le_size
  norm_num [fourierLaplaceCertificateReady,
    fourierLaplaceCertificateControlled, sampleFourierLaplaceCertificate]

/-- A refinement certificate separating the comparison budget from the parameter windows. -/
structure FourierLaplaceRefinementCertificate where
  latticeWindow : ℕ
  varianceNumeratorWindow : ℕ
  varianceDenominatorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def FourierLaplaceRefinementCertificate.parametersControlled
    (cert : FourierLaplaceRefinementCertificate) : Prop :=
  0 < cert.latticeWindow ∧
    0 < cert.varianceNumeratorWindow ∧
      0 < cert.varianceDenominatorWindow

def FourierLaplaceRefinementCertificate.budgetControlled
    (cert : FourierLaplaceRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.latticeWindow + cert.varianceNumeratorWindow +
      cert.varianceDenominatorWindow + cert.slack

def fourierLaplaceRefinementReady
    (cert : FourierLaplaceRefinementCertificate) : Prop :=
  cert.parametersControlled ∧ cert.budgetControlled

def FourierLaplaceRefinementCertificate.size
    (cert : FourierLaplaceRefinementCertificate) : ℕ :=
  cert.latticeWindow + cert.varianceNumeratorWindow +
    cert.varianceDenominatorWindow + cert.slack

theorem fourierLaplace_certificateBudgetWindow_le_size
    (cert : FourierLaplaceRefinementCertificate)
    (h : fourierLaplaceRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFourierLaplaceRefinementCertificate :
    FourierLaplaceRefinementCertificate where
  latticeWindow := 2
  varianceNumeratorWindow := 1
  varianceDenominatorWindow := 1
  certificateBudgetWindow := 5
  slack := 1

example :
    fourierLaplaceRefinementReady sampleFourierLaplaceRefinementCertificate := by
  norm_num [fourierLaplaceRefinementReady,
    FourierLaplaceRefinementCertificate.parametersControlled,
    FourierLaplaceRefinementCertificate.budgetControlled,
    sampleFourierLaplaceRefinementCertificate]

example :
    sampleFourierLaplaceRefinementCertificate.certificateBudgetWindow ≤
      sampleFourierLaplaceRefinementCertificate.size := by
  apply fourierLaplace_certificateBudgetWindow_le_size
  norm_num [fourierLaplaceRefinementReady,
    FourierLaplaceRefinementCertificate.parametersControlled,
    FourierLaplaceRefinementCertificate.budgetControlled,
    sampleFourierLaplaceRefinementCertificate]

structure FourierLaplaceBudgetCertificate where
  latticeWindow : ℕ
  varianceNumeratorWindow : ℕ
  varianceDenominatorWindow : ℕ
  comparisonBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FourierLaplaceBudgetCertificate.controlled
    (c : FourierLaplaceBudgetCertificate) : Prop :=
  0 < c.latticeWindow ∧
    0 < c.varianceNumeratorWindow ∧
      0 < c.varianceDenominatorWindow ∧
        c.comparisonBudgetWindow ≤
          c.latticeWindow + c.varianceNumeratorWindow +
            c.varianceDenominatorWindow + c.slack

def FourierLaplaceBudgetCertificate.budgetControlled
    (c : FourierLaplaceBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.latticeWindow + c.varianceNumeratorWindow +
      c.varianceDenominatorWindow + c.comparisonBudgetWindow + c.slack

def FourierLaplaceBudgetCertificate.Ready
    (c : FourierLaplaceBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FourierLaplaceBudgetCertificate.size
    (c : FourierLaplaceBudgetCertificate) : ℕ :=
  c.latticeWindow + c.varianceNumeratorWindow +
    c.varianceDenominatorWindow + c.comparisonBudgetWindow + c.slack

theorem fourierLaplace_budgetCertificate_le_size
    (c : FourierLaplaceBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFourierLaplaceBudgetCertificate :
    FourierLaplaceBudgetCertificate :=
  { latticeWindow := 2
    varianceNumeratorWindow := 1
    varianceDenominatorWindow := 1
    comparisonBudgetWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleFourierLaplaceBudgetCertificate.Ready := by
  constructor
  · norm_num [FourierLaplaceBudgetCertificate.controlled,
      sampleFourierLaplaceBudgetCertificate]
  · norm_num [FourierLaplaceBudgetCertificate.budgetControlled,
      sampleFourierLaplaceBudgetCertificate]

example :
    sampleFourierLaplaceBudgetCertificate.certificateBudgetWindow ≤
      sampleFourierLaplaceBudgetCertificate.size := by
  apply fourierLaplace_budgetCertificate_le_size
  constructor
  · norm_num [FourierLaplaceBudgetCertificate.controlled,
      sampleFourierLaplaceBudgetCertificate]
  · norm_num [FourierLaplaceBudgetCertificate.budgetControlled,
      sampleFourierLaplaceBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFourierLaplaceBudgetCertificate.Ready := by
  constructor
  · norm_num [FourierLaplaceBudgetCertificate.controlled,
      sampleFourierLaplaceBudgetCertificate]
  · norm_num [FourierLaplaceBudgetCertificate.budgetControlled,
      sampleFourierLaplaceBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFourierLaplaceBudgetCertificate.certificateBudgetWindow ≤
      sampleFourierLaplaceBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FourierLaplaceBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFourierLaplaceBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFourierLaplaceBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.FourierLaplace
