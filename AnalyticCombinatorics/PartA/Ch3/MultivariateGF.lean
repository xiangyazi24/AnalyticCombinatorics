import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multivariate generating-function coefficient schemas.
-/

namespace AnalyticCombinatorics.PartA.Ch3.MultivariateGF

structure BivariateCoefficient where
  sizeIndex : ℕ
  markIndex : ℕ
  coefficient : ℕ
deriving DecidableEq, Repr

def bivariateSupportControlled (c : BivariateCoefficient) : Prop :=
  c.markIndex ≤ c.sizeIndex + c.coefficient

def bivariateCoefficientWeight (c : BivariateCoefficient) : ℕ :=
  c.sizeIndex + c.markIndex + c.coefficient

theorem coefficient_le_weight (c : BivariateCoefficient) :
    c.coefficient ≤ bivariateCoefficientWeight c := by
  unfold bivariateCoefficientWeight
  omega

def sampleBivariateCoefficient : BivariateCoefficient :=
  { sizeIndex := 7, markIndex := 3, coefficient := 11 }

example : bivariateSupportControlled sampleBivariateCoefficient := by
  norm_num [bivariateSupportControlled, sampleBivariateCoefficient]

example : bivariateCoefficientWeight sampleBivariateCoefficient = 21 := by
  native_decide

structure MultivariateSupportWindow where
  sizeIndex : ℕ
  firstMark : ℕ
  secondMark : ℕ
  coefficientBound : ℕ
deriving DecidableEq, Repr

def MultivariateSupportWindow.markTotal (w : MultivariateSupportWindow) : ℕ :=
  w.firstMark + w.secondMark

def MultivariateSupportWindow.supportReady (w : MultivariateSupportWindow) : Prop :=
  w.markTotal ≤ w.sizeIndex + w.coefficientBound

def MultivariateSupportWindow.diagonalReady (w : MultivariateSupportWindow) : Prop :=
  w.firstMark = w.secondMark

def MultivariateSupportWindow.certificate (w : MultivariateSupportWindow) : ℕ :=
  w.sizeIndex + w.firstMark + w.secondMark + w.coefficientBound

theorem markTotal_le_certificate (w : MultivariateSupportWindow) :
    w.markTotal ≤ w.certificate := by
  unfold MultivariateSupportWindow.markTotal MultivariateSupportWindow.certificate
  omega

def sampleMultivariateSupportWindow : MultivariateSupportWindow :=
  { sizeIndex := 8, firstMark := 3, secondMark := 3, coefficientBound := 5 }

example : sampleMultivariateSupportWindow.supportReady := by
  norm_num [sampleMultivariateSupportWindow, MultivariateSupportWindow.supportReady,
    MultivariateSupportWindow.markTotal]

example : sampleMultivariateSupportWindow.diagonalReady := by
  norm_num [sampleMultivariateSupportWindow, MultivariateSupportWindow.diagonalReady]


structure MultivariateGFBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultivariateGFBudgetCertificate.controlled
    (c : MultivariateGFBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MultivariateGFBudgetCertificate.budgetControlled
    (c : MultivariateGFBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MultivariateGFBudgetCertificate.Ready
    (c : MultivariateGFBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultivariateGFBudgetCertificate.size
    (c : MultivariateGFBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem multivariateGF_budgetCertificate_le_size
    (c : MultivariateGFBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMultivariateGFBudgetCertificate :
    MultivariateGFBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMultivariateGFBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivariateGFBudgetCertificate.controlled,
      sampleMultivariateGFBudgetCertificate]
  · norm_num [MultivariateGFBudgetCertificate.budgetControlled,
      sampleMultivariateGFBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultivariateGFBudgetCertificate.certificateBudgetWindow ≤
      sampleMultivariateGFBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMultivariateGFBudgetCertificate.Ready := by
  constructor
  · norm_num [MultivariateGFBudgetCertificate.controlled,
      sampleMultivariateGFBudgetCertificate]
  · norm_num [MultivariateGFBudgetCertificate.budgetControlled,
      sampleMultivariateGFBudgetCertificate]

example :
    sampleMultivariateGFBudgetCertificate.certificateBudgetWindow ≤
      sampleMultivariateGFBudgetCertificate.size := by
  apply multivariateGF_budgetCertificate_le_size
  constructor
  · norm_num [MultivariateGFBudgetCertificate.controlled,
      sampleMultivariateGFBudgetCertificate]
  · norm_num [MultivariateGFBudgetCertificate.budgetControlled,
      sampleMultivariateGFBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MultivariateGFBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultivariateGFBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMultivariateGFBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.MultivariateGF
