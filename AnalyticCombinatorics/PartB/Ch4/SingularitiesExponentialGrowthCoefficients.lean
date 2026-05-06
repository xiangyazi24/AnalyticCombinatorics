import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Singularities and exponential growth of coefficients.
-/

namespace AnalyticCombinatorics.PartB.Ch4.SingularitiesExponentialGrowthCoefficients

/-- Coefficient model controlled by a dominant singularity of reciprocal radius. -/
def exponentialCoefficientModel (growth n : ℕ) : ℕ :=
  growth ^ n

/-- Finite exponential-growth envelope for coefficients. -/
def exponentialGrowthEnvelopeCheck
    (coeff : ℕ → ℕ) (growth N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => coeff n ≤ growth ^ n

/-- Finite statement form for the exponential-growth theorem. -/
def ExponentialGrowthCoefficientWindow
    (coeff : ℕ → ℕ) (growth N : ℕ) : Prop :=
  0 < growth ∧ exponentialGrowthEnvelopeCheck coeff growth N = true

theorem geometric_exponentialGrowthWindow :
    ExponentialGrowthCoefficientWindow (exponentialCoefficientModel 3) 3 16 := by
  constructor
  · norm_num
  · unfold exponentialGrowthEnvelopeCheck exponentialCoefficientModel
    native_decide

theorem exponentialCoefficientModel_samples :
    exponentialCoefficientModel 3 0 = 1 ∧
    exponentialCoefficientModel 3 1 = 3 ∧
    exponentialCoefficientModel 3 2 = 9 ∧
    exponentialCoefficientModel 3 3 = 27 := by
  unfold exponentialCoefficientModel
  native_decide

/-- Finite constant-ratio audit for coefficients with exponential growth. -/
def exponentialCoefficientRatioCheck (growth N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    exponentialCoefficientModel growth (n + 1) =
      growth * exponentialCoefficientModel growth n

theorem exponentialCoefficient_ratioWindow :
    exponentialCoefficientRatioCheck 4 16 = true := by
  unfold exponentialCoefficientRatioCheck exponentialCoefficientModel
  native_decide

structure SingularitiesExponentialGrowthCoefficientsBudgetCertificate where
  singularityWindow : ℕ
  growthWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularitiesExponentialGrowthCoefficientsBudgetCertificate.controlled
    (c : SingularitiesExponentialGrowthCoefficientsBudgetCertificate) : Prop :=
  0 < c.singularityWindow ∧
    c.coefficientWindow ≤ c.singularityWindow + c.growthWindow + c.slack

def SingularitiesExponentialGrowthCoefficientsBudgetCertificate.budgetControlled
    (c : SingularitiesExponentialGrowthCoefficientsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.singularityWindow + c.growthWindow + c.coefficientWindow + c.slack

def SingularitiesExponentialGrowthCoefficientsBudgetCertificate.Ready
    (c : SingularitiesExponentialGrowthCoefficientsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularitiesExponentialGrowthCoefficientsBudgetCertificate.size
    (c : SingularitiesExponentialGrowthCoefficientsBudgetCertificate) : ℕ :=
  c.singularityWindow + c.growthWindow + c.coefficientWindow + c.slack

theorem singularitiesExponentialGrowthCoefficients_budgetCertificate_le_size
    (c : SingularitiesExponentialGrowthCoefficientsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSingularitiesExponentialGrowthCoefficientsBudgetCertificate :
    SingularitiesExponentialGrowthCoefficientsBudgetCertificate :=
  { singularityWindow := 5
    growthWindow := 6
    coefficientWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example :
    sampleSingularitiesExponentialGrowthCoefficientsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [SingularitiesExponentialGrowthCoefficientsBudgetCertificate.controlled,
        sampleSingularitiesExponentialGrowthCoefficientsBudgetCertificate]
  · norm_num
      [SingularitiesExponentialGrowthCoefficientsBudgetCertificate.budgetControlled,
        sampleSingularitiesExponentialGrowthCoefficientsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleSingularitiesExponentialGrowthCoefficientsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularitiesExponentialGrowthCoefficientsBudgetCertificate.controlled,
      sampleSingularitiesExponentialGrowthCoefficientsBudgetCertificate]
  · norm_num [SingularitiesExponentialGrowthCoefficientsBudgetCertificate.budgetControlled,
      sampleSingularitiesExponentialGrowthCoefficientsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularitiesExponentialGrowthCoefficientsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularitiesExponentialGrowthCoefficientsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List SingularitiesExponentialGrowthCoefficientsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularitiesExponentialGrowthCoefficientsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSingularitiesExponentialGrowthCoefficientsBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleSingularitiesExponentialGrowthCoefficientsBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch4.SingularitiesExponentialGrowthCoefficients
