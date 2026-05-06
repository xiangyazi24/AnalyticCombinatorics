import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Singularities and exponential growth of coefficients

Finite dominant-singularity and exponential-envelope certificates.
-/

namespace AnalyticCombinatorics.PartB.Ch4.SingularitiesAndExponentialGrowthCoefficients

def exponentialEnvelope (base n : ℕ) : ℕ :=
  base ^ n

theorem exponentialEnvelope_zero (base : ℕ) :
    exponentialEnvelope base 0 = 1 := by
  simp [exponentialEnvelope]

theorem exponentialEnvelope_succ (base n : ℕ) :
    exponentialEnvelope base (n + 1) =
      base * exponentialEnvelope base n := by
  simp [exponentialEnvelope, pow_succ, Nat.mul_comm]

def coefficientBelowEnvelope
    (coeff : ℕ → ℕ) (base N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => coeff n ≤ exponentialEnvelope base n

theorem coefficientBelowEnvelope_geometric :
    coefficientBelowEnvelope (exponentialEnvelope 2) 2 12 = true := by
  unfold coefficientBelowEnvelope exponentialEnvelope
  native_decide

def coefficientEnvelopeProduct (baseA baseB n : ℕ) : ℕ :=
  exponentialEnvelope (baseA * baseB) n

theorem coefficientEnvelopeProduct_eq (baseA baseB n : ℕ) :
    coefficientEnvelopeProduct baseA baseB n =
      exponentialEnvelope baseA n * exponentialEnvelope baseB n := by
  simp [coefficientEnvelopeProduct, exponentialEnvelope, mul_pow]

structure DominantSingularityWindow where
  singularityWindow : ℕ
  coefficientWindow : ℕ
  growthWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DominantSingularityWindow.ready
    (w : DominantSingularityWindow) : Prop :=
  0 < w.singularityWindow ∧
    w.coefficientWindow ≤ w.growthWindow + w.slack

def sampleDominantSingularityWindow : DominantSingularityWindow :=
  { singularityWindow := 2
    coefficientWindow := 6
    growthWindow := 6
    slack := 0 }

example : sampleDominantSingularityWindow.ready := by
  norm_num [DominantSingularityWindow.ready,
    sampleDominantSingularityWindow]

def dominantSingularityWindowListReady
    (data : List DominantSingularityWindow) : Bool :=
  data.all fun w =>
    0 < w.singularityWindow &&
      w.coefficientWindow ≤ w.growthWindow + w.slack

theorem dominantSingularityWindowList_readyWindow :
    dominantSingularityWindowListReady
      [sampleDominantSingularityWindow,
       { singularityWindow := 1, coefficientWindow := 3,
         growthWindow := 4, slack := 0 }] = true := by
  unfold dominantSingularityWindowListReady
    sampleDominantSingularityWindow
  native_decide

structure SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate where
  singularityWindow : ℕ
  coefficientWindow : ℕ
  growthWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate.controlled
    (c : SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate) :
    Prop :=
  0 < c.singularityWindow ∧
    c.coefficientWindow ≤ c.growthWindow + c.slack

def SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate.budgetControlled
    (c : SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate) :
    Prop :=
  c.certificateBudgetWindow ≤
    c.singularityWindow + c.coefficientWindow + c.growthWindow + c.slack

def SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate.Ready
    (c : SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate) :
    Prop :=
  c.controlled ∧ c.budgetControlled

def SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate.size
    (c : SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate) :
    ℕ :=
  c.singularityWindow + c.coefficientWindow + c.growthWindow + c.slack

theorem singularitiesAndExponentialGrowthCoefficients_budgetCertificate_le_size
    (c : SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSingularitiesAndExponentialGrowthCoefficientsBudgetCertificate :
    SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate :=
  { singularityWindow := 2
    coefficientWindow := 6
    growthWindow := 6
    certificateBudgetWindow := 15
    slack := 1 }

example :
    sampleSingularitiesAndExponentialGrowthCoefficientsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate.controlled,
        sampleSingularitiesAndExponentialGrowthCoefficientsBudgetCertificate]
  · norm_num
      [SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate.budgetControlled,
        sampleSingularitiesAndExponentialGrowthCoefficientsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularitiesAndExponentialGrowthCoefficientsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate.controlled,
      sampleSingularitiesAndExponentialGrowthCoefficientsBudgetCertificate]
  · norm_num [SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate.budgetControlled,
      sampleSingularitiesAndExponentialGrowthCoefficientsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularitiesAndExponentialGrowthCoefficientsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularitiesAndExponentialGrowthCoefficientsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data :
      List SingularitiesAndExponentialGrowthCoefficientsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularitiesAndExponentialGrowthCoefficientsBudgetCertificate] =
        true := by
  unfold budgetCertificateListReady
    sampleSingularitiesAndExponentialGrowthCoefficientsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.SingularitiesAndExponentialGrowthCoefficients
