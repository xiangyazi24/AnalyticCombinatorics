import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Saddle-points and probability distributions
-/

namespace AnalyticCombinatorics.PartB.Ch8.SaddlePointsAndProbabilityDistributions

/-- Moment data delivered by a saddle-point approximation. -/
structure SaddleMomentData where
  mass : ℕ
  meanNumerator : ℕ
  varianceNumerator : ℕ
deriving DecidableEq, Repr

def SaddleMomentData.usable (d : SaddleMomentData) : Prop :=
  0 < d.mass ∧ d.varianceNumerator ≤ d.mass ^ 2

theorem saddleMomentData_sample_usable :
    ({ mass := 6, meanNumerator := 9,
       varianceNumerator := 12 } : SaddleMomentData).usable := by
  norm_num [SaddleMomentData.usable]

/-- Cleared Gaussian scale from mass and variance numerators. -/
def saddleGaussianScale (mass varianceNumerator : ℕ) : ℕ :=
  mass + varianceNumerator

theorem saddleGaussianScale_sample :
    saddleGaussianScale 6 12 = 18 := by
  native_decide

structure SaddleProbabilityWindow where
  saddleWindow : ℕ
  momentWindow : ℕ
  distributionWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleProbabilityWindow.ready (w : SaddleProbabilityWindow) : Prop :=
  0 < w.saddleWindow ∧
    w.distributionWindow ≤ w.saddleWindow + w.momentWindow + w.slack

def sampleSaddleProbabilityWindow : SaddleProbabilityWindow :=
  { saddleWindow := 4, momentWindow := 3,
    distributionWindow := 7, slack := 0 }

example : sampleSaddleProbabilityWindow.ready := by
  norm_num [SaddleProbabilityWindow.ready, sampleSaddleProbabilityWindow]

structure BudgetCertificate where
  saddleWindow : ℕ
  distributionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.saddleWindow ∧ c.distributionWindow ≤ c.saddleWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.saddleWindow + c.distributionWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.saddleWindow + c.distributionWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { saddleWindow := 5, distributionWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  have h : sampleBudgetCertificate.Ready := by
    constructor
    · norm_num [BudgetCertificate.controlled,
        sampleBudgetCertificate]
    · norm_num [BudgetCertificate.budgetControlled,
        sampleBudgetCertificate]
  exact h.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.SaddlePointsAndProbabilityDistributions
