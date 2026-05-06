import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Singularity analysis and probability distributions
-/

namespace AnalyticCombinatorics.PartB.Ch7.SingularityAnalysisAndProbabilityDistributions

/-- Moment data extracted from a singular expansion. -/
structure SingularityMomentData where
  mass : ℕ
  firstMoment : ℕ
  secondMoment : ℕ
deriving DecidableEq, Repr

def SingularityMomentData.varianceNumerator
    (d : SingularityMomentData) : ℕ :=
  d.mass * d.secondMoment - d.firstMoment ^ 2

theorem singularityMomentData_sample_variance :
    ({ mass := 6, firstMoment := 9,
       secondMoment := 15 } : SingularityMomentData).varianceNumerator = 9 := by
  native_decide

/-- Probability-transfer readiness after clearing denominators. -/
def probabilityTransferReady (mass momentWindow : ℕ) : Bool :=
  0 < mass && momentWindow ≤ mass * mass

theorem probabilityTransferReady_sample :
    probabilityTransferReady 6 15 = true := by
  native_decide

structure ProbabilityTransferWindow where
  singularityWindow : ℕ
  momentWindow : ℕ
  distributionWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProbabilityTransferWindow.ready (w : ProbabilityTransferWindow) : Prop :=
  0 < w.singularityWindow ∧
    w.distributionWindow ≤ w.singularityWindow + w.momentWindow + w.slack

def sampleProbabilityTransferWindow : ProbabilityTransferWindow :=
  { singularityWindow := 4, momentWindow := 3,
    distributionWindow := 7, slack := 0 }

example : sampleProbabilityTransferWindow.ready := by
  norm_num [ProbabilityTransferWindow.ready, sampleProbabilityTransferWindow]

structure BudgetCertificate where
  singularityWindow : ℕ
  distributionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.singularityWindow ∧
    c.distributionWindow ≤ c.singularityWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.singularityWindow + c.distributionWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.singularityWindow + c.distributionWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { singularityWindow := 5, distributionWindow := 6,
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

end AnalyticCombinatorics.PartB.Ch7.SingularityAnalysisAndProbabilityDistributions
