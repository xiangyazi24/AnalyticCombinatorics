import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Concepts of probability theory
-/

namespace AnalyticCombinatorics.AppC.ConceptsOfProbabilityTheory

/-- Finite probability mass model on the prefix `0, ..., N`. -/
def probabilityMassTotal (mass : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl (fun total k => total + mass k) 0

def finiteDistributionReady (mass : ℕ → ℚ) (N : ℕ) : Prop :=
  probabilityMassTotal mass N = 1 ∧
    (List.range (N + 1)).all (fun k => 0 ≤ mass k) = true

def pointMassZero : ℕ → ℚ
  | 0 => 1
  | _ => 0

theorem pointMassZero_ready :
    finiteDistributionReady pointMassZero 4 := by
  unfold finiteDistributionReady probabilityMassTotal pointMassZero
  native_decide

/-- Finite expectation over a sampled support. -/
def finiteExpectation (mass : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun total (k : ℕ) => total + (k : ℚ) * mass k) 0

theorem pointMassZero_expectation :
    finiteExpectation pointMassZero 4 = 0 := by
  unfold finiteExpectation pointMassZero
  native_decide

def bernoulliHalfMass : ℕ → ℚ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | _ => 0

theorem bernoulliHalf_ready :
    finiteDistributionReady bernoulliHalfMass 4 := by
  unfold finiteDistributionReady probabilityMassTotal bernoulliHalfMass
  native_decide

theorem bernoulliHalf_expectation :
    finiteExpectation bernoulliHalfMass 4 = 1 / 2 := by
  unfold finiteExpectation bernoulliHalfMass
  native_decide

example : probabilityMassTotal bernoulliHalfMass 1 = 1 := by
  unfold probabilityMassTotal bernoulliHalfMass
  native_decide

example : finiteExpectation bernoulliHalfMass 1 = 1 / 2 := by
  unfold finiteExpectation bernoulliHalfMass
  native_decide

structure BudgetCertificate where
  probabilityWindow : ℕ
  distributionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.probabilityWindow ∧
    c.distributionWindow ≤ c.probabilityWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.probabilityWindow + c.distributionWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.probabilityWindow + c.distributionWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { probabilityWindow := 5, distributionWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ConceptsOfProbabilityTheory
