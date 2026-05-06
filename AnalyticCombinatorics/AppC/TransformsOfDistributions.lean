import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Transforms of distributions
-/

namespace AnalyticCombinatorics.AppC.TransformsOfDistributions

/-- Probability generating function prefix. -/
def pgfPrefix (mass : ℕ → ℚ) (z : ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun total k => total + mass k * z ^ k) 0

def pointMassZero : ℕ → ℚ
  | 0 => 1
  | _ => 0

theorem pgfPrefix_pointMassZero_sample :
    pgfPrefix pointMassZero 3 4 = 1 := by
  unfold pgfPrefix pointMassZero
  native_decide

def bernoulliHalfMass : ℕ → ℚ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | _ => 0

theorem pgfPrefix_bernoulliHalf_one :
    pgfPrefix bernoulliHalfMass 1 4 = 1 := by
  unfold pgfPrefix bernoulliHalfMass
  native_decide

theorem pgfPrefix_bernoulliHalf_zero :
    pgfPrefix bernoulliHalfMass 0 4 = 1 / 2 := by
  unfold pgfPrefix bernoulliHalfMass
  native_decide

/-- Moment certificate from the first derivative at one for finite supports. -/
def firstMomentPrefix (mass : ℕ → ℚ) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun total (k : ℕ) => total + (k : ℚ) * mass k) 0

theorem firstMoment_bernoulliHalf :
    firstMomentPrefix bernoulliHalfMass 4 = 1 / 2 := by
  unfold firstMomentPrefix bernoulliHalfMass
  native_decide

structure BudgetCertificate where
  transformWindow : ℕ
  distributionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.transformWindow ∧
    c.distributionWindow ≤ c.transformWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.transformWindow + c.distributionWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.transformWindow + c.distributionWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { transformWindow := 5, distributionWindow := 6,
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

example :
    budgetCertificateListReady
      [sampleBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.AppC.TransformsOfDistributions
