import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Labelled structures and exponential generating functions
-/

namespace AnalyticCombinatorics.PartA.Ch2.LabelledStructuresAndExponentialGeneratingFunctions

/-- Labelled object counts are read as EGF numerators. -/
def egfNumerator (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  a n

/-- EGF denominator at size `n`. -/
def egfDenominator (n : ℕ) : ℕ :=
  Nat.factorial n

theorem egfDenominator_zero :
    egfDenominator 0 = 1 := by
  simp [egfDenominator]

theorem egfDenominator_succ (n : ℕ) :
    egfDenominator (n + 1) = (n + 1) * egfDenominator n := by
  simp [egfDenominator, Nat.factorial_succ]

/-- Product of labelled classes: binomial convolution of labelled counts. -/
def labelledProductCount (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl
    (fun total k => total + n.choose k * a k * b (n - k)) 0

theorem labelledProductCount_zero (a b : ℕ → ℕ) :
    labelledProductCount a b 0 = a 0 * b 0 := by
  simp [labelledProductCount]

theorem labelledProductCount_const_one_samples :
    labelledProductCount (fun _ => 1) (fun _ => 1) 3 = 8 := by
  unfold labelledProductCount
  native_decide

structure BudgetCertificate where
  labelledWindow : ℕ
  egfWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.labelledWindow ∧ c.egfWindow ≤ c.labelledWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.labelledWindow + c.egfWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.labelledWindow + c.egfWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { labelledWindow := 5, egfWindow := 6, certificateBudgetWindow := 12,
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

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

end AnalyticCombinatorics.PartA.Ch2.LabelledStructuresAndExponentialGeneratingFunctions
