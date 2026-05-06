import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Combinatorial parameters and multivariate generating functions
-/

namespace AnalyticCombinatorics.PartA.Ch3.CombinatorialParametersAndMultivariateGeneratingFunctions

/-- Bivariate coefficient table for size and parameter value. -/
def bivariateCoeff (a : ℕ → ℕ → ℕ) (n k : ℕ) : ℕ :=
  a n k

/-- Marginal size count obtained by summing a finite parameter range. -/
def parameterMarginal (a : ℕ → ℕ → ℕ) (n K : ℕ) : ℕ :=
  (List.range (K + 1)).foldl (fun total k => total + a n k) 0

theorem parameterMarginal_zero_range (a : ℕ → ℕ → ℕ) (n : ℕ) :
    parameterMarginal a n 0 = a n 0 := by
  simp [parameterMarginal]

/-- First parameter moment over a finite range. -/
def parameterFirstMoment (a : ℕ → ℕ → ℕ) (n K : ℕ) : ℕ :=
  (List.range (K + 1)).foldl (fun total k => total + k * a n k) 0

def singleParameterAtSize (n k : ℕ) : ℕ :=
  if k = n then 1 else 0

theorem singleParameter_marginal :
    parameterMarginal singleParameterAtSize 4 6 = 1 := by
  unfold parameterMarginal singleParameterAtSize
  native_decide

theorem singleParameter_firstMoment :
    parameterFirstMoment singleParameterAtSize 4 6 = 4 := by
  unfold parameterFirstMoment singleParameterAtSize
  native_decide

structure BudgetCertificate where
  parameterWindow : ℕ
  multivariateWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.parameterWindow ∧
    c.multivariateWindow ≤ c.parameterWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.parameterWindow + c.multivariateWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.parameterWindow + c.multivariateWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { parameterWindow := 5, multivariateWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

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

end AnalyticCombinatorics.PartA.Ch3.CombinatorialParametersAndMultivariateGeneratingFunctions
