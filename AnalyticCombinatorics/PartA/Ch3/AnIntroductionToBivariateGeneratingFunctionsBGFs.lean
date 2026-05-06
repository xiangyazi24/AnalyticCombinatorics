import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# An introduction to bivariate generating functions (BGFs)
-/

namespace AnalyticCombinatorics.PartA.Ch3.AnIntroductionToBivariateGeneratingFunctionsBGFs

/-- A coefficient of `z^n u^k` in a bivariate generating function. -/
structure BivariateCoeff where
  size : ℕ
  parameter : ℕ
  value : ℕ
deriving DecidableEq, Repr

def BivariateCoeff.matches (c : BivariateCoeff) (n k : ℕ) : Bool :=
  c.size == n && c.parameter == k

theorem bivariateCoeff_matches_self (c : BivariateCoeff) :
    c.matches c.size c.parameter = true := by
  unfold BivariateCoeff.matches
  simp

/-- Marginal count at a fixed size from an explicit finite coefficient table. -/
def bivariateMarginalAtSize (n : ℕ) (data : List BivariateCoeff) : ℕ :=
  data.foldl
    (fun acc c => if c.size = n then acc + c.value else acc) 0

theorem bivariateMarginalAtSize_sample :
    bivariateMarginalAtSize 3
      [{ size := 3, parameter := 0, value := 2 },
       { size := 3, parameter := 1, value := 5 },
       { size := 4, parameter := 0, value := 11 }] = 7 := by
  native_decide

/-- First parameter moment at a fixed size from a finite BGF coefficient table. -/
def bivariateFirstMomentNumerator (n : ℕ) (data : List BivariateCoeff) : ℕ :=
  data.foldl
    (fun acc c => if c.size = n then acc + c.parameter * c.value else acc) 0

theorem bivariateFirstMomentNumerator_sample :
    bivariateFirstMomentNumerator 3
      [{ size := 3, parameter := 0, value := 2 },
       { size := 3, parameter := 2, value := 5 },
       { size := 4, parameter := 1, value := 11 }] = 10 := by
  native_decide

structure BudgetCertificate where
  sizeVariableWindow : ℕ
  parameterVariableWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.sizeVariableWindow ∧
    c.parameterVariableWindow ≤ c.sizeVariableWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.sizeVariableWindow + c.parameterVariableWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.sizeVariableWindow + c.parameterVariableWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { sizeVariableWindow := 5, parameterVariableWindow := 6,
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

end AnalyticCombinatorics.PartA.Ch3.AnIntroductionToBivariateGeneratingFunctionsBGFs
