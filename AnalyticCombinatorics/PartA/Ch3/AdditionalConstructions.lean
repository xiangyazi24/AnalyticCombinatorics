import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Additional constructions
-/

namespace AnalyticCombinatorics.PartA.Ch3.AdditionalConstructions

/-- Additive inherited parameter on a finite product construction. -/
def inheritedParameterProduct (left right : ℕ) : ℕ :=
  left + right

theorem inheritedParameterProduct_comm (left right : ℕ) :
    inheritedParameterProduct left right =
      inheritedParameterProduct right left := by
  unfold inheritedParameterProduct
  omega

/-- Marking transform for a parameter tracked by a size count and a total weight. -/
structure MarkedClass where
  objects : ℕ
  totalWeight : ℕ
deriving DecidableEq, Repr

def MarkedClass.meanNumerator (c : MarkedClass) : ℕ :=
  c.totalWeight

def MarkedClass.meanDenominator (c : MarkedClass) : ℕ :=
  c.objects

theorem markedClass_sample_mean_data :
    ({ objects := 6, totalWeight := 14 } : MarkedClass).meanNumerator = 14 ∧
      ({ objects := 6, totalWeight := 14 } : MarkedClass).meanDenominator = 6 := by
  native_decide

/-- Finite substitution of a parameter count into an outer construction. -/
def parameterSubstitutionCount (outer inner : ℕ) : ℕ :=
  outer * inner

theorem parameterSubstitutionCount_sample :
    parameterSubstitutionCount 7 5 = 35 := by
  native_decide

structure BudgetCertificate where
  constructionWindow : ℕ
  parameterWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.constructionWindow ∧
    c.parameterWindow ≤ c.constructionWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.constructionWindow + c.parameterWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.constructionWindow + c.parameterWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { constructionWindow := 5, parameterWindow := 6,
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

end AnalyticCombinatorics.PartA.Ch3.AdditionalConstructions
