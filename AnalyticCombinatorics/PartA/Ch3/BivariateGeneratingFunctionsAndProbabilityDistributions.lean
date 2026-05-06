import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Bivariate generating functions and probability distributions
-/

namespace AnalyticCombinatorics.PartA.Ch3.BivariateGeneratingFunctionsAndProbabilityDistributions

/-- Finite probability mass at a fixed size. -/
def probabilityMassAtSize (table : ℕ → ℕ → ℕ) (n k K : ℕ) : ℚ :=
  (table n k : ℚ) /
    ((List.range (K + 1)).foldl (fun total j => total + table n j) 0 : ℚ)

def bernoulliParameterTable (_n k : ℕ) : ℕ :=
  if k = 0 then 1 else if k = 1 then 1 else 0

theorem bernoulliParameterMass_zero :
    probabilityMassAtSize bernoulliParameterTable 3 0 2 = 1 / 2 := by
  unfold probabilityMassAtSize bernoulliParameterTable
  native_decide

theorem bernoulliParameterMass_one :
    probabilityMassAtSize bernoulliParameterTable 3 1 2 = 1 / 2 := by
  unfold probabilityMassAtSize bernoulliParameterTable
  native_decide

/-- Probability normalization audit for a finite parameter range. -/
def probabilityMassTotal (table : ℕ → ℕ → ℕ) (n K : ℕ) : ℚ :=
  (List.range (K + 1)).foldl
    (fun total k => total + probabilityMassAtSize table n k K) 0

theorem bernoulliParameterMass_total :
    probabilityMassTotal bernoulliParameterTable 3 2 = 1 := by
  unfold probabilityMassTotal probabilityMassAtSize bernoulliParameterTable
  native_decide

structure BudgetCertificate where
  bivariateWindow : ℕ
  probabilityWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.bivariateWindow ∧ c.probabilityWindow ≤ c.bivariateWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.bivariateWindow + c.probabilityWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.bivariateWindow + c.probabilityWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { bivariateWindow := 5, probabilityWindow := 6,
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

end AnalyticCombinatorics.PartA.Ch3.BivariateGeneratingFunctionsAndProbabilityDistributions
