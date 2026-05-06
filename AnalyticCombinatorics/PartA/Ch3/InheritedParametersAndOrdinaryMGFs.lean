import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Inherited parameters and ordinary MGFs
-/

namespace AnalyticCombinatorics.PartA.Ch3.InheritedParametersAndOrdinaryMGFs

/-- Ordinary moment generating polynomial over a finite parameter support. -/
def ordinaryMGFPrefix (weights : ℕ → ℕ) (u K : ℕ) : ℕ :=
  (List.range (K + 1)).foldl (fun total k => total + weights k * u ^ k) 0

theorem ordinaryMGFPrefix_zero_support (weights : ℕ → ℕ) (u : ℕ) :
    ordinaryMGFPrefix weights u 0 = weights 0 := by
  simp [ordinaryMGFPrefix]

def inheritedAdditiveWeights (k : ℕ) : ℕ :=
  if k = 0 then 1 else if k = 1 then 2 else 0

theorem inheritedAdditiveWeights_mgf_one :
    ordinaryMGFPrefix inheritedAdditiveWeights 1 3 = 3 := by
  unfold ordinaryMGFPrefix inheritedAdditiveWeights
  native_decide

theorem inheritedAdditiveWeights_mgf_two :
    ordinaryMGFPrefix inheritedAdditiveWeights 2 3 = 5 := by
  unfold ordinaryMGFPrefix inheritedAdditiveWeights
  native_decide

structure BudgetCertificate where
  inheritedWindow : ℕ
  ordinaryMGFWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.inheritedWindow ∧ c.ordinaryMGFWindow ≤ c.inheritedWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.inheritedWindow + c.ordinaryMGFWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.inheritedWindow + c.ordinaryMGFWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { inheritedWindow := 5, ordinaryMGFWindow := 6,
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

end AnalyticCombinatorics.PartA.Ch3.InheritedParametersAndOrdinaryMGFs
