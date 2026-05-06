import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Simple varieties of trees and inverse functions
-/

namespace AnalyticCombinatorics.PartB.Ch7.SimpleVarietiesOfTreesAndInverseFunctions

/-- Critical data for a simple variety of trees `T = z phi(T)`. -/
structure SimpleTreeCriticalData where
  characteristicValue : ℕ
  derivativeWeight : ℕ
  singularScale : ℕ
deriving DecidableEq, Repr

def SimpleTreeCriticalData.balanced
    (d : SimpleTreeCriticalData) : Prop :=
  d.derivativeWeight ≤ d.characteristicValue + d.singularScale

theorem simpleTreeCriticalData_sample_balanced :
    ({ characteristicValue := 2, derivativeWeight := 5,
       singularScale := 3 } : SimpleTreeCriticalData).balanced := by
  norm_num [SimpleTreeCriticalData.balanced]

/-- Catalan model for the inverse-function tree schema. -/
def inverseTreeCatalan (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

theorem inverseTreeCatalan_four :
    inverseTreeCatalan 4 = 14 := by
  native_decide

structure TreeInverseWindow where
  treeWindow : ℕ
  inverseWindow : ℕ
  singularWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TreeInverseWindow.ready (w : TreeInverseWindow) : Prop :=
  0 < w.treeWindow ∧
    w.inverseWindow ≤ w.treeWindow + w.singularWindow + w.slack

def sampleTreeInverseWindow : TreeInverseWindow :=
  { treeWindow := 4, inverseWindow := 7, singularWindow := 3, slack := 0 }

example : sampleTreeInverseWindow.ready := by
  norm_num [TreeInverseWindow.ready, sampleTreeInverseWindow]

structure BudgetCertificate where
  treeWindow : ℕ
  inverseWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.treeWindow ∧ c.inverseWindow ≤ c.treeWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.treeWindow + c.inverseWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.treeWindow + c.inverseWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { treeWindow := 5, inverseWindow := 6,
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

end AnalyticCombinatorics.PartB.Ch7.SimpleVarietiesOfTreesAndInverseFunctions
