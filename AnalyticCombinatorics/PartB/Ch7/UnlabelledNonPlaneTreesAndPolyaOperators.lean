import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Unlabelled non-plane trees and Polya operators
-/

namespace AnalyticCombinatorics.PartB.Ch7.UnlabelledNonPlaneTreesAndPolyaOperators

/-- Finite Polya operator term for an unlabelled tree model. -/
structure PolyaOperatorTerm where
  orbitSize : ℕ
  substitutionArity : ℕ
  weight : ℕ
deriving DecidableEq, Repr

def PolyaOperatorTerm.valid (t : PolyaOperatorTerm) : Prop :=
  0 < t.orbitSize ∧ 0 < t.substitutionArity

theorem polyaOperatorTerm_sample_valid :
    ({ orbitSize := 2, substitutionArity := 3,
       weight := 5 } : PolyaOperatorTerm).valid := by
  norm_num [PolyaOperatorTerm.valid]

/-- Cleared contribution of a finite Polya operator term. -/
def polyaOperatorContribution (orbitSize weight : ℕ) : ℕ :=
  orbitSize * weight

theorem polyaOperatorContribution_sample :
    polyaOperatorContribution 2 5 = 10 := by
  native_decide

structure PolyaTreeWindow where
  treeWindow : ℕ
  orbitWindow : ℕ
  operatorWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PolyaTreeWindow.ready (w : PolyaTreeWindow) : Prop :=
  0 < w.treeWindow ∧
    w.operatorWindow ≤ w.treeWindow + w.orbitWindow + w.slack

def samplePolyaTreeWindow : PolyaTreeWindow :=
  { treeWindow := 4, orbitWindow := 3, operatorWindow := 7, slack := 0 }

example : samplePolyaTreeWindow.ready := by
  norm_num [PolyaTreeWindow.ready, samplePolyaTreeWindow]

structure BudgetCertificate where
  treeWindow : ℕ
  operatorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.treeWindow ∧ c.operatorWindow ≤ c.treeWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.treeWindow + c.operatorWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.treeWindow + c.operatorWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { treeWindow := 5, operatorWindow := 6,
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

end AnalyticCombinatorics.PartB.Ch7.UnlabelledNonPlaneTreesAndPolyaOperators
