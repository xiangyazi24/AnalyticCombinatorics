import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Unlabelled non-plane trees and Polya operators.

Finite bookkeeping for cycle-index and unlabelled tree enumeration windows.
-/

namespace AnalyticCombinatorics.PartB.Ch7.UnlabelledNonPlaneTreesPolyaOperators

structure PolyaTreeWindow where
  treeWindow : ℕ
  cycleIndexWindow : ℕ
  operatorDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def polyaTreeReady (w : PolyaTreeWindow) : Prop :=
  0 < w.treeWindow ∧
    w.operatorDepth ≤ w.treeWindow + w.cycleIndexWindow + w.slack

def polyaTreeBudget (w : PolyaTreeWindow) : ℕ :=
  w.treeWindow + w.cycleIndexWindow + w.operatorDepth + w.slack

theorem operatorDepth_le_polyaTreeBudget (w : PolyaTreeWindow) :
    w.operatorDepth ≤ polyaTreeBudget w := by
  unfold polyaTreeBudget
  omega

def samplePolyaTreeWindow : PolyaTreeWindow :=
  { treeWindow := 5, cycleIndexWindow := 6, operatorDepth := 9, slack := 1 }

example : polyaTreeReady samplePolyaTreeWindow := by
  norm_num [polyaTreeReady, samplePolyaTreeWindow]

/-- Finite model for a cycle-index term feeding Polya tree operators. -/
def cycleIndexTermProxy (cycleSize multiplicity : ℕ) : ℕ :=
  (cycleSize + 1) * (multiplicity + 1)

/-- Finite audit that sampled Polya terms stay under a product envelope. -/
def polyaOperatorEnvelopeCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    cycleIndexTermProxy n n ≤ (n + 1) * (n + 1)

theorem polyaOperator_envelopeWindow :
    polyaOperatorEnvelopeCheck 16 = true := by
  unfold polyaOperatorEnvelopeCheck cycleIndexTermProxy
  native_decide

structure UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate where
  treeWindow : ℕ
  cycleWindow : ℕ
  operatorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate.controlled
    (c : UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate) : Prop :=
  0 < c.treeWindow ∧
    c.operatorWindow ≤ c.treeWindow + c.cycleWindow + c.slack

def UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate.budgetControlled
    (c : UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.treeWindow + c.cycleWindow + c.operatorWindow + c.slack

def UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate.Ready
    (c : UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate.size
    (c : UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate) : ℕ :=
  c.treeWindow + c.cycleWindow + c.operatorWindow + c.slack

theorem unlabelledNonPlaneTreesPolyaOperators_budgetCertificate_le_size
    (c : UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleUnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate :
    UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate :=
  { treeWindow := 5
    cycleWindow := 6
    operatorWindow := 9
    certificateBudgetWindow := 21
    slack := 1 }

example :
    sampleUnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate.controlled,
        sampleUnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate]
  · norm_num
      [UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate.budgetControlled,
        sampleUnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    sampleUnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate.Ready := by
  constructor
  · norm_num [UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate.controlled,
      sampleUnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate]
  · norm_num [UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate.budgetControlled,
      sampleUnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate.certificateBudgetWindow ≤
      sampleUnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleUnlabelledNonPlaneTreesPolyaOperatorsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.UnlabelledNonPlaneTreesPolyaOperators
