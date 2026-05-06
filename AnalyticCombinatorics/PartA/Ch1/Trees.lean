import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Tree count tables.
-/

namespace AnalyticCombinatorics.PartA.Ch1.Trees

def catalanTreeCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 42
  | 6 => 132
  | 7 => 429
  | 8 => 1430
  | 9 => 4862
  | 10 => 16796
  | _ => 0

example : catalanTreeCount 5 = 42 := by native_decide
example : catalanTreeCount 10 = 16796 := by native_decide

theorem catalanTreeCount_values_0_to_10 :
    (List.range 11).map catalanTreeCount =
      [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796] := by
  native_decide

structure TreeShapeWindow where
  leaves : ℕ
  unaryNodes : ℕ
  binaryNodes : ℕ
  maxDepth : ℕ
  traversalBudget : ℕ
deriving DecidableEq, Repr

def TreeShapeWindow.nodeCount (w : TreeShapeWindow) : ℕ :=
  w.leaves + w.unaryNodes + w.binaryNodes

def TreeShapeWindow.edgeCount (w : TreeShapeWindow) : ℕ :=
  w.unaryNodes + 2 * w.binaryNodes

def TreeShapeWindow.fullBinaryReady (w : TreeShapeWindow) : Prop :=
  w.unaryNodes = 0 ∧ w.leaves = w.binaryNodes + 1

def TreeShapeWindow.depthControlled (w : TreeShapeWindow) : Prop :=
  w.maxDepth ≤ w.traversalBudget ∧
    w.nodeCount ≤ w.traversalBudget + w.leaves + w.binaryNodes

def TreeShapeWindow.ready (w : TreeShapeWindow) : Prop :=
  0 < w.leaves ∧ w.depthControlled

def TreeShapeWindow.certificate (w : TreeShapeWindow) : ℕ :=
  w.nodeCount + w.edgeCount + w.maxDepth + w.traversalBudget

theorem leaves_le_certificate (w : TreeShapeWindow) :
    w.leaves ≤ w.certificate := by
  unfold TreeShapeWindow.certificate TreeShapeWindow.nodeCount TreeShapeWindow.edgeCount
  omega

theorem edgeCount_le_certificate (w : TreeShapeWindow) :
    w.edgeCount ≤ w.certificate := by
  unfold TreeShapeWindow.certificate
  omega

def sampleBinaryTreeWindow : TreeShapeWindow :=
  { leaves := 5, unaryNodes := 0, binaryNodes := 4, maxDepth := 4, traversalBudget := 9 }

example : sampleBinaryTreeWindow.fullBinaryReady := by
  norm_num [sampleBinaryTreeWindow, TreeShapeWindow.fullBinaryReady]

example : sampleBinaryTreeWindow.ready := by
  norm_num [sampleBinaryTreeWindow, TreeShapeWindow.ready, TreeShapeWindow.depthControlled,
    TreeShapeWindow.nodeCount]

example : sampleBinaryTreeWindow.certificate = 30 := by
  norm_num [sampleBinaryTreeWindow, TreeShapeWindow.certificate, TreeShapeWindow.nodeCount,
    TreeShapeWindow.edgeCount]


structure TreesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TreesBudgetCertificate.controlled
    (c : TreesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TreesBudgetCertificate.budgetControlled
    (c : TreesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TreesBudgetCertificate.Ready
    (c : TreesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TreesBudgetCertificate.size
    (c : TreesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem trees_budgetCertificate_le_size
    (c : TreesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTreesBudgetCertificate :
    TreesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [TreesBudgetCertificate.controlled,
      sampleTreesBudgetCertificate]
  · norm_num [TreesBudgetCertificate.budgetControlled,
      sampleTreesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleTreesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [TreesBudgetCertificate.controlled,
      sampleTreesBudgetCertificate]
  · norm_num [TreesBudgetCertificate.budgetControlled,
      sampleTreesBudgetCertificate]

example :
    sampleTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleTreesBudgetCertificate.size := by
  apply trees_budgetCertificate_le_size
  constructor
  · norm_num [TreesBudgetCertificate.controlled,
      sampleTreesBudgetCertificate]
  · norm_num [TreesBudgetCertificate.budgetControlled,
      sampleTreesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List TreesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTreesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTreesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.Trees
