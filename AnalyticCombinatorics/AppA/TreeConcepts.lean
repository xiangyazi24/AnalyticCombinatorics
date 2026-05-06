import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix A: tree concepts.

Finite node, edge, height, and branching windows.
-/

namespace AnalyticCombinatorics.AppA.TreeConcepts

/-- Finite rooted tree descriptor by node, edge, and height counts. -/
structure RootedTreeStats where
  nodes : ℕ
  edges : ℕ
  height : ℕ
deriving DecidableEq, Repr

def RootedTreeStats.valid (t : RootedTreeStats) : Prop :=
  0 < t.nodes ∧ t.edges + 1 = t.nodes ∧ t.height ≤ t.nodes

/-- Boolean validation for finite tree statistics. -/
def rootedTreeStatsValidBool (t : RootedTreeStats) : Bool :=
  decide (0 < t.nodes) && decide (t.edges + 1 = t.nodes) &&
    decide (t.height ≤ t.nodes)

def pathTreeStats (n : ℕ) : RootedTreeStats :=
  { nodes := n + 1, edges := n, height := n + 1 }

theorem pathTreeStats_valid_window :
    (List.range 16).all (fun n => rootedTreeStatsValidBool (pathTreeStats n)) = true := by
  unfold rootedTreeStatsValidBool pathTreeStats
  native_decide

/-- Prefix sum of path-tree heights in a sampled window. -/
def pathTreeHeightPrefix (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total n => total + (pathTreeStats n).height) 0

theorem pathTreeHeight_prefixWindow :
    pathTreeHeightPrefix 5 = 21 := by
  unfold pathTreeHeightPrefix pathTreeStats
  native_decide

structure TreeConceptWindow where
  nodeWindow : ℕ
  edgeWindow : ℕ
  heightWindow : ℕ
  branchingSlack : ℕ
deriving DecidableEq, Repr

def treeConceptWindowReady (w : TreeConceptWindow) : Prop :=
  0 < w.nodeWindow ∧
    w.edgeWindow ≤ w.nodeWindow + w.branchingSlack ∧
      w.heightWindow ≤ w.nodeWindow + w.branchingSlack

def treeConceptBudget (w : TreeConceptWindow) : ℕ :=
  w.nodeWindow + w.edgeWindow + w.heightWindow + w.branchingSlack

theorem edgeWindow_le_budget (w : TreeConceptWindow) :
    w.edgeWindow ≤ treeConceptBudget w := by
  unfold treeConceptBudget
  omega

def sampleTreeConceptWindow : TreeConceptWindow :=
  { nodeWindow := 7, edgeWindow := 6, heightWindow := 4, branchingSlack := 0 }

example : treeConceptWindowReady sampleTreeConceptWindow := by
  norm_num [treeConceptWindowReady, sampleTreeConceptWindow]

structure TreeConceptsBudgetCertificate where
  nodeWindow : ℕ
  edgeWindow : ℕ
  heightWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TreeConceptsBudgetCertificate.controlled
    (c : TreeConceptsBudgetCertificate) : Prop :=
  0 < c.nodeWindow ∧
    c.edgeWindow ≤ c.nodeWindow + c.slack ∧
      c.heightWindow ≤ c.nodeWindow + c.slack

def TreeConceptsBudgetCertificate.budgetControlled
    (c : TreeConceptsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.nodeWindow + c.edgeWindow + c.heightWindow + c.slack

def TreeConceptsBudgetCertificate.Ready
    (c : TreeConceptsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TreeConceptsBudgetCertificate.size
    (c : TreeConceptsBudgetCertificate) : ℕ :=
  c.nodeWindow + c.edgeWindow + c.heightWindow + c.slack

theorem treeConcepts_budgetCertificate_le_size
    (c : TreeConceptsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleTreeConceptsBudgetCertificate :
    TreeConceptsBudgetCertificate :=
  { nodeWindow := 7
    edgeWindow := 6
    heightWindow := 4
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTreeConceptsBudgetCertificate.Ready := by
  constructor
  · norm_num [TreeConceptsBudgetCertificate.controlled,
      sampleTreeConceptsBudgetCertificate]
  · norm_num [TreeConceptsBudgetCertificate.budgetControlled,
      sampleTreeConceptsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTreeConceptsBudgetCertificate.certificateBudgetWindow ≤
      sampleTreeConceptsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleTreeConceptsBudgetCertificate.Ready := by
  constructor
  · norm_num [TreeConceptsBudgetCertificate.controlled,
      sampleTreeConceptsBudgetCertificate]
  · norm_num [TreeConceptsBudgetCertificate.budgetControlled,
      sampleTreeConceptsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List TreeConceptsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleTreeConceptsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleTreeConceptsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.TreeConcepts
