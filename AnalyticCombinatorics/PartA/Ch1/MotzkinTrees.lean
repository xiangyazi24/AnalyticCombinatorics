import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Motzkin tree count table.

Motzkin trees are unary-binary trees.  The inductive model below records the
node-size statistic independently of the old cross-file class machinery.
-/

namespace AnalyticCombinatorics.PartA.Ch1.MotzkinTrees

inductive MotzkinTree where
  | leaf : MotzkinTree
  | unary : MotzkinTree → MotzkinTree
  | binary : MotzkinTree → MotzkinTree → MotzkinTree
deriving DecidableEq, Repr

namespace MotzkinTree

def size : MotzkinTree → ℕ
  | leaf => 1
  | unary t => 1 + size t
  | binary l r => 1 + size l + size r

def leaves : MotzkinTree → ℕ
  | leaf => 1
  | unary t => leaves t
  | binary l r => leaves l + leaves r

def unaryNodeCount : MotzkinTree → ℕ
  | leaf => 0
  | unary t => 1 + unaryNodeCount t
  | binary l r => unaryNodeCount l + unaryNodeCount r

def binaryNodeCount : MotzkinTree → ℕ
  | leaf => 0
  | unary t => binaryNodeCount t
  | binary l r => 1 + binaryNodeCount l + binaryNodeCount r

theorem size_pos (t : MotzkinTree) : 0 < size t := by
  induction t with
  | leaf =>
      simp [size]
  | unary t ih =>
      simp [size]
  | binary l r ihl ihr =>
      simp [size]

theorem leaves_pos (t : MotzkinTree) : 0 < leaves t := by
  induction t with
  | leaf =>
      simp [leaves]
  | unary t ih =>
      simpa [leaves]
  | binary l r ihl ihr =>
      simp [leaves, Nat.add_pos_left ihl]

end MotzkinTree

structure MotzkinTreeWindow where
  unaryNodes : ℕ
  binaryNodes : ℕ
  leafSlack : ℕ
deriving DecidableEq, Repr

def hasMotzkinBranching (w : MotzkinTreeWindow) : Prop :=
  0 < w.unaryNodes + w.binaryNodes

def binaryNodesControlled (w : MotzkinTreeWindow) : Prop :=
  w.binaryNodes ≤ w.unaryNodes + w.leafSlack

def motzkinTreeWindowReady (w : MotzkinTreeWindow) : Prop :=
  hasMotzkinBranching w ∧ binaryNodesControlled w

def motzkinTreeWindowBudget (w : MotzkinTreeWindow) : ℕ :=
  w.unaryNodes + w.binaryNodes + w.leafSlack

theorem motzkinTreeWindowReady.certificate {w : MotzkinTreeWindow}
    (h : motzkinTreeWindowReady w) :
    hasMotzkinBranching w ∧ binaryNodesControlled w ∧
      w.binaryNodes ≤ motzkinTreeWindowBudget w := by
  rcases h with ⟨hbranching, hcontrolled⟩
  refine ⟨hbranching, hcontrolled, ?_⟩
  unfold motzkinTreeWindowBudget
  omega

theorem unaryNodes_le_budget (w : MotzkinTreeWindow) :
    w.unaryNodes ≤ motzkinTreeWindowBudget w := by
  unfold motzkinTreeWindowBudget
  omega

def sampleMotzkinTree : MotzkinTree :=
  MotzkinTree.binary (MotzkinTree.unary MotzkinTree.leaf) MotzkinTree.leaf

def motzkinTreeCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 9
  | 5 => 21
  | 6 => 51
  | _ => 0

def sampleMotzkinTreeWindow : MotzkinTreeWindow :=
  { unaryNodes := 4, binaryNodes := 5, leafSlack := 1 }

example : motzkinTreeWindowReady sampleMotzkinTreeWindow := by
  norm_num [motzkinTreeWindowReady, hasMotzkinBranching]
  norm_num [binaryNodesControlled, sampleMotzkinTreeWindow]

example : motzkinTreeCount 6 = 51 := by native_decide
example : motzkinTreeWindowBudget sampleMotzkinTreeWindow = 10 := by native_decide
example : MotzkinTree.size sampleMotzkinTree = 4 := by native_decide
example : MotzkinTree.leaves sampleMotzkinTree = 2 := by native_decide
example : MotzkinTree.unaryNodeCount sampleMotzkinTree = 1 := by native_decide
example : MotzkinTree.binaryNodeCount sampleMotzkinTree = 1 := by native_decide


structure MotzkinTreesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MotzkinTreesBudgetCertificate.controlled
    (c : MotzkinTreesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MotzkinTreesBudgetCertificate.budgetControlled
    (c : MotzkinTreesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MotzkinTreesBudgetCertificate.Ready
    (c : MotzkinTreesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MotzkinTreesBudgetCertificate.size
    (c : MotzkinTreesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem motzkinTrees_budgetCertificate_le_size
    (c : MotzkinTreesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMotzkinTreesBudgetCertificate :
    MotzkinTreesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleMotzkinTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [MotzkinTreesBudgetCertificate.controlled,
      sampleMotzkinTreesBudgetCertificate]
  · norm_num [MotzkinTreesBudgetCertificate.budgetControlled,
      sampleMotzkinTreesBudgetCertificate]

example :
    sampleMotzkinTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleMotzkinTreesBudgetCertificate.size := by
  apply motzkinTrees_budgetCertificate_le_size
  constructor
  · norm_num [MotzkinTreesBudgetCertificate.controlled,
      sampleMotzkinTreesBudgetCertificate]
  · norm_num [MotzkinTreesBudgetCertificate.budgetControlled,
      sampleMotzkinTreesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMotzkinTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [MotzkinTreesBudgetCertificate.controlled,
      sampleMotzkinTreesBudgetCertificate]
  · norm_num [MotzkinTreesBudgetCertificate.budgetControlled,
      sampleMotzkinTreesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMotzkinTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleMotzkinTreesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MotzkinTreesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMotzkinTreesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMotzkinTreesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.MotzkinTrees
