import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch7.RecursiveTreeStructures


/-!
  Recursive decomposition of tree structures, following Chapter VII of
  Analytic Combinatorics.  The file records finite coefficient checks for
  the standard tree equations.
-/

/-! ## Binary trees and Catalan numbers -/

/-- Catalan number `C_n = binom(2n,n)/(n+1)`. -/
def catalanNumber (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Initial Catalan coefficients for `T(z) = 1 + z * T(z)^2`. -/
def catalanTable : Fin 9 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430]

/-- Number of binary trees with `n` internal nodes. -/
def binaryTreeCount (n : ℕ) : ℕ := catalanNumber n

/-- Coefficient convolution from `T(z) = 1 + z * T(z)^2`. -/
def catalanConvolution (n : ℕ) : ℕ :=
  (Finset.range n).sum (fun k => catalanNumber k * catalanNumber (n - 1 - k))

theorem catalan_values_0_8 :
    [catalanNumber 0, catalanNumber 1, catalanNumber 2,
      catalanNumber 3, catalanNumber 4, catalanNumber 5,
      catalanNumber 6, catalanNumber 7, catalanNumber 8] =
    [1, 1, 2, 5, 14, 42, 132, 429, 1430] := by native_decide

theorem catalan_table_check :
    ∀ i : Fin 9, catalanNumber i.val = catalanTable i := by native_decide

theorem catalan_recurrence_1_8 :
    ∀ i : Fin 8,
      let n := i.val + 1
      catalanNumber n = catalanConvolution n := by native_decide

theorem binary_tree_values_0_8 :
    [binaryTreeCount 0, binaryTreeCount 1, binaryTreeCount 2,
      binaryTreeCount 3, binaryTreeCount 4, binaryTreeCount 5,
      binaryTreeCount 6, binaryTreeCount 7, binaryTreeCount 8] =
    [1, 1, 2, 5, 14, 42, 132, 429, 1430] := by native_decide

/-! ## Ordered trees -/

/-- Plane ordered trees with `n` edges, shifted from binary trees. -/
def orderedTreeEdgesCount (n : ℕ) : ℕ := catalanNumber n

theorem ordered_tree_edges_values_0_8 :
    [orderedTreeEdgesCount 0, orderedTreeEdgesCount 1, orderedTreeEdgesCount 2,
      orderedTreeEdgesCount 3, orderedTreeEdgesCount 4, orderedTreeEdgesCount 5,
      orderedTreeEdgesCount 6, orderedTreeEdgesCount 7, orderedTreeEdgesCount 8] =
    [1, 1, 2, 5, 14, 42, 132, 429, 1430] := by native_decide

theorem ordered_tree_binary_shift_0_8 :
    ∀ i : Fin 9, orderedTreeEdgesCount i.val = binaryTreeCount i.val := by native_decide

/-! ## Unary-binary trees and Motzkin numbers -/

/--
Unary-binary recursive decomposition has alternatives `1`, `z * T`,
and a binary product term `z * T^2`; the Motzkin indexing checked here
uses the standard convolution with total binary-size shift two.
-/
def motzkinPrefix : ℕ → List ℕ
  | 0 => [1]
  | n + 1 =>
      let xs := motzkinPrefix n
      let next :=
        xs.getD n 0 +
          (Finset.range n).sum (fun k => xs.getD k 0 * xs.getD (n - 1 - k) 0)
      xs ++ [next]

/-- Motzkin number `M_n`. -/
def motzkinNumber (n : ℕ) : ℕ := (motzkinPrefix n).getD n 0

/-- Unary-binary tree coefficients in the Motzkin indexing. -/
def unaryBinaryTreeCount (n : ℕ) : ℕ := motzkinNumber n

/-- Initial Motzkin coefficients. -/
def motzkinTable : Fin 9 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323]

/-- Right side of `M_n = M_{n-1} + sum_{k=0}^{n-2} M_k M_{n-2-k}`. -/
def motzkinConvolutionRhs (n : ℕ) : ℕ :=
  motzkinNumber (n - 1) +
    (Finset.range (n - 1)).sum
      (fun k => motzkinNumber k * motzkinNumber (n - 2 - k))

theorem motzkin_values_0_8 :
    [motzkinNumber 0, motzkinNumber 1, motzkinNumber 2,
      motzkinNumber 3, motzkinNumber 4, motzkinNumber 5,
      motzkinNumber 6, motzkinNumber 7, motzkinNumber 8] =
    [1, 1, 2, 4, 9, 21, 51, 127, 323] := by native_decide

theorem motzkin_table_check :
    ∀ i : Fin 9, motzkinNumber i.val = motzkinTable i := by native_decide

theorem unary_binary_tree_values_0_8 :
    [unaryBinaryTreeCount 0, unaryBinaryTreeCount 1, unaryBinaryTreeCount 2,
      unaryBinaryTreeCount 3, unaryBinaryTreeCount 4, unaryBinaryTreeCount 5,
      unaryBinaryTreeCount 6, unaryBinaryTreeCount 7, unaryBinaryTreeCount 8] =
    [1, 1, 2, 4, 9, 21, 51, 127, 323] := by native_decide

theorem unary_binary_tree_eq_motzkin_0_8 :
    ∀ i : Fin 9, unaryBinaryTreeCount i.val = motzkinNumber i.val := by native_decide

theorem motzkin_recurrence_2_8 :
    ∀ i : Fin 7,
      let n := i.val + 2
      motzkinNumber n = motzkinConvolutionRhs n := by native_decide

/-! ## 2-3 trees by leaves, with internal-node statistics -/

/-- Plane 2-3 trees: every internal node has two or three children. -/
inductive TwoThreeTree where
  | leaf : TwoThreeTree
  | node2 : TwoThreeTree → TwoThreeTree → TwoThreeTree
  | node3 : TwoThreeTree → TwoThreeTree → TwoThreeTree → TwoThreeTree
deriving DecidableEq, Repr

namespace TwoThreeTree

/-- Number of leaves. -/
def leaves : TwoThreeTree → ℕ
  | .leaf => 1
  | .node2 l r => l.leaves + r.leaves
  | .node3 a b c => a.leaves + b.leaves + c.leaves

/-- Number of internal nodes. -/
def internalNodes : TwoThreeTree → ℕ
  | .leaf => 0
  | .node2 l r => l.internalNodes + r.internalNodes + 1
  | .node3 a b c => a.internalNodes + b.internalNodes + c.internalNodes + 1

end TwoThreeTree

/-- Number of plane 2-3 trees with `n` leaves, indexed by `n = 0, ..., 8`. -/
def twoThreeLeavesTable : Fin 9 → ℕ :=
  ![0, 1, 1, 3, 10, 38, 154, 654, 2871]

/-- Tabulated count of 2-3 trees with `n` leaves. -/
def twoThreeTreeLeavesCount (n : ℕ) : ℕ :=
  if h : n < 9 then twoThreeLeavesTable ⟨n, h⟩ else 0

/-- Binary and ternary root decompositions for the tabulated 2-3 tree counts. -/
def twoThreeLeavesRhs (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n - 1)).sum
      (fun i => twoThreeTreeLeavesCount i * twoThreeTreeLeavesCount (n - i)) +
    (Finset.Icc 1 (n - 1)).sum
      (fun i =>
        (Finset.Icc 1 (n - i - 1)).sum
          (fun j =>
            twoThreeTreeLeavesCount i *
              twoThreeTreeLeavesCount j *
              twoThreeTreeLeavesCount (n - i - j)))

theorem twoThree_leaves_values_0_8 :
    [twoThreeTreeLeavesCount 0, twoThreeTreeLeavesCount 1,
      twoThreeTreeLeavesCount 2, twoThreeTreeLeavesCount 3,
      twoThreeTreeLeavesCount 4, twoThreeTreeLeavesCount 5,
      twoThreeTreeLeavesCount 6, twoThreeTreeLeavesCount 7,
      twoThreeTreeLeavesCount 8] =
    [0, 1, 1, 3, 10, 38, 154, 654, 2871] := by native_decide

theorem twoThree_leaves_recurrence_2_8 :
    ∀ i : Fin 7,
      let n := i.val + 2
      twoThreeTreeLeavesCount n = twoThreeLeavesRhs n := by native_decide

def twoThreeSample : TwoThreeTree :=
  .node3 (.node2 .leaf .leaf) .leaf .leaf

theorem twoThreeSample_leaves : twoThreeSample.leaves = 4 := by native_decide

theorem twoThreeSample_internalNodes : twoThreeSample.internalNodes = 2 := by native_decide

/-! ## Labeled rooted and unrooted trees -/

/-- Cayley's formula for labeled rooted trees: `n^(n-1)`. -/
def labelledRootedTreeCount (n : ℕ) : ℕ := n ^ (n - 1)

/-- Cayley's formula for labeled unrooted trees: `n^(n-2)`. -/
def labelledUnrootedTreeCount (n : ℕ) : ℕ := n ^ (n - 2)

def labelledRootedTreeTable : Fin 8 → ℕ :=
  ![1, 2, 9, 64, 625, 7776, 117649, 2097152]

def labelledUnrootedTreeTable : Fin 8 → ℕ :=
  ![1, 1, 3, 16, 125, 1296, 16807, 262144]

theorem labelled_rooted_values_1_8 :
    [labelledRootedTreeCount 1, labelledRootedTreeCount 2,
      labelledRootedTreeCount 3, labelledRootedTreeCount 4,
      labelledRootedTreeCount 5, labelledRootedTreeCount 6,
      labelledRootedTreeCount 7, labelledRootedTreeCount 8] =
    [1, 2, 9, 64, 625, 7776, 117649, 2097152] := by native_decide

theorem labelled_unrooted_values_1_8 :
    [labelledUnrootedTreeCount 1, labelledUnrootedTreeCount 2,
      labelledUnrootedTreeCount 3, labelledUnrootedTreeCount 4,
      labelledUnrootedTreeCount 5, labelledUnrootedTreeCount 6,
      labelledUnrootedTreeCount 7, labelledUnrootedTreeCount 8] =
    [1, 1, 3, 16, 125, 1296, 16807, 262144] := by native_decide

theorem labelled_rooted_table_check :
    ∀ i : Fin 8,
      labelledRootedTreeCount (i.val + 1) = labelledRootedTreeTable i := by native_decide

theorem labelled_unrooted_table_check :
    ∀ i : Fin 8,
      labelledUnrootedTreeCount (i.val + 1) = labelledUnrootedTreeTable i := by native_decide

theorem rooted_eq_choose_root_1_8 :
    ∀ i : Fin 8,
      let n := i.val + 1
      labelledRootedTreeCount n = n * labelledUnrootedTreeCount n := by native_decide

/-! ## Forests on a labeled vertex set -/

/-- Number of forests on `[n]`: `(n+1)^(n-1)`. -/
def labelledForestCount (n : ℕ) : ℕ := (n + 1) ^ (n - 1)

def labelledForestTable : Fin 7 → ℕ :=
  ![1, 3, 16, 125, 1296, 16807, 262144]

theorem labelled_forest_values_1_7 :
    [labelledForestCount 1, labelledForestCount 2, labelledForestCount 3,
      labelledForestCount 4, labelledForestCount 5, labelledForestCount 6,
      labelledForestCount 7] =
    [1, 3, 16, 125, 1296, 16807, 262144] := by native_decide

theorem labelled_forest_table_check :
    ∀ i : Fin 7, labelledForestCount (i.val + 1) = labelledForestTable i := by native_decide

/-! ## Binary search trees -/

/-- Number of binary search trees on `[n]`; the shape is a binary tree. -/
def binarySearchTreeCount (n : ℕ) : ℕ := catalanNumber n

theorem binary_search_tree_values_0_8 :
    [binarySearchTreeCount 0, binarySearchTreeCount 1,
      binarySearchTreeCount 2, binarySearchTreeCount 3,
      binarySearchTreeCount 4, binarySearchTreeCount 5,
      binarySearchTreeCount 6, binarySearchTreeCount 7,
      binarySearchTreeCount 8] =
    [1, 1, 2, 5, 14, 42, 132, 429, 1430] := by native_decide

theorem binary_search_tree_eq_binary_tree_0_8 :
    ∀ i : Fin 9, binarySearchTreeCount i.val = binaryTreeCount i.val := by native_decide

/-! ## AVL tree height bound -/

/-- Minimum number of nodes in an AVL tree of height `h`, with empty height `0`. -/
def avlMinNodes : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | h + 2 => 1 + avlMinNodes (h + 1) + avlMinNodes h

/-- Maximum AVL height for `n = 1, ..., 15`, indexed by `n - 1`. -/
def avlMaxHeightTable : Fin 15 → ℕ :=
  ![1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5]

/-- `floor(1.44 * log2(n+2))` for `n = 1, ..., 15`, indexed by `n - 1`. -/
def avlHeightBoundFloorTable : Fin 15 → ℕ :=
  ![2, 2, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5]

/-- Tabulated maximum AVL height on the checked range. -/
def avlMaxHeight (n : ℕ) : ℕ :=
  if h : n - 1 < 15 then avlMaxHeightTable ⟨n - 1, h⟩ else 0

/-- Tabulated floor of `1.44 * log2(n+2)` on the checked range. -/
def avlHeightBoundFloor (n : ℕ) : ℕ :=
  if h : n - 1 < 15 then avlHeightBoundFloorTable ⟨n - 1, h⟩ else 0

theorem avl_min_nodes_values_0_6 :
    [avlMinNodes 0, avlMinNodes 1, avlMinNodes 2,
      avlMinNodes 3, avlMinNodes 4, avlMinNodes 5, avlMinNodes 6] =
    [0, 1, 2, 4, 7, 12, 20] := by native_decide

theorem avl_max_height_values_1_15 :
    [avlMaxHeight 1, avlMaxHeight 2, avlMaxHeight 3,
      avlMaxHeight 4, avlMaxHeight 5, avlMaxHeight 6,
      avlMaxHeight 7, avlMaxHeight 8, avlMaxHeight 9,
      avlMaxHeight 10, avlMaxHeight 11, avlMaxHeight 12,
      avlMaxHeight 13, avlMaxHeight 14, avlMaxHeight 15] =
    [1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5] := by native_decide

theorem avl_height_bound_floor_values_1_15 :
    [avlHeightBoundFloor 1, avlHeightBoundFloor 2, avlHeightBoundFloor 3,
      avlHeightBoundFloor 4, avlHeightBoundFloor 5, avlHeightBoundFloor 6,
      avlHeightBoundFloor 7, avlHeightBoundFloor 8, avlHeightBoundFloor 9,
      avlHeightBoundFloor 10, avlHeightBoundFloor 11, avlHeightBoundFloor 12,
      avlHeightBoundFloor 13, avlHeightBoundFloor 14, avlHeightBoundFloor 15] =
    [2, 2, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5] := by native_decide

theorem avl_height_bound_floor_1_15 :
    ∀ i : Fin 15,
      let n := i.val + 1
      avlMaxHeight n ≤ avlHeightBoundFloor n := by native_decide

theorem avl_max_height_is_feasible_1_15 :
    ∀ i : Fin 15,
      let n := i.val + 1
      avlMinNodes (avlMaxHeight n) ≤ n := by native_decide

theorem avl_next_height_not_feasible_1_15 :
    ∀ i : Fin 15,
      let n := i.val + 1
      n < avlMinNodes (avlMaxHeight n + 1) := by native_decide



structure RecursiveTreeStructuresBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RecursiveTreeStructuresBudgetCertificate.controlled
    (c : RecursiveTreeStructuresBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RecursiveTreeStructuresBudgetCertificate.budgetControlled
    (c : RecursiveTreeStructuresBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RecursiveTreeStructuresBudgetCertificate.Ready
    (c : RecursiveTreeStructuresBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RecursiveTreeStructuresBudgetCertificate.size
    (c : RecursiveTreeStructuresBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem recursiveTreeStructures_budgetCertificate_le_size
    (c : RecursiveTreeStructuresBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRecursiveTreeStructuresBudgetCertificate :
    RecursiveTreeStructuresBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRecursiveTreeStructuresBudgetCertificate.Ready := by
  constructor
  · norm_num [RecursiveTreeStructuresBudgetCertificate.controlled,
      sampleRecursiveTreeStructuresBudgetCertificate]
  · norm_num [RecursiveTreeStructuresBudgetCertificate.budgetControlled,
      sampleRecursiveTreeStructuresBudgetCertificate]

example :
    sampleRecursiveTreeStructuresBudgetCertificate.certificateBudgetWindow ≤
      sampleRecursiveTreeStructuresBudgetCertificate.size := by
  apply recursiveTreeStructures_budgetCertificate_le_size
  constructor
  · norm_num [RecursiveTreeStructuresBudgetCertificate.controlled,
      sampleRecursiveTreeStructuresBudgetCertificate]
  · norm_num [RecursiveTreeStructuresBudgetCertificate.budgetControlled,
      sampleRecursiveTreeStructuresBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRecursiveTreeStructuresBudgetCertificate.Ready := by
  constructor
  · norm_num [RecursiveTreeStructuresBudgetCertificate.controlled,
      sampleRecursiveTreeStructuresBudgetCertificate]
  · norm_num [RecursiveTreeStructuresBudgetCertificate.budgetControlled,
      sampleRecursiveTreeStructuresBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRecursiveTreeStructuresBudgetCertificate.certificateBudgetWindow ≤
      sampleRecursiveTreeStructuresBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RecursiveTreeStructuresBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRecursiveTreeStructuresBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRecursiveTreeStructuresBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.RecursiveTreeStructures
