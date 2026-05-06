import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch7.SimpleTreeFamilies


/-!
  Simple families of trees from Chapter VII of Flajolet--Sedgewick.
  The file records computable enumerations and small-value checks.
-/

/-! ## 1. Unary-binary trees and Motzkin numbers -/

/-- Unary-binary trees: an atom may be absent, unary, or binary. -/
inductive UnaryBinaryTree where
  | empty : UnaryBinaryTree
  | unary : UnaryBinaryTree → UnaryBinaryTree
  | binary : UnaryBinaryTree → UnaryBinaryTree → UnaryBinaryTree
deriving DecidableEq, Repr

namespace UnaryBinaryTree

/-- Size compatible with the Motzkin recurrence `M = 1 + z M + z^2 M^2`. -/
def size : UnaryBinaryTree → ℕ
  | .empty => 0
  | .unary t => t.size + 1
  | .binary l r => l.size + r.size + 2

end UnaryBinaryTree

/-- The first `n + 1` Motzkin numbers, computed by
`M_{k+1} = M_k + sum_{i=0}^{k-1} M_i M_{k-1-i}`. -/
def motzkinPrefix : ℕ → List ℕ
  | 0 => [1]
  | n + 1 =>
      let xs := motzkinPrefix n
      let next := xs.getD n 0 +
        (Finset.range n).sum (fun i => xs.getD i 0 * xs.getD (n - 1 - i) 0)
      xs ++ [next]

/-- Motzkin number `M_n`. -/
def motzkinNumber (n : ℕ) : ℕ := (motzkinPrefix n).getD n 0

theorem motzkin_values :
    [motzkinNumber 0, motzkinNumber 1, motzkinNumber 2,
      motzkinNumber 3, motzkinNumber 4, motzkinNumber 5] =
    [1, 1, 2, 4, 9, 21] := by
  native_decide

theorem motzkin_0 : motzkinNumber 0 = 1 := by native_decide
theorem motzkin_1 : motzkinNumber 1 = 1 := by native_decide
theorem motzkin_2 : motzkinNumber 2 = 2 := by native_decide
theorem motzkin_3 : motzkinNumber 3 = 4 := by native_decide
theorem motzkin_4 : motzkinNumber 4 = 9 := by native_decide
theorem motzkin_5 : motzkinNumber 5 = 21 := by native_decide

/-! ## 2. 2-3 trees by height -/

/-- 2-3 trees: internal nodes have exactly two or three children. -/
inductive TwoThreeTree where
  | leaf : TwoThreeTree
  | node2 : TwoThreeTree → TwoThreeTree → TwoThreeTree
  | node3 : TwoThreeTree → TwoThreeTree → TwoThreeTree → TwoThreeTree
deriving DecidableEq, Repr

namespace TwoThreeTree

/-- Height of a 2-3 tree, with leaves at height zero. -/
def height : TwoThreeTree → ℕ
  | .leaf => 0
  | .node2 l r => max l.height r.height + 1
  | .node3 a b c => max (max a.height b.height) c.height + 1

end TwoThreeTree

/-- Number of 2-3 trees of height at most `h`. -/
def twoThreeHeightAtMost : ℕ → ℕ
  | 0 => 1
  | h + 1 =>
      let a := twoThreeHeightAtMost h
      1 + a ^ 2 + a ^ 3

/-- Number of 2-3 trees of exact height `h`. -/
def twoThreeHeightExact (h : ℕ) : ℕ :=
  if h = 0 then 1 else twoThreeHeightAtMost h - twoThreeHeightAtMost (h - 1)

theorem twoThree_height_atMost_table :
    [twoThreeHeightAtMost 0, twoThreeHeightAtMost 1,
      twoThreeHeightAtMost 2, twoThreeHeightAtMost 3] =
    [1, 3, 37, 52023] := by
  native_decide

theorem twoThree_height_exact_table :
    [twoThreeHeightExact 0, twoThreeHeightExact 1,
      twoThreeHeightExact 2, twoThreeHeightExact 3] =
    [1, 2, 34, 51986] := by
  native_decide

/-! ## 3. Heap-ordered trees -/

/-- Small rooted tree shapes used for heap-order verification. -/
inductive HeapShape where
  | leaf : HeapShape
  | unary : HeapShape → HeapShape
  | binary : HeapShape → HeapShape → HeapShape
  | ternary : HeapShape → HeapShape → HeapShape → HeapShape
deriving DecidableEq, Repr

namespace HeapShape

/-- Number of vertices in the rooted shape. -/
def size : HeapShape → ℕ
  | .leaf => 1
  | .unary t => t.size + 1
  | .binary l r => l.size + r.size + 1
  | .ternary a b c => a.size + b.size + c.size + 1

/-- Product of all rooted subtree sizes. -/
def subtreeSizeProduct : HeapShape → ℕ
  | .leaf => 1
  | .unary t => (t.size + 1) * t.subtreeSizeProduct
  | .binary l r => (l.size + r.size + 1) * l.subtreeSizeProduct * r.subtreeSizeProduct
  | .ternary a b c =>
      (a.size + b.size + c.size + 1) *
        a.subtreeSizeProduct * b.subtreeSizeProduct * c.subtreeSizeProduct

/-- Hook-length enumeration for heap-ordered labelings of a fixed rooted shape. -/
def heapOrderedLabelings (t : HeapShape) : ℕ :=
  Nat.factorial t.size / t.subtreeSizeProduct

end HeapShape

def heapPath3 : HeapShape := .unary (.unary .leaf)
def heapStar3 : HeapShape := .binary .leaf .leaf
def heapPath4 : HeapShape := .unary (.unary (.unary .leaf))
def heapFork4 : HeapShape := .binary (.unary .leaf) .leaf
def heapStar4 : HeapShape := .ternary .leaf .leaf .leaf

theorem heap_path3_hook :
    HeapShape.heapOrderedLabelings heapPath3 =
      Nat.factorial 3 / (3 * 2 * 1) := by
  native_decide

theorem heap_star3_hook :
    HeapShape.heapOrderedLabelings heapStar3 =
      Nat.factorial 3 / (3 * 1 * 1) := by
  native_decide

theorem heap_small_values :
    [HeapShape.heapOrderedLabelings heapPath3,
      HeapShape.heapOrderedLabelings heapStar3,
      HeapShape.heapOrderedLabelings heapPath4,
      HeapShape.heapOrderedLabelings heapFork4,
      HeapShape.heapOrderedLabelings heapStar4] =
    [1, 2, 1, 3, 6] := by
  native_decide

/-! ## 4. Planted plane trees and Catalan numbers -/

/-- Catalan number `C_n = binom(2n,n)/(n+1)`. -/
def catalanNumber (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Planted plane trees: a root edge is planted above an ordinary plane tree. -/
def plantedPlaneTreeCount (n : ℕ) : ℕ := catalanNumber n

theorem plantedPlaneTree_values :
    [plantedPlaneTreeCount 0, plantedPlaneTreeCount 1, plantedPlaneTreeCount 2,
      plantedPlaneTreeCount 3, plantedPlaneTreeCount 4, plantedPlaneTreeCount 5] =
    [1, 1, 2, 5, 14, 42] := by
  native_decide

/-! ## 5. Binary search trees -/

/-- Distinct binary-search-tree shapes on `n` ordered keys. -/
def binarySearchTreeCount (n : ℕ) : ℕ := catalanNumber n

theorem binarySearchTree_values :
    [binarySearchTreeCount 0, binarySearchTreeCount 1, binarySearchTreeCount 2,
      binarySearchTreeCount 3, binarySearchTreeCount 4, binarySearchTreeCount 5] =
    [1, 1, 2, 5, 14, 42] := by
  native_decide

theorem bst_eq_catalan_6 : binarySearchTreeCount 6 = catalanNumber 6 := by native_decide

/-! ## 6. Generalized Catalan numbers for m-ary trees -/

/-- Fuss-Catalan number for full `m`-ary trees with `n` internal nodes. -/
def generalizedCatalan (m n : ℕ) : ℕ :=
  Nat.choose (m * n) n / ((m - 1) * n + 1)

theorem ternaryCatalan_values :
    [generalizedCatalan 3 0, generalizedCatalan 3 1, generalizedCatalan 3 2,
      generalizedCatalan 3 3, generalizedCatalan 3 4, generalizedCatalan 3 5] =
    [1, 1, 3, 12, 55, 273] := by
  native_decide

theorem quaternaryCatalan_values :
    [generalizedCatalan 4 0, generalizedCatalan 4 1, generalizedCatalan 4 2,
      generalizedCatalan 4 3, generalizedCatalan 4 4, generalizedCatalan 4 5] =
    [1, 1, 4, 22, 140, 969] := by
  native_decide

theorem generalizedCatalan_standard_form_3_4 :
    generalizedCatalan 3 4 = Nat.choose (3 * 4) 4 / (3 * 4 + 1 - 4) := by
  native_decide

theorem generalizedCatalan_standard_form_4_4 :
    generalizedCatalan 4 4 = Nat.choose (4 * 4) 4 / (4 * 4 + 1 - 4) := by
  native_decide



structure SimpleTreeFamiliesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SimpleTreeFamiliesBudgetCertificate.controlled
    (c : SimpleTreeFamiliesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SimpleTreeFamiliesBudgetCertificate.budgetControlled
    (c : SimpleTreeFamiliesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SimpleTreeFamiliesBudgetCertificate.Ready
    (c : SimpleTreeFamiliesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SimpleTreeFamiliesBudgetCertificate.size
    (c : SimpleTreeFamiliesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem simpleTreeFamilies_budgetCertificate_le_size
    (c : SimpleTreeFamiliesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSimpleTreeFamiliesBudgetCertificate :
    SimpleTreeFamiliesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSimpleTreeFamiliesBudgetCertificate.Ready := by
  constructor
  · norm_num [SimpleTreeFamiliesBudgetCertificate.controlled,
      sampleSimpleTreeFamiliesBudgetCertificate]
  · norm_num [SimpleTreeFamiliesBudgetCertificate.budgetControlled,
      sampleSimpleTreeFamiliesBudgetCertificate]

example :
    sampleSimpleTreeFamiliesBudgetCertificate.certificateBudgetWindow ≤
      sampleSimpleTreeFamiliesBudgetCertificate.size := by
  apply simpleTreeFamilies_budgetCertificate_le_size
  constructor
  · norm_num [SimpleTreeFamiliesBudgetCertificate.controlled,
      sampleSimpleTreeFamiliesBudgetCertificate]
  · norm_num [SimpleTreeFamiliesBudgetCertificate.budgetControlled,
      sampleSimpleTreeFamiliesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSimpleTreeFamiliesBudgetCertificate.Ready := by
  constructor
  · norm_num [SimpleTreeFamiliesBudgetCertificate.controlled,
      sampleSimpleTreeFamiliesBudgetCertificate]
  · norm_num [SimpleTreeFamiliesBudgetCertificate.budgetControlled,
      sampleSimpleTreeFamiliesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSimpleTreeFamiliesBudgetCertificate.certificateBudgetWindow ≤
      sampleSimpleTreeFamiliesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SimpleTreeFamiliesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSimpleTreeFamiliesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSimpleTreeFamiliesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.SimpleTreeFamilies
