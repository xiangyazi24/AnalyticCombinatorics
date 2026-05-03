import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace TreeHeightAsymptotics

/-!
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Asymptotic analysis of tree height and width.

  This file records executable finite checks for binary trees of bounded height,
  width at levels, Catalan coefficients, and binary de Bruijn sequence counts.
-/

/-! ## Catalan coefficients -/

/-- Catalan number `C_n = (2n choose n) / (n+1)`. -/
def catalanNumber (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Catalan numbers `C_n` for `n = 0, ..., 10`. -/
def catalanTable : Fin 11 → ℕ := ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]

theorem catalan_table_0 : catalanTable 0 = 1 := by native_decide
theorem catalan_table_1 : catalanTable 1 = 1 := by native_decide
theorem catalan_table_2 : catalanTable 2 = 2 := by native_decide
theorem catalan_table_3 : catalanTable 3 = 5 := by native_decide
theorem catalan_table_4 : catalanTable 4 = 14 := by native_decide
theorem catalan_table_5 : catalanTable 5 = 42 := by native_decide
theorem catalan_table_6 : catalanTable 6 = 132 := by native_decide
theorem catalan_table_7 : catalanTable 7 = 429 := by native_decide
theorem catalan_table_8 : catalanTable 8 = 1430 := by native_decide
theorem catalan_table_9 : catalanTable 9 = 4862 := by native_decide
theorem catalan_table_10 : catalanTable 10 = 16796 := by native_decide

theorem catalan_formula_0 : catalanNumber 0 = catalanTable 0 := by native_decide
theorem catalan_formula_1 : catalanNumber 1 = catalanTable 1 := by native_decide
theorem catalan_formula_2 : catalanNumber 2 = catalanTable 2 := by native_decide
theorem catalan_formula_3 : catalanNumber 3 = catalanTable 3 := by native_decide
theorem catalan_formula_4 : catalanNumber 4 = catalanTable 4 := by native_decide
theorem catalan_formula_5 : catalanNumber 5 = catalanTable 5 := by native_decide
theorem catalan_formula_6 : catalanNumber 6 = catalanTable 6 := by native_decide
theorem catalan_formula_7 : catalanNumber 7 = catalanTable 7 := by native_decide
theorem catalan_formula_8 : catalanNumber 8 = catalanTable 8 := by native_decide
theorem catalan_formula_9 : catalanNumber 9 = catalanTable 9 := by native_decide
theorem catalan_formula_10 : catalanNumber 10 = catalanTable 10 := by native_decide

/-! ## Binary trees of bounded height -/

/--
`boundedHeightTrees h n` counts binary trees with `n` internal nodes and height at most `h`.
Height `0` admits only the empty tree. For positive height and positive size, the root
contributes one internal node and the remaining nodes are split between the two subtrees.
-/
def boundedHeightTrees : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | _ + 1, 0 => 1
  | h + 1, n + 1 =>
      (List.range (n + 1)).foldl
        (fun total i => total + boundedHeightTrees h i * boundedHeightTrees h (n - i)) 0

/-- Height at most `0`: only the empty tree. -/
def heightAtMostZeroTable : Fin 5 → ℕ := ![1, 0, 0, 0, 0]

/-- Height at most `1`: the empty tree and the root with two empty subtrees. -/
def heightAtMostOneTable : Fin 5 → ℕ := ![1, 1, 0, 0, 0]

/-- Height at most `2`: finite table from the convolution of height-at-most-`1` trees. -/
def heightAtMostTwoTable : Fin 5 → ℕ := ![1, 1, 2, 1, 0]

theorem bounded_height_zero_empty : boundedHeightTrees 0 0 = 1 := by native_decide
theorem bounded_height_zero_nonempty_1 : boundedHeightTrees 0 1 = 0 := by native_decide
theorem bounded_height_zero_nonempty_2 : boundedHeightTrees 0 2 = 0 := by native_decide
theorem bounded_height_zero_nonempty_3 : boundedHeightTrees 0 3 = 0 := by native_decide
theorem bounded_height_zero_table : heightAtMostZeroTable = ![1, 0, 0, 0, 0] := by native_decide

theorem bounded_height_one_empty : boundedHeightTrees 1 0 = 1 := by native_decide
theorem bounded_height_one_single_root : boundedHeightTrees 1 1 = 1 := by native_decide
theorem bounded_height_one_two_nodes : boundedHeightTrees 1 2 = 0 := by native_decide
theorem bounded_height_one_three_nodes : boundedHeightTrees 1 3 = 0 := by native_decide
theorem bounded_height_one_table : heightAtMostOneTable = ![1, 1, 0, 0, 0] := by native_decide

theorem bounded_height_two_empty : boundedHeightTrees 2 0 = 1 := by native_decide
theorem bounded_height_two_one_node : boundedHeightTrees 2 1 = 1 := by native_decide

/-- For `n = 2`, the root has one internal child, either left or right. -/
theorem bounded_height_two_two_nodes : boundedHeightTrees 2 2 = 2 := by native_decide

/-- For `n = 3`, the only exact split is one internal node in each subtree. -/
theorem bounded_height_two_three_nodes : boundedHeightTrees 2 3 = 1 := by native_decide

theorem bounded_height_two_four_nodes : boundedHeightTrees 2 4 = 0 := by native_decide
theorem bounded_height_two_table : heightAtMostTwoTable = ![1, 1, 2, 1, 0] := by native_decide

/-- Height-at-most-`2` count for `n = 2`, written as the height-at-most-`1` convolution. -/
theorem bounded_height_two_convolution_two_nodes :
    boundedHeightTrees 2 2 =
      boundedHeightTrees 1 0 * boundedHeightTrees 1 1 +
      boundedHeightTrees 1 1 * boundedHeightTrees 1 0 := by native_decide

/-- Height-at-most-`2` count for `n = 3`, written as the height-at-most-`1` convolution. -/
theorem bounded_height_two_convolution_three_nodes :
    boundedHeightTrees 2 3 =
      boundedHeightTrees 1 0 * boundedHeightTrees 1 2 +
      boundedHeightTrees 1 1 * boundedHeightTrees 1 1 +
      boundedHeightTrees 1 2 * boundedHeightTrees 1 0 := by native_decide

theorem bounded_height_two_three_nodes_le_catalan_three :
    boundedHeightTrees 2 3 ≤ catalanNumber 3 := by native_decide

theorem bounded_height_two_three_nodes_le_catalan_table_three :
    boundedHeightTrees 2 3 ≤ catalanTable 3 := by native_decide

/-- The cumulative count through `n = 2` is `1 + 1 + 2 = 4`. -/
theorem bounded_height_two_cumulative_through_two :
    boundedHeightTrees 2 0 + boundedHeightTrees 2 1 + boundedHeightTrees 2 2 = 4 := by
  native_decide

/-! ## Width of binary trees -/

/-- Nodes at a level of a complete binary tree. -/
def completeBinaryTreeLevelNodes (level : ℕ) : ℕ := 2 ^ level

/-- Width of a complete binary tree of height `h`: the maximum number of nodes at any level. -/
def completeBinaryTreeWidth (h : ℕ) : ℕ := 2 ^ h

/-- Width values for complete binary trees of heights `0, ..., 5`. -/
def completeBinaryTreeWidthTable : Fin 6 → ℕ := ![1, 2, 4, 8, 16, 32]

theorem complete_binary_tree_level_nodes_0 : completeBinaryTreeLevelNodes 0 = 1 := by native_decide
theorem complete_binary_tree_level_nodes_1 : completeBinaryTreeLevelNodes 1 = 2 := by native_decide
theorem complete_binary_tree_level_nodes_2 : completeBinaryTreeLevelNodes 2 = 4 := by native_decide
theorem complete_binary_tree_level_nodes_3 : completeBinaryTreeLevelNodes 3 = 8 := by native_decide

theorem complete_binary_tree_width_0 : completeBinaryTreeWidth 0 = 1 := by native_decide
theorem complete_binary_tree_width_1 : completeBinaryTreeWidth 1 = 2 := by native_decide
theorem complete_binary_tree_width_2 : completeBinaryTreeWidth 2 = 4 := by native_decide
theorem complete_binary_tree_width_3 : completeBinaryTreeWidth 3 = 8 := by native_decide
theorem complete_binary_tree_width_4 : completeBinaryTreeWidth 4 = 16 := by native_decide
theorem complete_binary_tree_width_5 : completeBinaryTreeWidth 5 = 32 := by native_decide
theorem complete_binary_tree_width_table :
    completeBinaryTreeWidthTable = ![1, 2, 4, 8, 16, 32] := by native_decide

/-! ## Binary de Bruijn sequence counts -/

/-- Number of binary de Bruijn sequences of order `n`: `B(2,n) = 2^(2^(n-1)-n)`. -/
def binaryDeBruijnCount (n : ℕ) : ℕ := 2 ^ (2 ^ (n - 1) - n)

/-- Binary de Bruijn sequence counts for `n = 1, ..., 7`. -/
def binaryDeBruijnCountTable : Fin 7 → ℕ := ![1, 1, 2, 16, 2048, 67108864, 144115188075855872]

theorem binary_de_bruijn_count_1 : binaryDeBruijnCount 1 = 1 := by native_decide
theorem binary_de_bruijn_count_2 : binaryDeBruijnCount 2 = 1 := by native_decide
theorem binary_de_bruijn_count_3 : binaryDeBruijnCount 3 = 2 := by native_decide
theorem binary_de_bruijn_count_4 : binaryDeBruijnCount 4 = 16 := by native_decide
theorem binary_de_bruijn_count_5 : binaryDeBruijnCount 5 = 2048 := by native_decide
theorem binary_de_bruijn_count_6 : binaryDeBruijnCount 6 = 67108864 := by native_decide
theorem binary_de_bruijn_count_7 : binaryDeBruijnCount 7 = 144115188075855872 := by native_decide

theorem binary_de_bruijn_count_table :
    binaryDeBruijnCountTable = ![1, 1, 2, 16, 2048, 67108864, 144115188075855872] := by
  native_decide

end TreeHeightAsymptotics
