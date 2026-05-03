import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace SingularInversion2

/-!
  Bounded executable tables for singular inversion and implicit schemas from
  Chapter VII of Flajolet--Sedgewick.

  The file records small coefficient tables only.  Each check is finite and is
  discharged by `native_decide`.
-/

/-! ## Shared bounded coefficient utilities -/

/-- Read a coefficient from a `Fin 12` table, returning zero outside the table. -/
def tableGet12 (a : Fin 12 → ℕ) (i : ℕ) : ℕ :=
  if h : i < 12 then a ⟨i, h⟩ else 0

/-- Coefficient of degree `n` in the square of a bounded coefficient table. -/
def coeffSquare12 (a : Fin 12 → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl
    (fun total i => total + tableGet12 a i * tableGet12 a (n - i)) 0

/-- Coefficient of degree `n` in the cube of a bounded coefficient table. -/
def coeffCube12 (a : Fin 12 → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl
    (fun total i =>
      total +
        (List.range (n - i + 1)).foldl
          (fun inner j =>
            inner + tableGet12 a i * tableGet12 a j * tableGet12 a (n - i - j)) 0) 0

/-- Catalan numbers in closed form. -/
def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-! ## Cayley rooted trees and labelled rooted forests -/

/-- Rooted labelled trees on `n` vertices: `n^(n-1)`, with zero at `n = 0`. -/
def cayleyRootedCount (n : ℕ) : ℕ :=
  if n = 0 then 0 else n ^ (n - 1)

/-- Rooted labelled tree counts for `n < 8`. -/
def cayleyRootedTable : Fin 8 → ℕ :=
  ![0, 1, 2, 9, 64, 625, 7776, 117649]

/-- The Cayley table agrees with `n^(n-1)` on the bounded range. -/
theorem cayley_rooted_table_checked :
    ∀ n : Fin 8, cayleyRootedTable n = cayleyRootedCount n.val := by
  native_decide

/-- Rooted labelled forests on `n` vertices with `k` components. -/
def rootedForestCount (n k : ℕ) : ℕ :=
  if n = 0 ∨ k = 0 ∨ n < k then 0
  else Nat.choose (n - 1) (k - 1) * n ^ (n - k)

/-- Rooted labelled forests on five vertices, indexed by the number of components. -/
def rootedForestN5ByComponents : Fin 6 → ℕ :=
  ![0, 625, 500, 150, 20, 1]

/-- The five-vertex forest row matches the Cayley forest formula. -/
theorem rooted_forest_n5_components_checked :
    ∀ k : Fin 6, rootedForestN5ByComponents k = rootedForestCount 5 k.val := by
  native_decide

/-- The component counts sum to the total number `(n + 1)^(n - 1)` of rooted forests. -/
theorem rooted_forest_n5_total_checked :
    rootedForestN5ByComponents ⟨1, by native_decide⟩ +
      rootedForestN5ByComponents ⟨2, by native_decide⟩ +
      rootedForestN5ByComponents ⟨3, by native_decide⟩ +
      rootedForestN5ByComponents ⟨4, by native_decide⟩ +
      rootedForestN5ByComponents ⟨5, by native_decide⟩ = 6 ^ 4 := by
  native_decide

/-! ## Binary trees with bounded height -/

/-- Binary trees of height at most two, counted by internal nodes. -/
def binaryHeight2Coeffs : Fin 12 → ℕ :=
  ![1, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Binary trees of height at most three, counted by internal nodes. -/
def binaryHeight3Coeffs : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 6, 6, 4, 1, 0, 0, 0, 0]

/-- Binary trees of height at most four, counted by internal nodes. -/
def binaryHeight4Coeffs : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 14, 26, 44, 69, 94, 114, 116, 94]

/-- One step of `B_h(z) = 1 + z B_{h-1}(z)^2`. -/
def binaryHeightStep (a : Fin 12 → ℕ) (n : ℕ) : ℕ :=
  if n = 0 then 1 else coeffSquare12 a (n - 1)

/-- The height-three table is obtained from the height-two table. -/
theorem binary_height_three_step_checked :
    ∀ n : Fin 12, binaryHeight3Coeffs n = binaryHeightStep binaryHeight2Coeffs n.val := by
  native_decide

/-- The height-four table is obtained from the height-three table. -/
theorem binary_height_four_step_checked :
    ∀ n : Fin 12, binaryHeight4Coeffs n = binaryHeightStep binaryHeight3Coeffs n.val := by
  native_decide

/-! ## Simple varieties of tree coefficient tables -/

/-- Ordered rooted trees, the shifted Catalan sequence. -/
def orderedTreeCoeffs : Fin 12 → ℕ :=
  ![0, 1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]

/-- Unary-binary trees from `T = z * (1 + T + T^2)`. -/
def unaryBinaryTreeCoeffs : Fin 12 → ℕ :=
  ![0, 1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188]

/-- Full ternary trees from `T = z + T^3`. -/
def fullTernaryTreeCoeffs : Fin 12 → ℕ :=
  ![0, 1, 0, 1, 0, 3, 0, 12, 0, 55, 0, 273]

/-- Ordered rooted trees are counted by shifted Catalan numbers. -/
theorem ordered_tree_coeffs_checked :
    ∀ n : Fin 12,
      orderedTreeCoeffs n = if n.val = 0 then 0 else catalanNumber (n.val - 1) := by
  native_decide

/-- Coefficient step for `T = z * (1 + T + T^2)`. -/
def unaryBinaryRhs (a : Fin 12 → ℕ) (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (if n = 1 then 1 else 0) + tableGet12 a (n - 1) + coeffSquare12 a (n - 1)

/-- The unary-binary table satisfies its implicit functional equation. -/
theorem unary_binary_tree_recurrence_checked :
    ∀ n : Fin 12, unaryBinaryTreeCoeffs n = unaryBinaryRhs unaryBinaryTreeCoeffs n.val := by
  native_decide

/-- Coefficient step for `T = z + T^3`. -/
def fullTernaryRhs (a : Fin 12 → ℕ) (n : ℕ) : ℕ :=
  if n = 1 then 1 else coeffCube12 a n

/-- The full ternary table satisfies its cubic implicit equation. -/
theorem full_ternary_tree_recurrence_checked :
    ∀ n : Fin 12, fullTernaryTreeCoeffs n = fullTernaryRhs fullTernaryTreeCoeffs n.val := by
  native_decide

/-! ## 2-3 trees from a smooth implicit schema -/

/-- Plane 2-3 trees from `T = z + T^2 + T^3`. -/
def twoThreeTreeCoeffs : Fin 12 → ℕ :=
  ![0, 1, 1, 3, 10, 38, 154, 654, 2871, 12925, 59345, 276835]

/-- Coefficient step for `T = z + T^2 + T^3`. -/
def twoThreeTreeRhs (a : Fin 12 → ℕ) (n : ℕ) : ℕ :=
  if n = 1 then 1 else coeffSquare12 a n + coeffCube12 a n

/-- The 2-3 tree table satisfies the quadratic-cubic implicit equation. -/
theorem two_three_tree_recurrence_checked :
    ∀ n : Fin 12, twoThreeTreeCoeffs n = twoThreeTreeRhs twoThreeTreeCoeffs n.val := by
  native_decide

/-- The first nontrivial 2-3 tree coefficients dominate the binary-only row. -/
theorem two_three_dominates_ordered_checked :
    ∀ n : Fin 12,
      2 ≤ n.val → orderedTreeCoeffs n ≤ twoThreeTreeCoeffs n := by
  native_decide

/-! ## Non-crossing partitions by number and type -/

/-- Narayana row for non-crossing partitions of a five-element set. -/
def narayanaRowFive : Fin 6 → ℕ :=
  ![0, 1, 10, 20, 10, 1]

/-- Narayana formula `N(5,k) = binom(5,k) binom(5,k-1) / 5`. -/
theorem narayana_row_five_checked :
    ∀ k : Fin 6,
      narayanaRowFive k =
        if k.val = 0 then 0 else Nat.choose 5 k.val * Nat.choose 5 (k.val - 1) / 5 := by
  native_decide

/-- Counts of non-crossing partitions of size five by block-size type. -/
def noncrossingTypeCountsN5 : Fin 7 → ℕ :=
  ![1, 5, 5, 10, 10, 10, 1]

/-- Number of blocks in the corresponding type rows. -/
def noncrossingTypeBlocksN5 : Fin 7 → ℕ :=
  ![1, 2, 2, 3, 3, 4, 5]

/-- Type counts group to the Narayana row by number of blocks. -/
theorem noncrossing_type_counts_group_checked :
    noncrossingTypeCountsN5 ⟨0, by native_decide⟩ = narayanaRowFive ⟨1, by native_decide⟩ ∧
      noncrossingTypeCountsN5 ⟨1, by native_decide⟩ +
        noncrossingTypeCountsN5 ⟨2, by native_decide⟩ = narayanaRowFive ⟨2, by native_decide⟩ ∧
      noncrossingTypeCountsN5 ⟨3, by native_decide⟩ +
        noncrossingTypeCountsN5 ⟨4, by native_decide⟩ = narayanaRowFive ⟨3, by native_decide⟩ ∧
      noncrossingTypeCountsN5 ⟨5, by native_decide⟩ = narayanaRowFive ⟨4, by native_decide⟩ ∧
      noncrossingTypeCountsN5 ⟨6, by native_decide⟩ = narayanaRowFive ⟨5, by native_decide⟩ := by
  native_decide

/-- The type counts sum to the Catalan number `C_5`. -/
theorem noncrossing_type_counts_total_checked :
    noncrossingTypeCountsN5 ⟨0, by native_decide⟩ +
      noncrossingTypeCountsN5 ⟨1, by native_decide⟩ +
      noncrossingTypeCountsN5 ⟨2, by native_decide⟩ +
      noncrossingTypeCountsN5 ⟨3, by native_decide⟩ +
      noncrossingTypeCountsN5 ⟨4, by native_decide⟩ +
      noncrossingTypeCountsN5 ⟨5, by native_decide⟩ +
      noncrossingTypeCountsN5 ⟨6, by native_decide⟩ = catalanNumber 5 := by
  native_decide

end SingularInversion2
