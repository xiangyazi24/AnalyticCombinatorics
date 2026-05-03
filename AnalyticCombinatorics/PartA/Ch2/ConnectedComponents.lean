import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace ConnectedComponents

/-! # Connected components: finite numerical checks

Small labelled enumeration tables for connected graphs, connected permutations,
Cayley trees, rooted Cayley trees, and ordered set partitions.
-/

/-! ## 1. Connected labelled graphs -/

/-- Connected labelled graph counts `c(n)` for `n = 1, ..., 6`. -/
def connectedGraphTable : Fin 6 → ℕ := ![1, 1, 4, 38, 728, 26704]

/-- Total labelled graph counts `g(n) = 2^C(n,2)` for `n = 1, ..., 6`. -/
def totalGraphTable : Fin 6 → ℕ := ![1, 2, 8, 64, 1024, 32768]

/-- Connected labelled graph count, using the finite table for `1 ≤ n ≤ 6`. -/
def connectedGraphCount : ℕ → ℕ
  | 1 => connectedGraphTable 0
  | 2 => connectedGraphTable 1
  | 3 => connectedGraphTable 2
  | 4 => connectedGraphTable 3
  | 5 => connectedGraphTable 4
  | 6 => connectedGraphTable 5
  | _ => 0

/-- Total labelled graph count, using the finite table for `1 ≤ n ≤ 6`. -/
def totalGraphCount : ℕ → ℕ
  | 1 => totalGraphTable 0
  | 2 => totalGraphTable 1
  | 3 => totalGraphTable 2
  | 4 => totalGraphTable 3
  | 5 => totalGraphTable 4
  | 6 => totalGraphTable 5
  | _ => 0

theorem connectedGraph_values :
    connectedGraphTable 0 = 1 ∧
    connectedGraphTable 1 = 1 ∧
    connectedGraphTable 2 = 4 ∧
    connectedGraphTable 3 = 38 ∧
    connectedGraphTable 4 = 728 ∧
    connectedGraphTable 5 = 26704 := by
  native_decide

theorem totalGraph_values :
    totalGraphTable 0 = 1 ∧
    totalGraphTable 1 = 2 ∧
    totalGraphTable 2 = 8 ∧
    totalGraphTable 3 = 64 ∧
    totalGraphTable 4 = 1024 ∧
    totalGraphTable 5 = 32768 := by
  native_decide

theorem totalGraph_formula_table :
    ∀ i : Fin 6, totalGraphTable i = 2 ^ Nat.choose (i.val + 1) 2 := by
  native_decide

theorem connectedGraph_le_totalGraph_table :
    ∀ i : Fin 6, connectedGraphTable i ≤ totalGraphTable i := by
  native_decide

/-! ## 2. Exponential decomposition for `n = 4` -/

theorem exponential_decomposition_four :
    38 + 16 + 3 + 6 + 1 = 64 := by
  native_decide

theorem exponential_decomposition_four_tables :
    connectedGraphCount 4
      + Nat.choose 4 1 * connectedGraphCount 1 * connectedGraphCount 3
      + (Nat.choose 4 2 / 2) * connectedGraphCount 2 * connectedGraphCount 2
      + Nat.choose 4 2 * connectedGraphCount 2 * connectedGraphCount 1 * connectedGraphCount 1
      + 1
      = totalGraphCount 4 := by
  native_decide

/-! ## 3. Connected permutations -/

/-- Connected permutation counts `cp(n)` for `n = 1, ..., 6`. -/
def connectedPermutationTable : Fin 6 → ℕ := ![1, 1, 3, 13, 71, 461]

/-- Connected permutation count, using the finite table for `1 ≤ n ≤ 6`. -/
def connectedPermutationCount : ℕ → ℕ
  | 1 => connectedPermutationTable 0
  | 2 => connectedPermutationTable 1
  | 3 => connectedPermutationTable 2
  | 4 => connectedPermutationTable 3
  | 5 => connectedPermutationTable 4
  | 6 => connectedPermutationTable 5
  | _ => 0

theorem connectedPermutation_values :
    connectedPermutationTable 0 = 1 ∧
    connectedPermutationTable 1 = 1 ∧
    connectedPermutationTable 2 = 3 ∧
    connectedPermutationTable 3 = 13 ∧
    connectedPermutationTable 4 = 71 ∧
    connectedPermutationTable 5 = 461 := by
  native_decide

theorem connectedPermutation_recurrence_three :
    Nat.factorial 3 =
      ∑ k ∈ Finset.Icc 1 3,
        connectedPermutationCount k * Nat.factorial (3 - k) := by
  native_decide

theorem connectedPermutation_recurrence_four :
    Nat.factorial 4 =
      ∑ k ∈ Finset.Icc 1 4,
        connectedPermutationCount k * Nat.factorial (4 - k) := by
  native_decide

theorem connectedPermutation_recurrence_five :
    Nat.factorial 5 =
      ∑ k ∈ Finset.Icc 1 5,
        connectedPermutationCount k * Nat.factorial (5 - k) := by
  native_decide

/-! ## 4. Cayley trees and rooted Cayley trees -/

/-- Cayley tree counts `n^(n-2)` for `n = 1, ..., 6`. -/
def cayleyTreeTable : Fin 6 → ℕ := ![1, 1, 3, 16, 125, 1296]

/-- Rooted Cayley tree counts `n^(n-1)` for `n = 1, ..., 6`. -/
def rootedCayleyTreeTable : Fin 6 → ℕ := ![1, 2, 9, 64, 625, 7776]

theorem cayleyTree_values :
    cayleyTreeTable 0 = 1 ∧
    cayleyTreeTable 1 = 1 ∧
    cayleyTreeTable 2 = 3 ∧
    cayleyTreeTable 3 = 16 ∧
    cayleyTreeTable 4 = 125 ∧
    cayleyTreeTable 5 = 1296 := by
  native_decide

theorem rootedCayleyTree_values :
    rootedCayleyTreeTable 0 = 1 ∧
    rootedCayleyTreeTable 1 = 2 ∧
    rootedCayleyTreeTable 2 = 9 ∧
    rootedCayleyTreeTable 3 = 64 ∧
    rootedCayleyTreeTable 4 = 625 ∧
    rootedCayleyTreeTable 5 = 7776 := by
  native_decide

theorem cayleyTree_formula_table :
    ∀ i : Fin 6, cayleyTreeTable i = (i.val + 1) ^ (i.val + 1 - 2) := by
  native_decide

theorem rootedCayleyTree_formula_table :
    ∀ i : Fin 6, rootedCayleyTreeTable i = (i.val + 1) ^ (i.val + 1 - 1) := by
  native_decide

/-! ## 5. Graph and tree inequalities -/

theorem connectedGraph_le_totalGraph_one : connectedGraphCount 1 ≤ totalGraphCount 1 := by
  native_decide

theorem connectedGraph_le_totalGraph_two : connectedGraphCount 2 ≤ totalGraphCount 2 := by
  native_decide

theorem connectedGraph_le_totalGraph_three : connectedGraphCount 3 ≤ totalGraphCount 3 := by
  native_decide

theorem connectedGraph_le_totalGraph_four : connectedGraphCount 4 ≤ totalGraphCount 4 := by
  native_decide

theorem connectedGraph_le_totalGraph_five : connectedGraphCount 5 ≤ totalGraphCount 5 := by
  native_decide

theorem connectedGraph_le_totalGraph_six : connectedGraphCount 6 ≤ totalGraphCount 6 := by
  native_decide

theorem cayleyTree_le_connectedGraph_three :
    cayleyTreeTable 2 ≤ connectedGraphTable 2 := by
  native_decide

theorem cayleyTree_le_connectedGraph_four :
    cayleyTreeTable 3 ≤ connectedGraphTable 3 := by
  native_decide

theorem cayleyTree_le_connectedGraph_five :
    cayleyTreeTable 4 ≤ connectedGraphTable 4 := by
  native_decide

theorem cayleyTree_le_connectedGraph_six :
    cayleyTreeTable 5 ≤ connectedGraphTable 5 := by
  native_decide

/-! ## 6. Fubini numbers -/

/-- Fubini numbers `a(n)` for `n = 0, ..., 5`. -/
def fubiniTable : Fin 6 → ℕ := ![1, 1, 3, 13, 75, 541]

/-- Stirling numbers of the second kind `S(3,k)` for `k = 0, ..., 3`. -/
def stirlingSecondRowThree : Fin 4 → ℕ := ![0, 1, 3, 1]

/-- Stirling numbers of the second kind `S(4,k)` for `k = 0, ..., 4`. -/
def stirlingSecondRowFour : Fin 5 → ℕ := ![0, 1, 7, 6, 1]

/-- Fubini number table lookup for `0 ≤ n ≤ 5`. -/
def fubiniNumber : ℕ → ℕ
  | 0 => fubiniTable 0
  | 1 => fubiniTable 1
  | 2 => fubiniTable 2
  | 3 => fubiniTable 3
  | 4 => fubiniTable 4
  | 5 => fubiniTable 5
  | _ => 0

/-- Small table lookup for `S(n,k)`, only populated for `n = 3, 4`. -/
def stirlingSecondSmall : ℕ → ℕ → ℕ
  | 3, 0 => stirlingSecondRowThree 0
  | 3, 1 => stirlingSecondRowThree 1
  | 3, 2 => stirlingSecondRowThree 2
  | 3, 3 => stirlingSecondRowThree 3
  | 4, 0 => stirlingSecondRowFour 0
  | 4, 1 => stirlingSecondRowFour 1
  | 4, 2 => stirlingSecondRowFour 2
  | 4, 3 => stirlingSecondRowFour 3
  | 4, 4 => stirlingSecondRowFour 4
  | _, _ => 0

theorem fubini_values :
    fubiniTable 0 = 1 ∧
    fubiniTable 1 = 1 ∧
    fubiniTable 2 = 3 ∧
    fubiniTable 3 = 13 ∧
    fubiniTable 4 = 75 ∧
    fubiniTable 5 = 541 := by
  native_decide

theorem fubini_formula_three :
    fubiniNumber 3 =
      ∑ k ∈ Finset.range (3 + 1),
        Nat.factorial k * stirlingSecondSmall 3 k := by
  native_decide

theorem fubini_formula_four :
    fubiniNumber 4 =
      ∑ k ∈ Finset.range (4 + 1),
        Nat.factorial k * stirlingSecondSmall 4 k := by
  native_decide

end ConnectedComponents
