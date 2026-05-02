import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartA.Ch3.Parameters
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open CombinatorialClass

/-! # Ch III — Moments of Parameters

This file records the elementary finite-level moment definitions used for
combinatorial parameters, together with small binary-tree checks.
-/

namespace CombinatorialClass

/-- Second moment of a parameter among objects of size `n`.
Empty levels have second moment `0`. -/
noncomputable def secondMomentParam (A : CombinatorialClass) (cost : A.Obj → ℕ)
    (n : ℕ) : ℚ :=
  if A.count n = 0 then 0
  else (∑ k ∈ (A.level n).image cost, ((k * k * A.jointCount cost n k : ℕ) : ℚ)) / A.count n

/-- Variance of a parameter among objects of size `n`.
Empty levels have variance `0`. -/
noncomputable def varianceParam (A : CombinatorialClass) (cost : A.Obj → ℕ)
    (n : ℕ) : ℚ :=
  A.secondMomentParam cost n - (A.meanParam cost n) ^ 2

end CombinatorialClass

/-! ## Binary-tree parameters -/

/-- Number of leaves in a binary tree. -/
def binaryTreeLeaves : BinaryTree → ℕ
  | .leaf => 1
  | .node l r => binaryTreeLeaves l + binaryTreeLeaves r

/-- Sum of leaf depths in a binary tree, under the recursion specified in Chapter III checks. -/
def binaryTreePathLength : BinaryTree → ℕ
  | .leaf => 0
  | .node l r => binaryTreePathLength l + binaryTreePathLength r +
      binaryTreeLeaves l + binaryTreeLeaves r

theorem binaryTreeLeaves_eq_size_add_one (t : BinaryTree) :
    binaryTreeLeaves t = BinaryTree.size t + 1 := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      simp [binaryTreeLeaves, BinaryTree.size, ihl, ihr]
      omega

/-! ### Cumulated leaves -/

example : binaryTreeClass.cumulatedCost binaryTreeLeaves 0 = 1 := by
  rw [CombinatorialClass.cumulatedCost_eq_sum_param, binaryTreeClass_level_eq]
  native_decide

example : binaryTreeClass.cumulatedCost binaryTreeLeaves 1 = 2 := by
  rw [CombinatorialClass.cumulatedCost_eq_sum_param, binaryTreeClass_level_eq]
  native_decide

example : binaryTreeClass.cumulatedCost binaryTreeLeaves 2 = 6 := by
  rw [CombinatorialClass.cumulatedCost_eq_sum_param, binaryTreeClass_level_eq]
  native_decide

example : binaryTreeClass.cumulatedCost binaryTreeLeaves 3 = 20 := by
  rw [CombinatorialClass.cumulatedCost_eq_sum_param, binaryTreeClass_level_eq]
  native_decide

example : binaryTreeClass.cumulatedCost binaryTreeLeaves 4 = 70 := by
  rw [CombinatorialClass.cumulatedCost_eq_sum_param, binaryTreeClass_level_eq]
  native_decide

/-! ### Cumulated path length -/

example : binaryTreeClass.cumulatedCost binaryTreePathLength 0 = 0 := by
  rw [CombinatorialClass.cumulatedCost_eq_sum_param, binaryTreeClass_level_eq]
  native_decide

example : binaryTreeClass.cumulatedCost binaryTreePathLength 1 = 2 := by
  rw [CombinatorialClass.cumulatedCost_eq_sum_param, binaryTreeClass_level_eq]
  native_decide

example : binaryTreeClass.cumulatedCost binaryTreePathLength 2 = 10 := by
  rw [CombinatorialClass.cumulatedCost_eq_sum_param, binaryTreeClass_level_eq]
  native_decide

example : binaryTreeClass.cumulatedCost binaryTreePathLength 3 = 44 := by
  rw [CombinatorialClass.cumulatedCost_eq_sum_param, binaryTreeClass_level_eq]
  native_decide

example : binaryTreeClass.cumulatedCost binaryTreePathLength 4 = 186 := by
  rw [CombinatorialClass.cumulatedCost_eq_sum_param, binaryTreeClass_level_eq]
  native_decide

/-! ### Initial growth sanity check -/

/-- Average path length divided by the number of internal nodes. -/
noncomputable def binaryTreeAveragePathLengthPerNode (n : ℕ) : ℚ :=
  if n = 0 then 0 else binaryTreeClass.meanParam binaryTreePathLength n / n

theorem binaryTreeAveragePathLengthPerNode_increases_to_six :
    binaryTreeAveragePathLengthPerNode 1 <
      binaryTreeAveragePathLengthPerNode 2 ∧
    binaryTreeAveragePathLengthPerNode 2 <
      binaryTreeAveragePathLengthPerNode 3 ∧
    binaryTreeAveragePathLengthPerNode 3 <
      binaryTreeAveragePathLengthPerNode 4 ∧
    binaryTreeAveragePathLengthPerNode 4 <
      binaryTreeAveragePathLengthPerNode 5 ∧
    binaryTreeAveragePathLengthPerNode 5 <
      binaryTreeAveragePathLengthPerNode 6 := by
  simp only [binaryTreeAveragePathLengthPerNode, CombinatorialClass.meanParam,
    CombinatorialClass.jointCount, binaryTreeClass_count_eq_card, binaryTreeClass_level_eq,
    Nat.reduceEqDiff, ↓reduceIte, Nat.cast_ofNat, OfNat.ofNat_ne_zero, div_eq_inv_mul]
  native_decide
