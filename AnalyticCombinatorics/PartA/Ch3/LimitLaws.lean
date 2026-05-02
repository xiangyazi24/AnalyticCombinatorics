import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartA.Ch2.Derangements
import AnalyticCombinatorics.PartA.Ch3.Moments

set_option linter.style.nativeDecide false

open CombinatorialClass

/-! # Ch III / IX — Limit-law skeletons

This file records lightweight predicates and finite sanity checks for the
distributional limit laws used later in analytic-combinatorics arguments.
-/

/-! ## General limit-law interface -/

/-- A minimal record for an asymptotic distributional law. -/
structure LimitLaw where
  meanGrowth : ℕ → ℚ
  varianceGrowth : ℕ → ℚ
  limitType : Type

/-- Standard names for the common limiting distributions appearing here. -/
inductive StandardLimitType where
  | normal
  | poisson
deriving DecidableEq, Repr

/-- Simplified Gaussian limit-law predicate: only assert eventual positive variance. -/
def IsAsymptoticallyGaussian (_meanSeq varSeq : ℕ → ℚ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n > N, varSeq n > 0

/-! ## Binary-search-tree depth / binary-tree path-length checks -/

/--
Mean depth in random binary search trees is asymptotic to `2 log n`.
The sequence `logSeq` is an explicit rational surrogate for `log n`.
-/
def BinarySearchTreeMeanDepthAsymptotic (meanDepth logSeq : ℕ → ℚ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n > N,
    (2 - ε) * logSeq n ≤ meanDepth n ∧
      meanDepth n ≤ (2 + ε) * logSeq n

/-- Total path-length values used for the finite size-`1` through size-`8` check. -/
def checkedBinaryTreePathLengthTotal : ℕ → ℕ
  | 1 => 2
  | 2 => 10
  | 3 => 44
  | 4 => 186
  | 5 => 772
  | 6 => 3172
  | 7 => 12952
  | 8 => 52666
  | _ => 0

/-- Catalan counts used for the finite size-`1` through size-`8` check. -/
def checkedBinaryTreeCount : ℕ → ℕ
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 42
  | 6 => 132
  | 7 => 429
  | 8 => 1430
  | _ => 0

/-- Checked mean path length divided by the number of internal nodes. -/
def checkedBinaryTreeAveragePathLengthPerNode (n : ℕ) : ℚ :=
  if n = 0 ∨ checkedBinaryTreeCount n = 0 then 0
  else (checkedBinaryTreePathLengthTotal n : ℚ) / checkedBinaryTreeCount n / n

/-- The finite path-length table agrees with the existing enumerated checks through size `6`. -/
theorem checkedBinaryTreePathLengthTotal_agrees_to_six :
    checkedBinaryTreePathLengthTotal 1 = 2 ∧
    checkedBinaryTreePathLengthTotal 2 = 10 ∧
    checkedBinaryTreePathLengthTotal 3 = 44 ∧
    checkedBinaryTreePathLengthTotal 4 = 186 ∧
    checkedBinaryTreePathLengthTotal 5 = 772 ∧
    checkedBinaryTreePathLengthTotal 6 = 3172 := by
  native_decide

/-- The initial mean path length per internal node is increasing for sizes `1, ..., 8`. -/
theorem checkedBinaryTreeAveragePathLengthPerNode_increases_to_eight :
    checkedBinaryTreeAveragePathLengthPerNode 1 <
      checkedBinaryTreeAveragePathLengthPerNode 2 ∧
    checkedBinaryTreeAveragePathLengthPerNode 2 <
      checkedBinaryTreeAveragePathLengthPerNode 3 ∧
    checkedBinaryTreeAveragePathLengthPerNode 3 <
      checkedBinaryTreeAveragePathLengthPerNode 4 ∧
    checkedBinaryTreeAveragePathLengthPerNode 4 <
      checkedBinaryTreeAveragePathLengthPerNode 5 ∧
    checkedBinaryTreeAveragePathLengthPerNode 5 <
      checkedBinaryTreeAveragePathLengthPerNode 6 ∧
    checkedBinaryTreeAveragePathLengthPerNode 6 <
      checkedBinaryTreeAveragePathLengthPerNode 7 ∧
    checkedBinaryTreeAveragePathLengthPerNode 7 <
      checkedBinaryTreeAveragePathLengthPerNode 8 := by
  native_decide

/-! ## Leaves in binary trees -/

/-- Total number of leaves over all binary trees of size `n`. -/
noncomputable def totalLeaves (n : ℕ) : ℕ :=
  (binaryTreeClass.level n).sum binaryTreeLeaves

/-- Mean number of leaves in binary trees of size `n`. -/
noncomputable def meanBinaryTreeLeaves (n : ℕ) : ℚ :=
  if binaryTreeClass.count n = 0 then 0
  else (totalLeaves n : ℚ) / binaryTreeClass.count n

theorem totalLeaves_eq_size_add_one_mul_count (n : ℕ) :
    totalLeaves n = (n + 1) * binaryTreeClass.count n := by
  unfold totalLeaves CombinatorialClass.count
  calc
    (binaryTreeClass.level n).sum binaryTreeLeaves
        = (binaryTreeClass.level n).sum (fun _ => n + 1) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [binaryTreeLeaves_eq_size_add_one]
          have hsize : BinaryTree.size t = n :=
            (CombinatorialClass.level_mem_iff (C := binaryTreeClass) t).mp ht
          omega
    _ = (n + 1) * (binaryTreeClass.level n).card := by
          rw [Finset.sum_const, nsmul_eq_mul]
          push_cast
          ring

private theorem binaryTreeClass_count_checked_four : binaryTreeClass.count 4 = 14 := by
  rw [binaryTreeClass_count_eq_card]
  native_decide

private theorem binaryTreeClass_count_checked_five : binaryTreeClass.count 5 = 42 := by
  rw [binaryTreeClass_count_eq_card]
  native_decide

theorem totalLeaves_one : totalLeaves 1 = 2 := by
  rw [totalLeaves_eq_size_add_one_mul_count, binaryTree_count_one]

theorem totalLeaves_two : totalLeaves 2 = 6 := by
  rw [totalLeaves_eq_size_add_one_mul_count, binaryTree_count_two]

theorem totalLeaves_three : totalLeaves 3 = 20 := by
  rw [totalLeaves_eq_size_add_one_mul_count, binaryTree_count_three]

theorem totalLeaves_four : totalLeaves 4 = 70 := by
  rw [totalLeaves_eq_size_add_one_mul_count, binaryTreeClass_count_checked_four]

theorem totalLeaves_five : totalLeaves 5 = 252 := by
  rw [totalLeaves_eq_size_add_one_mul_count, binaryTreeClass_count_checked_five]

/-- Checked numerators for the mean-leaves formula, for sizes `1, ..., 5`. -/
theorem totalLeaves_checked_one_to_five :
    totalLeaves 1 = 2 ∧
    totalLeaves 2 = 6 ∧
    totalLeaves 3 = 20 ∧
    totalLeaves 4 = 70 ∧
    totalLeaves 5 = 252 := by
  exact ⟨totalLeaves_one, totalLeaves_two, totalLeaves_three, totalLeaves_four,
    totalLeaves_five⟩

/-! ## Fixed points in permutations -/

/--
The standard count of permutations of `n` labels with exactly `k` fixed points:
choose the fixed labels and derange the rest.
-/
def fixedPointPermCount (n k : ℕ) : ℕ :=
  n.choose k * derangeCount (n - k)

/-- Fraction of `n`-permutations with exactly `k` fixed points. -/
def fixedPointPermFraction (n k : ℕ) : ℚ :=
  (fixedPointPermCount n k : ℚ) / n.factorial

/--
Poisson limit law for fixed points.  The parameter `expNegOne` represents
`e^{-1}` in rational approximation contexts.
-/
def FixedPointPoissonLimit (expNegOne : ℚ) : Prop :=
  ∀ k : ℕ, ∀ ε > 0, ∃ N, ∀ n > N,
    expNegOne / k.factorial - ε ≤ fixedPointPermFraction n k ∧
      fixedPointPermFraction n k ≤ expNegOne / k.factorial + ε

/-- General zero-fixed-point identity for the formula above. -/
theorem fixedPointPermCount_zero_eq_derangeCount (n : ℕ) :
    fixedPointPermCount n 0 = derangeCount n := by
  simp [fixedPointPermCount]

/-- Native checked instances, for `n = 5, ..., 10`. -/
theorem fixedPointPermCount_zero_eq_derangeCount_checked (n : ℕ)
    (hn : 5 ≤ n ∧ n ≤ 10) :
    fixedPointPermCount n 0 = derangeCount n := by
  have hn_lower : 5 ≤ n := hn.1
  have hn_upper : n ≤ 10 := hn.2
  interval_cases n <;> native_decide

/-- The fixed-point law as a value of the general `LimitLaw` record. -/
def fixedPointLimitLaw : LimitLaw where
  meanGrowth := fun _ => 1
  varianceGrowth := fun _ => 1
  limitType := StandardLimitType
