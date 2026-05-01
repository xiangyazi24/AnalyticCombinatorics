import AnalyticCombinatorics.Examples.BinaryTrees
import AnalyticCombinatorics.Examples.PlaneTrees
import AnalyticCombinatorics.Examples.Triangulations
import AnalyticCombinatorics.Examples.DyckPaths

example : BinTree.asClass.count 5 = dyckPathClass.count 5 := by
  rw [show BinTree.asClass.count 5 = BinTree.catalan 5 from rfl,
      BinTree.catalan_eq_nat_catalan, dyckPathClass_count]

theorem binTree_count_eq_planeTree (n : ℕ) :
    BinTree.asClass.count n = planeTreeClass.count n := by
  rw [show BinTree.asClass.count n = BinTree.catalan n from rfl,
      BinTree.catalan_eq_nat_catalan, planeTreeClass_count]

theorem binTree_count_eq_triangulation (n : ℕ) :
    BinTree.asClass.count n = triangulationClass.count n := by
  rw [show BinTree.asClass.count n = BinTree.catalan n from rfl,
      BinTree.catalan_eq_nat_catalan, triangulationClass_count]

theorem binTree_count_eq_dyckPath (n : ℕ) :
    BinTree.asClass.count n = dyckPathClass.count n := by
  rw [show BinTree.asClass.count n = BinTree.catalan n from rfl,
      BinTree.catalan_eq_nat_catalan, dyckPathClass_count]

theorem planeTree_count_eq_triangulation (n : ℕ) :
    planeTreeClass.count n = triangulationClass.count n := by
  rw [planeTreeClass_count, triangulationClass_count]

theorem planeTree_count_eq_dyckPath (n : ℕ) :
    planeTreeClass.count n = dyckPathClass.count n := by
  rw [planeTreeClass_count, dyckPathClass_count]

theorem triangulation_count_eq_dyckPath (n : ℕ) :
    triangulationClass.count n = dyckPathClass.count n := by
  rw [triangulationClass_count, dyckPathClass_count]

/-- Classical Catalan recurrence.

This Mathlib snapshot exposes Catalan numbers as the root-level `_root_.catalan`,
not as `Nat.catalan`; the proof is just Mathlib's `catalan_succ` rewritten from
the finite-type sum to an explicit `Finset.range`. -/
theorem catalan_recurrence (n : ℕ) :
    _root_.catalan (n + 1) =
      ∑ i ∈ Finset.range (n + 1), _root_.catalan i * _root_.catalan (n - i) := by
  rw [Finset.sum_range]
  exact _root_.catalan_succ n
