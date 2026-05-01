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
