import AnalyticCombinatorics.Examples.BinaryTrees

/-- A triangulation of a convex (n+2)-gon is the same data as a binary tree
    with n internal nodes (well-known bijection: each triangle ↔ internal node). -/
noncomputable def triangulationClass : CombinatorialClass := BinTree.asClass

/-- Count of triangulations of an (n+2)-gon equals the n-th Catalan number. -/
theorem triangulationClass_count (n : ℕ) :
    triangulationClass.count n = _root_.catalan n := by
  rw [show triangulationClass = BinTree.asClass from rfl]
  exact BinTree.catalan_eq_nat_catalan n
