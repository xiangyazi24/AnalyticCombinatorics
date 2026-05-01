import Mathlib.Data.Nat.Choose.Central
import AnalyticCombinatorics.Examples.BinaryTrees

/-- A triangulation of a convex (n+2)-gon is the same data as a binary tree
    with n internal nodes (well-known bijection: each triangle ↔ internal node). -/
noncomputable def triangulationClass : CombinatorialClass := BinTree.asClass

/-- Count of triangulations of an (n+2)-gon equals the n-th Catalan number. -/
theorem triangulationClass_count (n : ℕ) :
    triangulationClass.count n = _root_.catalan n := by
  rw [show triangulationClass = BinTree.asClass from rfl]
  exact BinTree.catalan_eq_nat_catalan n

example : triangulationClass.count 0 = 1 := by rw [triangulationClass_count, catalan_zero]
example : triangulationClass.count 1 = 1 := by rw [triangulationClass_count, catalan_one]
example : triangulationClass.count 2 = 2 := by rw [triangulationClass_count, catalan_two]
example : triangulationClass.count 3 = 5 := by rw [triangulationClass_count, catalan_three]
example : triangulationClass.count 4 = 14 := by
  rw [triangulationClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : triangulationClass.count 5 = 42 := by
  rw [triangulationClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : triangulationClass.count 6 = 132 := by
  rw [triangulationClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : triangulationClass.count 7 = 429 := by
  rw [triangulationClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : triangulationClass.count 8 = 1430 := by
  rw [triangulationClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

/-- (n+1) · #triangulations of (n+2)-gon = C(2n, n) (central binomial). -/
theorem succ_mul_triangulationClass_count_eq_centralBinom (n : ℕ) :
    (n + 1) * triangulationClass.count n = n.centralBinom := by
  exact BinTree.succ_mul_catalan_eq_centralBinom n

/-- Closed form: #triangulations of (n+2)-gon = C(2n,n) / (n+1). -/
theorem triangulationClass_count_eq_centralBinom_div (n : ℕ) :
    triangulationClass.count n = n.centralBinom / (n + 1) := by
  exact BinTree.catalan_eq_centralBinom_div n

/-- The triangulation class OGF satisfies the same quadratic as BinTree. -/
example :
    PowerSeries.X * (ogfZ triangulationClass) ^ 2
      - ogfZ triangulationClass + 1 = 0 := by
  change PowerSeries.X * (ogfZ BinTree.asClass) ^ 2
        - ogfZ BinTree.asClass + 1 = 0
  exact BinTree.ogfZ_quadratic
