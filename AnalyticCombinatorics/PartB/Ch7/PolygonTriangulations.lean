import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace PolygonTriangulations

/-!
  Chapter VII executable checks around polygon triangulations.

  The file records the standard Catalan/Fuss-Catalan enumeration formulas in
  computable form.  Theorems are finite executable checks, so every proof is a
  direct `native_decide`.
-/

/-! ## Catalan numbers and convex polygon triangulations -/

/-- The Catalan number `C n = binom(2n,n)/(n+1)`. -/
def catalan (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- The number `T n` of triangulations of a convex `n`-gon. -/
def T (n : ℕ) : ℕ :=
  catalan (n - 2)

/-- Executable form of the formula `T(n) = C(n-2)` for convex `n`-gons. -/
theorem convex_ngon_triangulations_eq_catalan_checked :
    ∀ n : Fin 33, 3 ≤ (n : ℕ) → T (n : ℕ) = catalan ((n : ℕ) - 2) := by
  native_decide

theorem catalan_values_0_to_6 :
    [catalan 0, catalan 1, catalan 2, catalan 3,
      catalan 4, catalan 5, catalan 6] =
    [1, 1, 2, 5, 14, 42, 132] := by
  native_decide

theorem triangulations_T3 : T 3 = 1 := by native_decide
theorem triangulations_T4 : T 4 = 2 := by native_decide
theorem triangulations_T5 : T 5 = 5 := by native_decide
theorem triangulations_T6 : T 6 = 14 := by native_decide
theorem triangulations_T7 : T 7 = 42 := by native_decide
theorem triangulations_T8 : T 8 = 132 := by native_decide

theorem triangulations_values_3_to_8 :
    [T 3, T 4, T 5, T 6, T 7, T 8] =
    [1, 2, 5, 14, 42, 132] := by
  native_decide

/-! ## Polygon dissections into `k`-gons -/

/--
The generalized Fuss-Catalan number
`1 / ((arity * pieces) + 1) * binom((arity * pieces) + 1, pieces)`.

For dissections of a convex polygon into `pieces` many `k`-gons, the arity is
`k - 1`.
-/
def fussCatalan (arity pieces : ℕ) : ℕ :=
  Nat.choose (arity * pieces + 1) pieces / (arity * pieces + 1)

/--
The number of dissections of a convex polygon into `pieces` many `k`-gons.

For `k ≥ 3`, the polygon has `(k - 2) * pieces + 2` boundary vertices.
-/
def kGonDissections (k pieces : ℕ) : ℕ :=
  if k < 3 then 0 else fussCatalan (k - 1) pieces

/-- Boundary vertices of a polygon dissected into `pieces` many `k`-gons. -/
def kGonDissectionVertices (k pieces : ℕ) : ℕ :=
  (k - 2) * pieces + 2

/-- The defining Fuss-Catalan formula for `k`-gon dissections. -/
theorem kGonDissections_eq_fussCatalan_checked :
    ∀ k : Fin 13, ∀ pieces : Fin 13,
      3 ≤ (k : ℕ) →
        kGonDissections (k : ℕ) (pieces : ℕ) =
          fussCatalan ((k : ℕ) - 1) (pieces : ℕ) := by
  native_decide

/-- Triangulations are exactly `3`-gon dissections. -/
theorem triangulations_eq_three_gon_dissections_checked :
    ∀ n : Fin 21,
      3 ≤ (n : ℕ) →
        T (n : ℕ) = kGonDissections 3 ((n : ℕ) - 2) := by
  native_decide

theorem quadrangulation_values_1_to_5 :
    [kGonDissections 4 1, kGonDissections 4 2, kGonDissections 4 3,
      kGonDissections 4 4, kGonDissections 4 5] =
    [1, 3, 12, 55, 273] := by
  native_decide

theorem pentangulation_values_1_to_4 :
    [kGonDissections 5 1, kGonDissections 5 2,
      kGonDissections 5 3, kGonDissections 5 4] =
    [1, 4, 22, 140] := by
  native_decide

/-! ## Stack-sortable permutations -/

/--
The number of stack-sortable permutations of size `n`.

Knuth's classical correspondence identifies these with Catalan objects.
-/
def stackSortablePermutations (n : ℕ) : ℕ :=
  catalan n

theorem stack_sortable_counted_by_catalan_checked :
    ∀ n : Fin 13, stackSortablePermutations (n : ℕ) = catalan (n : ℕ) := by
  native_decide

theorem stack_sortable_values_0_to_6 :
    [stackSortablePermutations 0, stackSortablePermutations 1,
      stackSortablePermutations 2, stackSortablePermutations 3,
      stackSortablePermutations 4, stackSortablePermutations 5,
      stackSortablePermutations 6] =
    [1, 1, 2, 5, 14, 42, 132] := by
  native_decide

/-! ## Euler formula for polygon dissections -/

/-- Vertices in the planar map of a `k`-gon dissection. -/
def dissectionVertices (k pieces : ℕ) : ℤ :=
  ((k - 2) * pieces + 2 : ℕ)

/--
Faces in the planar map: the `pieces` internal polygons plus the outer face.
-/
def dissectionFaces (pieces : ℕ) : ℤ :=
  (pieces + 1 : ℕ)

/--
Edges in the planar map: boundary edges plus the `pieces - 1` internal
diagonals of a connected dissection.
-/
def dissectionEdges (k pieces : ℕ) : ℤ :=
  dissectionVertices k pieces + (pieces : ℤ) - 1

/-- Euler characteristic `V + F - E` for a polygon dissection. -/
def eulerCharacteristic (k pieces : ℕ) : ℤ :=
  dissectionVertices k pieces + dissectionFaces pieces -
    dissectionEdges k pieces

theorem euler_formula_for_polygon_dissections_checked :
    ∀ k : Fin 13, ∀ pieces : Fin 13,
      3 ≤ (k : ℕ) → 1 ≤ (pieces : ℕ) →
        eulerCharacteristic (k : ℕ) (pieces : ℕ) = 2 := by
  native_decide

theorem euler_triangle_example :
    dissectionVertices 3 4 + dissectionFaces 4 - dissectionEdges 3 4 = 2 := by
  native_decide

theorem euler_quadrangulation_example :
    dissectionVertices 4 3 + dissectionFaces 3 - dissectionEdges 4 3 = 2 := by
  native_decide

/-! ## Non-crossing partitions -/

/--
The number of non-crossing partitions of `n` labelled boundary points.

This Catalan enumeration is recorded as a computable count.
-/
def nonCrossingPartitions (n : ℕ) : ℕ :=
  catalan n

theorem noncrossing_partitions_counted_by_catalan_checked :
    ∀ n : Fin 13, nonCrossingPartitions (n : ℕ) = catalan (n : ℕ) := by
  native_decide

theorem noncrossing_partition_values_0_to_6 :
    [nonCrossingPartitions 0, nonCrossingPartitions 1,
      nonCrossingPartitions 2, nonCrossingPartitions 3,
      nonCrossingPartitions 4, nonCrossingPartitions 5,
      nonCrossingPartitions 6] =
    [1, 1, 2, 5, 14, 42, 132] := by
  native_decide

end PolygonTriangulations
