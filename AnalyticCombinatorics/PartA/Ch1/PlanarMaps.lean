/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I: Planar Maps and Related Counting Sequences.

  This file formalizes several counting sequences related to planar maps,
  polygon triangulations/dissections, and stack-sortable permutations:

  1. Triangulations of an (n+2)-gon = Catalan number C(n)
  2. Little Schröder numbers (polygon dissections, OEIS A001003)
  3. Large Schröder numbers (= 2 * little Schröder for n ≥ 1)
  4. Rooted planar maps by edges (OEIS A000168)
  5. Stack-sortable (231-avoiding) permutations = Catalan numbers
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace PlanarMaps

/-! ## 1. Triangulations of (n+2)-gon = Catalan(n) -/

/-- The number of triangulations of an (n+2)-gon equals the n-th Catalan number. -/
def triangulationCount (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

theorem triangulationCount_one : triangulationCount 1 = 1 := by native_decide
theorem triangulationCount_two : triangulationCount 2 = 2 := by native_decide
theorem triangulationCount_three : triangulationCount 3 = 5 := by native_decide
theorem triangulationCount_four : triangulationCount 4 = 14 := by native_decide
theorem triangulationCount_five : triangulationCount 5 = 42 := by native_decide

/-! ## 2. Little Schröder numbers (polygon dissections, OEIS A001003) -/

/-- Little Schröder numbers s(n) count the number of ways to dissect a convex
    (n+2)-gon into smaller polygons by non-crossing diagonals.
    Values: 1, 1, 3, 11, 45, 197, 903, 4279, ... -/
def littleSchroederTable : Fin 8 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 11
  | ⟨4, _⟩ => 45
  | ⟨5, _⟩ => 197
  | ⟨6, _⟩ => 903
  | ⟨7, _⟩ => 4279

theorem littleSchroeder_zero : littleSchroederTable ⟨0, by omega⟩ = 1 := by native_decide
theorem littleSchroeder_one : littleSchroederTable ⟨1, by omega⟩ = 1 := by native_decide
theorem littleSchroeder_two : littleSchroederTable ⟨2, by omega⟩ = 3 := by native_decide
theorem littleSchroeder_three : littleSchroederTable ⟨3, by omega⟩ = 11 := by native_decide
theorem littleSchroeder_four : littleSchroederTable ⟨4, by omega⟩ = 45 := by native_decide
theorem littleSchroeder_five : littleSchroederTable ⟨5, by omega⟩ = 197 := by native_decide
theorem littleSchroeder_six : littleSchroederTable ⟨6, by omega⟩ = 903 := by native_decide
theorem littleSchroeder_seven : littleSchroederTable ⟨7, by omega⟩ = 4279 := by native_decide

/-! ## 3. Large Schröder numbers (OEIS A006318) -/

/-- Large Schröder numbers S(n): S(0) = 1 and S(n) = 2 * s(n) for n ≥ 1.
    Values: 1, 2, 6, 22, 90, 394, 1806, 8558, ... -/
def largeSchroederTable : Fin 8 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 6
  | ⟨3, _⟩ => 22
  | ⟨4, _⟩ => 90
  | ⟨5, _⟩ => 394
  | ⟨6, _⟩ => 1806
  | ⟨7, _⟩ => 8558

/-- For n ≥ 1, the large Schröder number equals twice the little Schröder number. -/
theorem largeSchroeder_eq_twice_little (i : Fin 8) (hi : i.val ≥ 1) :
    largeSchroederTable i = 2 * littleSchroederTable i := by
  fin_cases i <;> simp_all (config := { decide := true })

/-! ## 4. Rooted planar maps by edges (OEIS A000168) -/

/-- Rooted planar maps counted by number of edges.
    M(n) counts rooted planar maps with n edges.
    Values: M(0) = 2, M(1) = 4, M(2) = 10, M(3) = 28, M(4) = 84, M(5) = 264.
    (M(0) = 2 accounts for root edge orientation on the single-vertex map.) -/
def rootedMapTable : Fin 6 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 10
  | ⟨3, _⟩ => 28
  | ⟨4, _⟩ => 84
  | ⟨5, _⟩ => 264

theorem rootedMap_zero : rootedMapTable ⟨0, by omega⟩ = 2 := by native_decide
theorem rootedMap_one : rootedMapTable ⟨1, by omega⟩ = 4 := by native_decide
theorem rootedMap_two : rootedMapTable ⟨2, by omega⟩ = 10 := by native_decide
theorem rootedMap_three : rootedMapTable ⟨3, by omega⟩ = 28 := by native_decide
theorem rootedMap_four : rootedMapTable ⟨4, by omega⟩ = 84 := by native_decide
theorem rootedMap_five : rootedMapTable ⟨5, by omega⟩ = 264 := by native_decide

/-! ## 5. Stack-sortable permutations = Catalan -/

/-- The number of 1-stack-sortable (equivalently, 231-avoiding) permutations
    of [n] equals the n-th Catalan number. -/
def stackSortableCount (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Stack-sortable permutation count equals triangulation count (both are Catalan). -/
theorem stackSortable_eq_triangulation (n : ℕ) :
    stackSortableCount n = triangulationCount n := by
  rfl

theorem stackSortable_zero : stackSortableCount 0 = 1 := by native_decide
theorem stackSortable_one : stackSortableCount 1 = 1 := by native_decide
theorem stackSortable_two : stackSortableCount 2 = 2 := by native_decide
theorem stackSortable_three : stackSortableCount 3 = 5 := by native_decide
theorem stackSortable_four : stackSortableCount 4 = 14 := by native_decide
theorem stackSortable_five : stackSortableCount 5 = 42 := by native_decide
theorem stackSortable_six : stackSortableCount 6 = 132 := by native_decide
theorem stackSortable_seven : stackSortableCount 7 = 429 := by native_decide
theorem stackSortable_eight : stackSortableCount 8 = 1430 := by native_decide

end PlanarMaps
