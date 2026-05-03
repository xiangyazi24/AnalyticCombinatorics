/-
  Analytic Combinatorics — Part A, Chapter I: Polygon Dissection Enumeration.
  Triangulations of a convex (n+2)-gon = Catalan C(n). Fuss–Catalan numbers
  count k-gon dissections; little Schröder numbers count all non-crossing
  dissections. Reference: Flajolet & Sedgewick, §I.5.3.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace DissectionEnumeration

/-! ## Catalan Numbers -/

def catalan (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

theorem catalan_values :
    [catalan 0, catalan 1, catalan 2, catalan 3, catalan 4,
     catalan 5, catalan 6, catalan 7] =
    [1, 1, 2, 5, 14, 42, 132, 429] := by native_decide

theorem catalan_ballot_0_8 :
    ∀ n ∈ Finset.Icc 0 8,
      catalan n = Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, hhi⟩
  interval_cases n <;> native_decide

theorem catalan_segner_recurrence_0_7 :
    ∀ n ∈ Finset.Icc 0 7,
      catalan (n + 1) =
        ∑ k ∈ Finset.range (n + 1), catalan k * catalan (n - k) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, hhi⟩
  interval_cases n <;> native_decide

theorem catalan_ratio_1_7 :
    ∀ n ∈ Finset.Icc 1 7,
      catalan (n + 1) * (n + 2) = catalan n * (4 * n + 2) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, hhi⟩
  interval_cases n <;> native_decide

/-! ## Triangulations of Convex Polygons

The number of triangulations of a convex polygon with `sides` vertices
equals C(sides − 2). A triangulation draws `sides − 3` non-crossing
diagonals, partitioning the polygon into `sides − 2` triangles. -/

def triangulationCount (n : ℕ) : ℕ := catalan n

def polygonTriangulations (sides : ℕ) : ℕ :=
  if sides < 3 then 0
  else catalan (sides - 2)

theorem triangulation_triangle : polygonTriangulations 3 = 1 := by native_decide
theorem triangulation_square : polygonTriangulations 4 = 2 := by native_decide
theorem triangulation_pentagon : polygonTriangulations 5 = 5 := by native_decide
theorem triangulation_hexagon : polygonTriangulations 6 = 14 := by native_decide
theorem triangulation_heptagon : polygonTriangulations 7 = 42 := by native_decide
theorem triangulation_octagon : polygonTriangulations 8 = 132 := by native_decide

theorem pentagon_eq_catalan_3 : polygonTriangulations 5 = catalan 3 := by native_decide
theorem hexagon_eq_catalan_4 : polygonTriangulations 6 = catalan 4 := by native_decide

theorem euler_segner_pentagon :
    catalan 3 =
      catalan 0 * catalan 2 + catalan 1 * catalan 1 +
      catalan 2 * catalan 0 := by native_decide

theorem euler_segner_hexagon :
    catalan 4 =
      catalan 0 * catalan 3 + catalan 1 * catalan 2 +
      catalan 2 * catalan 1 + catalan 3 * catalan 0 := by native_decide

theorem triangulation_values_3_10 :
    ∀ s ∈ Finset.Icc 3 10,
      polygonTriangulations s = catalan (s - 2) := by
  intro s hs
  rcases Finset.mem_Icc.mp hs with ⟨hlo, hhi⟩
  interval_cases s <;> native_decide

/-! ## Fuss–Catalan Numbers and k-gon Dissections

FC(k, p) = C((k−1)p, p) / ((k−2)p + 1) counts the number of dissections
of a convex ((k−2)p + 2)-gon into exactly p convex k-gons by non-crossing
diagonals. For k = 3 this reduces to the ordinary Catalan number. -/

def fussCatalan (k p : ℕ) : ℕ :=
  if p = 0 then 1
  else if k < 3 then 0
  else Nat.choose ((k - 1) * p) p / ((k - 2) * p + 1)

theorem fuss_catalan_triangulation_0_8 :
    ∀ p ∈ Finset.Icc 0 8, fussCatalan 3 p = catalan p := by
  intro p hp
  rcases Finset.mem_Icc.mp hp with ⟨_, hhi⟩
  interval_cases p <;> native_decide

theorem fussCatalan_specializes_to_catalan (p : ℕ) (hp : p > 0) :
    fussCatalan 3 p = catalan p := by
  unfold fussCatalan catalan
  rw [if_neg (show p ≠ 0 by omega), if_neg (show ¬((3 : ℕ) < 3) by omega)]
  simp only [show (3 : ℕ) - 1 = 2 from by omega,
             show (3 : ℕ) - 2 = 1 from by omega, one_mul]

def quadDissectionCount (p : ℕ) : ℕ := fussCatalan 4 p

theorem quad_dissection_values :
    [quadDissectionCount 0, quadDissectionCount 1, quadDissectionCount 2,
     quadDissectionCount 3, quadDissectionCount 4] =
    [1, 1, 3, 12, 55] := by native_decide

theorem quad_hexagon : quadDissectionCount 2 = 3 := by native_decide
theorem quad_octagon : quadDissectionCount 3 = 12 := by native_decide
theorem quad_decagon : quadDissectionCount 4 = 55 := by native_decide

def pentDissectionCount (p : ℕ) : ℕ := fussCatalan 5 p

theorem pent_dissection_values :
    [pentDissectionCount 0, pentDissectionCount 1,
     pentDissectionCount 2, pentDissectionCount 3] =
    [1, 1, 4, 22] := by native_decide

/-! ## Total Polygon Dissections (Little Schröder Numbers)

The little Schröder number s(n) counts total dissections of a convex
(n+2)-gon by non-crossing diagonals (any piece size ≥ 3, including
the trivial dissection). Recurrence: (n+3)·s(n+2) = (6n+9)·s(n+1) − n·s(n). -/

def littleSchroeder : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => ((6 * n + 9) * littleSchroeder (n + 1) - n * littleSchroeder n) / (n + 3)

theorem littleSchroeder_values :
    [littleSchroeder 0, littleSchroeder 1, littleSchroeder 2,
     littleSchroeder 3, littleSchroeder 4, littleSchroeder 5,
     littleSchroeder 6] =
    [1, 1, 3, 11, 45, 197, 903] := by native_decide

def polygonDissections (sides : ℕ) : ℕ :=
  if sides < 3 then 0
  else littleSchroeder (sides - 2)

theorem dissection_triangle : polygonDissections 3 = 1 := by native_decide
theorem dissection_square : polygonDissections 4 = 3 := by native_decide
theorem dissection_pentagon : polygonDissections 5 = 11 := by native_decide
theorem dissection_hexagon : polygonDissections 6 = 45 := by native_decide
theorem dissection_heptagon : polygonDissections 7 = 197 := by native_decide

theorem schroeder_recurrence_2_6 :
    ∀ n ∈ Finset.Icc 2 6,
      (n + 1) * littleSchroeder n =
        (6 * n - 3) * littleSchroeder (n - 1) -
        (n - 2) * littleSchroeder (n - 2) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, hhi⟩
  interval_cases n <;> native_decide

/-! ## Relationships Between Dissection Counts -/

theorem triangulation_le_total_3_10 :
    ∀ s ∈ Finset.Icc 3 10,
      polygonTriangulations s ≤ polygonDissections s := by
  intro s hs
  rcases Finset.mem_Icc.mp hs with ⟨_, hhi⟩
  interval_cases s <;> native_decide

theorem total_gt_triangulation_4_10 :
    ∀ s ∈ Finset.Icc 4 10,
      polygonDissections s > polygonTriangulations s := by
  intro s hs
  rcases Finset.mem_Icc.mp hs with ⟨_, hhi⟩
  interval_cases s <;> native_decide

theorem fussCatalan_single_piece_3_10 :
    ∀ k ∈ Finset.Icc 3 10, fussCatalan k 1 = 1 := by
  intro k hk
  rcases Finset.mem_Icc.mp hk with ⟨_, hhi⟩
  interval_cases k <;> native_decide

theorem schroeder_growth_1_5 :
    ∀ n ∈ Finset.Icc 1 5,
      littleSchroeder (n + 1) > 2 * littleSchroeder n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, hhi⟩
  interval_cases n <;> native_decide

theorem schroeder_recurrence_general (n : ℕ) (hn : n ≥ 2) :
    (n + 1) * littleSchroeder n =
      (6 * n - 3) * littleSchroeder (n - 1) -
      (n - 2) * littleSchroeder (n - 2) := by
  sorry

end DissectionEnumeration
