import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace PolyominoEnumeration

/-!
Finite numerical checks for polyomino and lattice-animal enumeration data
from the Chapter I symbolic-method examples.

The tables are deliberately small: entry `i` is the value for size `i + 1`,
except for the two perimeter tables, where entry `i` is the value for
semi-perimeter `i + 2`.
-/

/-- Fixed polyominoes by area, for areas `1, ..., 12`. -/
def fixedPolyominoByArea : Fin 12 → ℕ :=
  ![1, 2, 6, 19, 63, 216, 760, 2725, 9910, 36446, 135268, 505861]

/-- Free polyominoes by area, for areas `1, ..., 12`. -/
def freePolyominoByArea : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 12, 35, 108, 369, 1285, 4655, 17073, 63600]

/-- Column-convex polyominoes by area, for areas `1, ..., 12`. -/
def columnConvexByArea : Fin 12 → ℕ :=
  ![1, 2, 6, 19, 61, 196, 629, 2017, 6466, 20727, 66441, 212980]

/-- Directed animals on the square lattice by area, for areas `1, ..., 12`. -/
def directedAnimalByArea : Fin 12 → ℕ :=
  ![1, 2, 5, 13, 35, 96, 267, 750, 2123, 6046, 17303, 49721]

/-- Catalan numbers, used for staircase polygons by shifted semi-perimeter. -/
def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Staircase polygons with semi-perimeters `2, ..., 13`. -/
def staircaseBySemiPerimeter : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786]

/-- Bargraphs with semi-perimeters `2, ..., 13`. -/
def bargraphBySemiPerimeter : Fin 12 → ℕ :=
  ![1, 2, 5, 13, 35, 97, 275, 794, 2327, 6905, 20705, 62642]

theorem fixed_polyomino_area_six :
    fixedPolyominoByArea 5 = 216 := by native_decide

theorem fixed_polyomino_area_twelve :
    fixedPolyominoByArea 11 = 505861 := by native_decide

theorem free_polyomino_area_eight :
    freePolyominoByArea 7 = 369 := by native_decide

theorem free_polyomino_area_twelve :
    freePolyominoByArea 11 = 63600 := by native_decide

theorem free_le_fixed_for_small_areas :
    ∀ i : Fin 12, freePolyominoByArea i ≤ fixedPolyominoByArea i := by
  native_decide

theorem fixed_at_most_dihedral_orbit_bound :
    ∀ i : Fin 12, fixedPolyominoByArea i ≤ 8 * freePolyominoByArea i := by
  native_decide

theorem fixed_polyomino_table_sum :
    Finset.univ.sum fixedPolyominoByArea = 691277 := by native_decide

theorem free_polyomino_table_sum :
    Finset.univ.sum freePolyominoByArea = 87146 := by native_decide

theorem column_convex_area_five :
    columnConvexByArea 4 = 61 := by native_decide

theorem column_convex_recurrence_at_area_twelve :
    columnConvexByArea 11 =
      5 * columnConvexByArea 10 - 7 * columnConvexByArea 9 +
        4 * columnConvexByArea 8 := by
  native_decide

theorem column_convex_le_fixed_for_small_areas :
    ∀ i : Fin 12, columnConvexByArea i ≤ fixedPolyominoByArea i := by
  native_decide

theorem directed_animals_area_seven :
    directedAnimalByArea 6 = 267 := by native_decide

theorem directed_animals_table_sum :
    Finset.univ.sum directedAnimalByArea = 76362 := by native_decide

theorem directed_animals_monotone_sample :
    directedAnimalByArea 11 > 2 * directedAnimalByArea 10 := by
  native_decide

theorem staircase_matches_catalan_table :
    ∀ i : Fin 12, staircaseBySemiPerimeter i = catalanNumber i.val := by
  native_decide

theorem staircase_semiperimeter_ten :
    staircaseBySemiPerimeter 8 = 1430 := by native_decide

theorem bargraph_semiperimeter_seven :
    bargraphBySemiPerimeter 5 = 97 := by native_decide

theorem bargraph_table_sum :
    Finset.univ.sum bargraphBySemiPerimeter = 93801 := by native_decide

theorem staircase_le_bargraph_for_small_semiperimeters :
    ∀ i : Fin 12, staircaseBySemiPerimeter i ≤ bargraphBySemiPerimeter i := by
  native_decide

end PolyominoEnumeration
