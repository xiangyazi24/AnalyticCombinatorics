import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace YoungTableaux

open Finset

/-!
Finite checks for Young tableaux and the Robinson-Schensted correspondence
from Chapter II of Analytic Combinatorics.
-/

/-! ## Hook lengths and standard Young tableaux -/

/-- Number of cells in a Young diagram represented by row lengths. -/
def shapeSize {h : Nat} (rows : Fin h -> Nat) : Nat :=
  ∑ i : Fin h, rows i

/-- Number of cells strictly below `(i,j)` in the same column. -/
def legLength {h : Nat} (rows : Fin h -> Nat) (i : Fin h) (j : Nat) : Nat :=
  ((Finset.univ : Finset (Fin h)).filter fun r => i.val < r.val ∧ j < rows r).card

/-- Hook length at zero-indexed cell `(i,j)`, for `j < rows i`. -/
def hookLength {h : Nat} (rows : Fin h -> Nat) (i : Fin h) (j : Nat) : Nat :=
  rows i - j + legLength rows i j

/-- Product of hook lengths over all cells of the diagram. -/
def hookProduct {h : Nat} (rows : Fin h -> Nat) : Nat :=
  ∏ i : Fin h, ∏ j ∈ Finset.range (rows i), hookLength rows i j

/-- The hook-length formula value `f^lambda = n! / product hook lengths`. -/
def sytByHook {h : Nat} (rows : Fin h -> Nat) : Nat :=
  Nat.factorial (shapeSize rows) / hookProduct rows

def oneRowShape (n : Nat) : Fin 1 -> Nat := ![n]

def oneColumnShape (n : Nat) : Fin n -> Nat := fun _ => 1

theorem one_row_shape_syt_count :
    ∀ i : Fin 8, sytByHook (oneRowShape (i.val + 1)) = 1 := by
  native_decide

theorem one_column_shape_syt_count :
    ∀ i : Fin 8, sytByHook (oneColumnShape (i.val + 1)) = 1 := by
  native_decide

def shape2_1 : Fin 2 -> Nat := ![2, 1]
def shape2_2 : Fin 2 -> Nat := ![2, 2]
def shape3_2 : Fin 2 -> Nat := ![3, 2]
def shape3_2_1 : Fin 3 -> Nat := ![3, 2, 1]

def hookLengths2_1 : Fin 3 -> Nat :=
  ![hookLength shape2_1 (0 : Fin 2) 0,
    hookLength shape2_1 (0 : Fin 2) 1,
    hookLength shape2_1 (1 : Fin 2) 0]

def hookLengths2_2 : Fin 4 -> Nat :=
  ![hookLength shape2_2 (0 : Fin 2) 0,
    hookLength shape2_2 (0 : Fin 2) 1,
    hookLength shape2_2 (1 : Fin 2) 0,
    hookLength shape2_2 (1 : Fin 2) 1]

def hookLengths3_2 : Fin 5 -> Nat :=
  ![hookLength shape3_2 (0 : Fin 2) 0,
    hookLength shape3_2 (0 : Fin 2) 1,
    hookLength shape3_2 (0 : Fin 2) 2,
    hookLength shape3_2 (1 : Fin 2) 0,
    hookLength shape3_2 (1 : Fin 2) 1]

def hookLengths3_2_1 : Fin 6 -> Nat :=
  ![hookLength shape3_2_1 (0 : Fin 3) 0,
    hookLength shape3_2_1 (0 : Fin 3) 1,
    hookLength shape3_2_1 (0 : Fin 3) 2,
    hookLength shape3_2_1 (1 : Fin 3) 0,
    hookLength shape3_2_1 (1 : Fin 3) 1,
    hookLength shape3_2_1 (2 : Fin 3) 0]

def expectedHookLengths2_1 : Fin 3 -> Nat := ![3, 1, 1]
def expectedHookLengths2_2 : Fin 4 -> Nat := ![3, 2, 2, 1]
def expectedHookLengths3_2 : Fin 5 -> Nat := ![4, 3, 1, 2, 1]
def expectedHookLengths3_2_1 : Fin 6 -> Nat := ![5, 3, 1, 3, 1, 1]

theorem hook_lengths_2_1 :
    hookLengths2_1 = expectedHookLengths2_1 := by
  native_decide

theorem hook_lengths_2_2 :
    hookLengths2_2 = expectedHookLengths2_2 := by
  native_decide

theorem hook_lengths_3_2 :
    hookLengths3_2 = expectedHookLengths3_2 := by
  native_decide

theorem hook_lengths_3_2_1 :
    hookLengths3_2_1 = expectedHookLengths3_2_1 := by
  native_decide

theorem hook_formula_shape_2_1 :
    hookProduct shape2_1 = 3 * 1 * 1 ∧ sytByHook shape2_1 = 2 := by
  native_decide

theorem hook_formula_shape_2_2 :
    hookProduct shape2_2 = 3 * 2 * 2 * 1 ∧ sytByHook shape2_2 = 2 := by
  native_decide

theorem hook_formula_shape_3_2 :
    hookProduct shape3_2 = 4 * 3 * 1 * 2 * 1 ∧ sytByHook shape3_2 = 5 := by
  native_decide

theorem hook_formula_shape_3_2_1 :
    hookProduct shape3_2_1 = 5 * 3 * 1 * 3 * 1 * 1 ∧
      sytByHook shape3_2_1 = 16 := by
  native_decide

/-! ## Catalan connection for two-row rectangular tableaux -/

def twoRowRectangle (n : Nat) : Fin 2 -> Nat := ![n, n]

def catalanNumber (n : Nat) : Nat :=
  Nat.choose (2 * n) n / (n + 1)

theorem two_row_rectangle_catalan_small :
    ∀ i : Fin 8, sytByHook (twoRowRectangle (i.val + 1)) = catalanNumber (i.val + 1) := by
  native_decide

theorem shape_2_2_catalan :
    sytByHook (twoRowRectangle 2) = 2 ∧ catalanNumber 2 = 2 := by
  native_decide

theorem shape_3_3_catalan :
    sytByHook (twoRowRectangle 3) = 5 ∧ catalanNumber 3 = 5 := by
  native_decide

theorem shape_4_4_catalan :
    sytByHook (twoRowRectangle 4) = 14 ∧ catalanNumber 4 = 14 := by
  native_decide

/-! ## Robinson-Schensted count identity -/

/--
The Robinson-Schensted correspondence is a bijection between permutations of
size `n` and ordered pairs `(P,Q)` of standard Young tableaux with the same
partition shape. Hence the numerical identity is `sum_lambda (f^lambda)^2 = n!`.
-/
def sameShapePairCount {k : Nat} (counts : Fin k -> Nat) : Nat :=
  ∑ i : Fin k, (counts i) ^ 2

def partitionSytCounts1 : Fin 1 -> Nat := ![1]
def partitionSytCounts2 : Fin 2 -> Nat := ![1, 1]
def partitionSytCounts3 : Fin 3 -> Nat := ![1, 2, 1]
def partitionSytCounts4 : Fin 5 -> Nat := ![1, 3, 2, 3, 1]
def partitionSytCounts5 : Fin 7 -> Nat := ![1, 4, 5, 6, 5, 4, 1]

def rskPairCountTable : Fin 5 -> Nat :=
  ![sameShapePairCount partitionSytCounts1,
    sameShapePairCount partitionSytCounts2,
    sameShapePairCount partitionSytCounts3,
    sameShapePairCount partitionSytCounts4,
    sameShapePairCount partitionSytCounts5]

def factorialTable1To5 : Fin 5 -> Nat :=
  ![Nat.factorial 1, Nat.factorial 2, Nat.factorial 3,
    Nat.factorial 4, Nat.factorial 5]

theorem robinson_schensted_counts_one_to_five :
    rskPairCountTable = factorialTable1To5 := by
  native_decide

theorem robinson_schensted_explicit_sums :
    sameShapePairCount partitionSytCounts1 = Nat.factorial 1 ∧
      sameShapePairCount partitionSytCounts2 = Nat.factorial 2 ∧
      sameShapePairCount partitionSytCounts3 = Nat.factorial 3 ∧
      sameShapePairCount partitionSytCounts4 = Nat.factorial 4 ∧
      sameShapePairCount partitionSytCounts5 = Nat.factorial 5 := by
  native_decide

end YoungTableaux
