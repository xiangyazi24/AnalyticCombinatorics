import Mathlib.Tactic
set_option linter.style.nativeDecide false
namespace PermutationFixedPoints

open Finset

/-!
# Fixed points and descent statistics of permutations

Chapter II of Flajolet and Sedgewick records permutations by fixed points
through derangements and rencontres numbers, and by local order statistics
through Eulerian numbers.  The statements below are deliberately finite
computable checks.
-/

/-- Derangement numbers `D(n)`. -/
def derangements : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangements (n + 1) + derangements n)

/-- Derangement table `D(0), ..., D(8)`. -/
def derangementTable : Fin 9 → ℕ := ![1, 0, 1, 2, 9, 44, 265, 1854, 14833]

theorem derangement_values_0_to_8 :
    derangements 0 = 1 ∧ derangements 1 = 0 ∧ derangements 2 = 1 ∧
    derangements 3 = 2 ∧ derangements 4 = 9 ∧ derangements 5 = 44 ∧
    derangements 6 = 265 ∧ derangements 7 = 1854 ∧
    derangements 8 = 14833 := by
  native_decide

theorem derangement_table_matches_definition :
    ∀ i : Fin 9, derangementTable i = derangements i.val := by
  native_decide

theorem derangement_recurrence_2_to_8 :
    derangements 2 = (2 - 1) * (derangements (2 - 1) + derangements (2 - 2)) ∧
    derangements 3 = (3 - 1) * (derangements (3 - 1) + derangements (3 - 2)) ∧
    derangements 4 = (4 - 1) * (derangements (4 - 1) + derangements (4 - 2)) ∧
    derangements 5 = (5 - 1) * (derangements (5 - 1) + derangements (5 - 2)) ∧
    derangements 6 = (6 - 1) * (derangements (6 - 1) + derangements (6 - 2)) ∧
    derangements 7 = (7 - 1) * (derangements (7 - 1) + derangements (7 - 2)) ∧
    derangements 8 = (8 - 1) * (derangements (8 - 1) + derangements (8 - 2)) := by
  native_decide

/-- Fixed points in a list, where the position index starts at `i`. -/
def fixedPointCountFrom (i : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => (if x = i then 1 else 0) + fixedPointCountFrom (i + 1) xs

/-- Fixed points of a permutation represented as a list. -/
def fixedPointCount (p : List ℕ) : ℕ :=
  fixedPointCountFrom 0 p

/-- Direct count of permutations of `[n]` with exactly `k` fixed points. -/
def permutationsWithFixedPoints (n k : ℕ) : ℕ :=
  ((List.range n).permutations.filter fun p => fixedPointCount p = k).length

/-- Rencontres number `R(n,k) = C(n,k)D(n-k)`. -/
def rencontres (n k : ℕ) : ℕ :=
  Nat.choose n k * derangements (n - k)

theorem fixed_point_formula_checked_pairs :
    permutationsWithFixedPoints 3 0 = rencontres 3 0 ∧
    permutationsWithFixedPoints 3 1 = rencontres 3 1 ∧
    permutationsWithFixedPoints 3 2 = rencontres 3 2 ∧
    permutationsWithFixedPoints 3 3 = rencontres 3 3 ∧
    permutationsWithFixedPoints 4 0 = rencontres 4 0 ∧
    permutationsWithFixedPoints 4 1 = rencontres 4 1 ∧
    permutationsWithFixedPoints 4 2 = rencontres 4 2 ∧
    permutationsWithFixedPoints 4 4 = rencontres 4 4 ∧
    permutationsWithFixedPoints 5 0 = rencontres 5 0 ∧
    permutationsWithFixedPoints 5 1 = rencontres 5 1 ∧
    permutationsWithFixedPoints 5 2 = rencontres 5 2 ∧
    permutationsWithFixedPoints 5 3 = rencontres 5 3 ∧
    permutationsWithFixedPoints 6 0 = rencontres 6 0 ∧
    permutationsWithFixedPoints 6 1 = rencontres 6 1 ∧
    permutationsWithFixedPoints 6 2 = rencontres 6 2 ∧
    permutationsWithFixedPoints 6 6 = rencontres 6 6 := by
  native_decide

/-- Row sum `Σ_k C(n,k)D(n-k)`. -/
def rencontresRowSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), rencontres n k

theorem rencontres_row_sums_1_to_7 :
    rencontresRowSum 1 = Nat.factorial 1 ∧
    rencontresRowSum 2 = Nat.factorial 2 ∧
    rencontresRowSum 3 = Nat.factorial 3 ∧
    rencontresRowSum 4 = Nat.factorial 4 ∧
    rencontresRowSum 5 = Nat.factorial 5 ∧
    rencontresRowSum 6 = Nat.factorial 6 ∧
    rencontresRowSum 7 = Nat.factorial 7 := by
  native_decide

/-- Rencontres row `R(0,k)`. -/
def rencontresRow0 : Fin 1 → ℕ := ![1]

/-- Rencontres row `R(1,k)`. -/
def rencontresRow1 : Fin 2 → ℕ := ![0, 1]

/-- Rencontres row `R(2,k)`. -/
def rencontresRow2 : Fin 3 → ℕ := ![1, 0, 1]

/-- Rencontres row `R(3,k)`. -/
def rencontresRow3 : Fin 4 → ℕ := ![2, 3, 0, 1]

/-- Rencontres row `R(4,k)`. -/
def rencontresRow4 : Fin 5 → ℕ := ![9, 8, 6, 0, 1]

/-- Rencontres row `R(5,k)`. -/
def rencontresRow5 : Fin 6 → ℕ := ![44, 45, 20, 10, 0, 1]

/-- Rencontres row `R(6,k)`. -/
def rencontresRow6 : Fin 7 → ℕ := ![265, 264, 135, 40, 15, 0, 1]

theorem rencontres_tables_match_formula :
    (∀ k : Fin 1, rencontresRow0 k = rencontres 0 k.val) ∧
    (∀ k : Fin 2, rencontresRow1 k = rencontres 1 k.val) ∧
    (∀ k : Fin 3, rencontresRow2 k = rencontres 2 k.val) ∧
    (∀ k : Fin 4, rencontresRow3 k = rencontres 3 k.val) ∧
    (∀ k : Fin 5, rencontresRow4 k = rencontres 4 k.val) ∧
    (∀ k : Fin 6, rencontresRow5 k = rencontres 5 k.val) ∧
    (∀ k : Fin 7, rencontresRow6 k = rencontres 6 k.val) := by
  native_decide

/-- A rational lower bound for `e`. -/
def eLower : ℚ := 27182818 / 10000000

/-- A rational upper bound for `e`. -/
def eUpper : ℚ := 27182819 / 10000000

/-- Rational check that `D(n) * e` is within one unit of `n!`. -/
def derangementRoundTripBound (n : ℕ) : Bool :=
  decide
    (((Nat.factorial n : ℤ) - 1) * 10000000 < (derangements n : ℤ) * 27182818 ∧
      (derangements n : ℤ) * 27182819 < ((Nat.factorial n : ℤ) + 1) * 10000000)

theorem derangement_round_trip_bounds_2_to_8 :
    derangementRoundTripBound 2 = true ∧ derangementRoundTripBound 3 = true ∧
    derangementRoundTripBound 4 = true ∧ derangementRoundTripBound 5 = true ∧
    derangementRoundTripBound 6 = true ∧ derangementRoundTripBound 7 = true ∧
    derangementRoundTripBound 8 = true := by
  native_decide

/-- Sign `(-1)^k` as a rational. -/
def alternatingSignRat (k : ℕ) : ℚ :=
  if k % 2 = 0 then 1 else -1

/-- Partial sum `Σ_{k=0}^n (-1)^k/k!`. -/
def subfactorialPartialSum (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), alternatingSignRat k / (Nat.factorial k : ℚ)

theorem subfactorial_ratio_partial_sums_0_to_8 :
    (derangements 0 : ℚ) / (Nat.factorial 0 : ℚ) = subfactorialPartialSum 0 ∧
    (derangements 1 : ℚ) / (Nat.factorial 1 : ℚ) = subfactorialPartialSum 1 ∧
    (derangements 2 : ℚ) / (Nat.factorial 2 : ℚ) = subfactorialPartialSum 2 ∧
    (derangements 3 : ℚ) / (Nat.factorial 3 : ℚ) = subfactorialPartialSum 3 ∧
    (derangements 4 : ℚ) / (Nat.factorial 4 : ℚ) = subfactorialPartialSum 4 ∧
    (derangements 5 : ℚ) / (Nat.factorial 5 : ℚ) = subfactorialPartialSum 5 ∧
    (derangements 6 : ℚ) / (Nat.factorial 6 : ℚ) = subfactorialPartialSum 6 ∧
    (derangements 7 : ℚ) / (Nat.factorial 7 : ℚ) = subfactorialPartialSum 7 ∧
    (derangements 8 : ℚ) / (Nat.factorial 8 : ℚ) = subfactorialPartialSum 8 := by
  native_decide

/-- Sign `(-1)^k` as an integer. -/
def alternatingSignInt (k : ℕ) : ℤ :=
  if k % 2 = 0 then 1 else -1

/-- Alternating sum `Σ_k (-1)^k C(n,k)D(n-k)`. -/
def alternatingRencontresSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), alternatingSignInt k * (rencontres n k : ℤ)

theorem alternating_rencontres_sums_0_to_8 :
    alternatingRencontresSum 0 = 1 ∧
    alternatingRencontresSum 1 = -1 ∧
    alternatingRencontresSum 2 = 2 ∧
    alternatingRencontresSum 3 = -2 ∧
    alternatingRencontresSum 4 = 8 ∧
    alternatingRencontresSum 5 = 8 ∧
    alternatingRencontresSum 6 = 112 ∧
    alternatingRencontresSum 7 = 656 ∧
    alternatingRencontresSum 8 = 5504 := by
  native_decide

/-- Computable Euler totient. -/
def totient (n : ℕ) : ℕ :=
  ((List.range (n + 1)).filter fun k => k < n ∧ Nat.gcd k n = 1).length

theorem totient_values :
    totient 1 = 1 ∧ totient 2 = 1 ∧ totient 3 = 2 ∧
    totient 4 = 2 ∧ totient 5 = 4 ∧ totient 6 = 2 ∧
    totient 7 = 6 ∧ totient 8 = 4 ∧ totient 9 = 6 ∧
    totient 10 = 4 ∧ totient 12 = 4 := by
  native_decide

theorem totient_multiplicative_examples :
    Nat.gcd 3 4 = 1 ∧ totient (3 * 4) = totient 3 * totient 4 ∧
    Nat.gcd 5 8 = 1 ∧ totient (5 * 8) = totient 5 * totient 8 ∧
    Nat.gcd 7 9 = 1 ∧ totient (7 * 9) = totient 7 * totient 9 := by
  native_decide

theorem derangements_are_not_totient_and_not_multiplicative :
    derangements 6 ≠ totient 6 ∧
    derangements (2 * 3) ≠ derangements 2 * derangements 3 := by
  native_decide

/-- Number of ascents in a list. -/
def ascentCount : List ℕ → ℕ
  | a :: b :: xs => (if a < b then 1 else 0) + ascentCount (b :: xs)
  | _ => 0

/-- Number of descents in a list. -/
def descentCount : List ℕ → ℕ
  | a :: b :: xs => (if a > b then 1 else 0) + descentCount (b :: xs)
  | _ => 0

/-- Direct count of permutations of `[n]` with no ascents. -/
def permutationsWithNoAscents (n : ℕ) : ℕ :=
  ((List.range n).permutations.filter fun p => ascentCount p = 0).length

/-- Direct count of permutations of `[n]` with no descents. -/
def permutationsWithNoDescents (n : ℕ) : ℕ :=
  ((List.range n).permutations.filter fun p => descentCount p = 0).length

theorem monotone_extreme_counts_1_to_7 :
    permutationsWithNoAscents 1 = 1 ∧ permutationsWithNoDescents 1 = 1 ∧
    permutationsWithNoAscents 2 = 1 ∧ permutationsWithNoDescents 2 = 1 ∧
    permutationsWithNoAscents 3 = 1 ∧ permutationsWithNoDescents 3 = 1 ∧
    permutationsWithNoAscents 4 = 1 ∧ permutationsWithNoDescents 4 = 1 ∧
    permutationsWithNoAscents 5 = 1 ∧ permutationsWithNoDescents 5 = 1 ∧
    permutationsWithNoAscents 6 = 1 ∧ permutationsWithNoDescents 6 = 1 ∧
    permutationsWithNoAscents 7 = 1 ∧ permutationsWithNoDescents 7 = 1 := by
  native_decide

theorem identity_lists_have_no_descents :
    descentCount (List.range 1) = 0 ∧ fixedPointCount (List.range 1) = 1 ∧
    descentCount (List.range 2) = 0 ∧ fixedPointCount (List.range 2) = 2 ∧
    descentCount (List.range 3) = 0 ∧ fixedPointCount (List.range 3) = 3 ∧
    descentCount (List.range 4) = 0 ∧ fixedPointCount (List.range 4) = 4 ∧
    descentCount (List.range 5) = 0 ∧ fixedPointCount (List.range 5) = 5 ∧
    descentCount (List.range 6) = 0 ∧ fixedPointCount (List.range 6) = 6 ∧
    descentCount (List.range 7) = 0 ∧ fixedPointCount (List.range 7) = 7 := by
  native_decide

/-- Eulerian number `A(n,k)`, counted directly by descents. -/
def eulerianNumber (n k : ℕ) : ℕ :=
  ((List.range n).permutations.filter fun p => descentCount p = k).length

/-- Eulerian row for `n=1`. -/
def eulerianRow1 : Fin 1 → ℕ := ![1]

/-- Eulerian row for `n=2`. -/
def eulerianRow2 : Fin 2 → ℕ := ![1, 1]

/-- Eulerian row for `n=3`. -/
def eulerianRow3 : Fin 3 → ℕ := ![1, 4, 1]

/-- Eulerian row for `n=4`. -/
def eulerianRow4 : Fin 4 → ℕ := ![1, 11, 11, 1]

/-- Eulerian row for `n=5`. -/
def eulerianRow5 : Fin 5 → ℕ := ![1, 26, 66, 26, 1]

theorem eulerian_tables_match_descent_counts :
    (∀ k : Fin 1, eulerianRow1 k = eulerianNumber 1 k.val) ∧
    (∀ k : Fin 2, eulerianRow2 k = eulerianNumber 2 k.val) ∧
    (∀ k : Fin 3, eulerianRow3 k = eulerianNumber 3 k.val) ∧
    (∀ k : Fin 4, eulerianRow4 k = eulerianNumber 4 k.val) ∧
    (∀ k : Fin 5, eulerianRow5 k = eulerianNumber 5 k.val) := by
  native_decide

theorem eulerian_row_sums_1_to_5 :
    (∑ k : Fin 1, eulerianRow1 k) = Nat.factorial 1 ∧
    (∑ k : Fin 2, eulerianRow2 k) = Nat.factorial 2 ∧
    (∑ k : Fin 3, eulerianRow3 k) = Nat.factorial 3 ∧
    (∑ k : Fin 4, eulerianRow4 k) = Nat.factorial 4 ∧
    (∑ k : Fin 5, eulerianRow5 k) = Nat.factorial 5 := by
  native_decide

end PermutationFixedPoints
