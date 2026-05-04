import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace RookPolynomials

open Finset

/-! ## Rook Polynomials

Rook placements on boards, rook numbers, hit numbers, permanents of 0-1
matrices, and inclusion-exclusion for permutations with forbidden positions
(Flajolet & Sedgewick, *Analytic Combinatorics*, Chapter II).
-/

/-! ### Combinatorial Helpers -/

/-- Insert `a` at every position in a list. -/
def insertEverywhere (a : α) : List α → List (List α)
  | [] => [[a]]
  | x :: xs => (a :: x :: xs) :: ((insertEverywhere a xs).map (x :: ·))

/-- All permutations of a list. -/
def perms : List α → List (List α)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (insertEverywhere x)

/-- All subsequences of exactly `k` elements (ordered combinations). -/
def chooseSub : List α → ℕ → List (List α)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: xs, k + 1 => (chooseSub xs k |>.map (x :: ·)) ++ chooseSub xs (k + 1)

/-! ### Boards and Rook Numbers -/

/-- A board is a list of `(row, column)` cells in a grid. -/
abbrev Board := List (ℕ × ℕ)

/-- No two cells in a placement share a row or a column. -/
def isNonAttacking : List (ℕ × ℕ) → Bool
  | [] => true
  | (r, c) :: rest =>
    (rest.all fun p => (r != p.1) && (c != p.2)) && isNonAttacking rest

/-- The rook number `r_k(B)`: number of non-attacking `k`-rook placements on `B`. -/
def rookNumber (B : Board) (k : ℕ) : ℕ :=
  (chooseSub B k |>.filter isNonAttacking).length

/-- The full `n × n` board. -/
def fullBoard (n : ℕ) : Board :=
  (List.range n).flatMap fun i => (List.range n).map fun j => (i, j)

/-- Staircase board `{(i, j) | 0 ≤ j < i < n}`. -/
def staircaseBoard (n : ℕ) : Board :=
  (List.range n).flatMap fun i => (List.range i).map fun j => (i, j)

/-- Diagonal board `{(i, i) | i < n}`. -/
def diagonalBoard (n : ℕ) : Board :=
  (List.range n).map fun i => (i, i)

/-- Board complement: cells in `[n] × [n]` not in `B`. -/
def complementBoard (n : ℕ) (B : Board) : Board :=
  (fullBoard n).filter fun cell => !(B.contains cell)

/-- Board of a 0-1 matrix given as a list of rows of Booleans. -/
def boardOfMatrix (A : List (List Bool)) : Board :=
  ((List.range A.length).zip A).flatMap fun (i, row) =>
    ((List.range row.length).zip row).filterMap fun (j, v) =>
      if v then some (i, j) else none

/-! ### Closed-Form Formula -/

/-- Closed form for the full board: `r_k([n]²) = C(n,k)² · k!`. -/
def fullBoardRookFormula (n k : ℕ) : ℕ :=
  n.choose k * n.choose k * k.factorial

/-! ### Hit Numbers and Permanents -/

/-- Number of positions `i` where `(i, σ(i)) ∈ B`. -/
def hitCount (B : Board) (σ : List ℕ) : ℕ :=
  ((List.range σ.length).zip σ |>.filter fun p => B.contains p).length

/-- Hit number `h_k(B, n)`: permutations of `{0,…,n−1}` hitting `B` exactly `k` times. -/
def hitNumber (B : Board) (n k : ℕ) : ℕ :=
  ((perms (List.range n)).filter fun σ => hitCount B σ == k).length

/-- Permanent of a 0-1 matrix: number of systems of distinct representatives. -/
def permanent (A : List (List Bool)) : ℕ :=
  hitNumber (boardOfMatrix A) A.length A.length

/-! ### The Rook Polynomial -/

/-- Rook polynomial as coefficient list `[r_0(B), r_1(B), …, r_n(B)]`. -/
def rookPolynomial (B : Board) (n : ℕ) : List ℕ :=
  (List.range (n + 1)).map (rookNumber B)

/-! ## Concrete Verifications -/

section FullBoardExamples

theorem fullBoard_r0_3 : rookNumber (fullBoard 3) 0 = 1 := by native_decide
theorem fullBoard_r1_3 : rookNumber (fullBoard 3) 1 = 9 := by native_decide
theorem fullBoard_r2_3 : rookNumber (fullBoard 3) 2 = 18 := by native_decide
theorem fullBoard_r3_3 : rookNumber (fullBoard 3) 3 = 6 := by native_decide

theorem fullBoard_formula_match_3 (k : ℕ) (hk : k ≤ 3) :
    rookNumber (fullBoard 3) k = fullBoardRookFormula 3 k := by
  interval_cases k <;> native_decide

theorem fullBoard_r0_4 : rookNumber (fullBoard 4) 0 = 1 := by native_decide
theorem fullBoard_r1_4 : rookNumber (fullBoard 4) 1 = 16 := by native_decide
theorem fullBoard_r2_4 : rookNumber (fullBoard 4) 2 = 72 := by native_decide
theorem fullBoard_r3_4 : rookNumber (fullBoard 4) 3 = 96 := by native_decide
theorem fullBoard_r4_4 : rookNumber (fullBoard 4) 4 = 24 := by native_decide

theorem fullBoard_formula_match_4 (k : ℕ) (hk : k ≤ 4) :
    rookNumber (fullBoard 4) k = fullBoardRookFormula 4 k := by
  interval_cases k <;> native_decide

end FullBoardExamples

section StaircaseExamples

theorem staircase_r0_3 : rookNumber (staircaseBoard 3) 0 = 1 := by native_decide
theorem staircase_r1_3 : rookNumber (staircaseBoard 3) 1 = 3 := by native_decide
theorem staircase_r2_3 : rookNumber (staircaseBoard 3) 2 = 1 := by native_decide

theorem staircase_r0_4 : rookNumber (staircaseBoard 4) 0 = 1 := by native_decide
theorem staircase_r1_4 : rookNumber (staircaseBoard 4) 1 = 6 := by native_decide
theorem staircase_r2_4 : rookNumber (staircaseBoard 4) 2 = 7 := by native_decide
theorem staircase_r3_4 : rookNumber (staircaseBoard 4) 3 = 1 := by native_decide

end StaircaseExamples

section DiagonalExamples

theorem diagonal_r0_3 : rookNumber (diagonalBoard 3) 0 = 1 := by native_decide
theorem diagonal_r1_3 : rookNumber (diagonalBoard 3) 1 = 3 := by native_decide
theorem diagonal_r2_3 : rookNumber (diagonalBoard 3) 2 = 3 := by native_decide
theorem diagonal_r3_3 : rookNumber (diagonalBoard 3) 3 = 1 := by native_decide

theorem diagonal_rook_eq_choose_3 (k : ℕ) (hk : k ≤ 3) :
    rookNumber (diagonalBoard 3) k = Nat.choose 3 k := by
  interval_cases k <;> native_decide

theorem diagonal_rook_eq_choose_4 (k : ℕ) (hk : k ≤ 4) :
    rookNumber (diagonalBoard 4) k = Nat.choose 4 k := by
  interval_cases k <;> native_decide

end DiagonalExamples

section HitNumberExamples

theorem derange_3 : hitNumber (diagonalBoard 3) 3 0 = 2 := by native_decide
theorem derange_4 : hitNumber (diagonalBoard 4) 4 0 = 9 := by native_decide

theorem hits_3_1 : hitNumber (diagonalBoard 3) 3 1 = 3 := by native_decide
theorem hits_3_2 : hitNumber (diagonalBoard 3) 3 2 = 0 := by native_decide
theorem hits_3_3 : hitNumber (diagonalBoard 3) 3 3 = 1 := by native_decide

theorem hits_sum_3 :
    hitNumber (diagonalBoard 3) 3 0 + hitNumber (diagonalBoard 3) 3 1 +
    hitNumber (diagonalBoard 3) 3 2 + hitNumber (diagonalBoard 3) 3 3 =
    Nat.factorial 3 := by native_decide

end HitNumberExamples

section PermanentExamples

theorem permanent_id2 :
    permanent [[true, false], [false, true]] = 1 := by native_decide

theorem permanent_ones2 :
    permanent [[true, true], [true, true]] = 2 := by native_decide

theorem permanent_id3 :
    permanent [[true, false, false], [false, true, false], [false, false, true]] = 1 := by
  native_decide

theorem permanent_ones3 :
    permanent [[true, true, true], [true, true, true], [true, true, true]] = 6 := by
  native_decide

theorem permanent_eq_rookNumber_2x2 :
    permanent [[true, true], [true, false]] =
    rookNumber (boardOfMatrix [[true, true], [true, false]]) 2 := by
  native_decide

end PermanentExamples

section RookPolyExamples

theorem rookPoly_full3 :
    rookPolynomial (fullBoard 3) 3 = [1, 9, 18, 6] := by native_decide

theorem rookPoly_diagonal3 :
    rookPolynomial (diagonalBoard 3) 3 = [1, 3, 3, 1] := by native_decide

theorem rookPoly_staircase4 :
    rookPolynomial (staircaseBoard 4) 3 = [1, 6, 7, 1] := by native_decide

end RookPolyExamples

section ComplementExamples

theorem complement_derange_3 :
    rookNumber (complementBoard 3 (diagonalBoard 3)) 3 = 2 := by native_decide

theorem complement_derange_4 :
    rookNumber (complementBoard 4 (diagonalBoard 4)) 4 = 9 := by native_decide

theorem complement_eq_hits_3 :
    rookNumber (complementBoard 3 (diagonalBoard 3)) 3 =
    hitNumber (diagonalBoard 3) 3 0 := by native_decide

end ComplementExamples

section InclusionExclusionCheck

theorem ie_derange_3 :
    rookNumber (diagonalBoard 3) 0 * Nat.factorial 3
    - rookNumber (diagonalBoard 3) 1 * Nat.factorial 2
    + rookNumber (diagonalBoard 3) 2 * Nat.factorial 1
    - rookNumber (diagonalBoard 3) 3 * Nat.factorial 0
    = hitNumber (diagonalBoard 3) 3 0 := by native_decide

theorem ie_derange_4 :
    rookNumber (diagonalBoard 4) 0 * Nat.factorial 4
    - rookNumber (diagonalBoard 4) 1 * Nat.factorial 3
    + rookNumber (diagonalBoard 4) 2 * Nat.factorial 2
    - rookNumber (diagonalBoard 4) 3 * Nat.factorial 1
    + rookNumber (diagonalBoard 4) 4 * Nat.factorial 0
    = hitNumber (diagonalBoard 4) 4 0 := by native_decide

end InclusionExclusionCheck

/-! ## Theoretical Results -/

/-- Rook number `r_0(B)` is always 1 (the empty placement). -/
theorem rookNumber_zero (B : Board) : rookNumber B 0 = 1 := by
  sorry

/-- Closed form `r_k([n]²) = C(n,k)²·k!` for all `n, k`. -/
theorem fullBoard_rookNumber_formula (n k : ℕ) :
    rookNumber (fullBoard n) k = fullBoardRookFormula n k := by
  sorry

/-- Diagonal board rook numbers equal binomial coefficients. -/
theorem diagonal_rookNumber_choose (n k : ℕ) :
    rookNumber (diagonalBoard n) k = n.choose k := by
  sorry

/-- The sum of all hit numbers equals `n!`. -/
theorem hitNumbers_sum (B : Board) (n : ℕ) :
    ∑ k ∈ range (n + 1), hitNumber B n k = n.factorial := by
  sorry

/-- **Inclusion-exclusion for hit numbers** (over ℤ):
`h_k(B,n) = ∑_{j≤n−k} (-1)^j · C(k+j,k) · r_{k+j}(B) · (n−k−j)!`. -/
theorem hitNumber_inclusion_exclusion (B : Board) (n k : ℕ) (hk : k ≤ n) :
    (hitNumber B n k : ℤ) =
      ∑ j ∈ range (n - k + 1),
        (-1 : ℤ) ^ j * ((k + j).choose k : ℤ) *
        (rookNumber B (k + j) : ℤ) * ((n - k - j).factorial : ℤ) := by
  sorry

/-- The permanent of a square 0-1 matrix equals the `n`-rook number on its board. -/
theorem permanent_eq_rookNumber (A : List (List Bool))
    (hsq : ∀ row ∈ A, row.length = A.length) :
    permanent A = rookNumber (boardOfMatrix A) A.length := by
  sorry

/-- Derangement count via rook-polynomial inclusion-exclusion. -/
theorem derangement_inclusion_exclusion (n : ℕ) :
    (hitNumber (diagonalBoard n) n 0 : ℤ) =
      ∑ k ∈ range (n + 1),
        (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n - k).factorial : ℤ) := by
  sorry

/-- Placing `n` non-attacking rooks on the complement of the diagonal
equals the derangement count. -/
theorem complement_diagonal_eq_derange (n : ℕ) :
    rookNumber (complementBoard n (diagonalBoard n)) n =
    hitNumber (diagonalBoard n) n 0 := by
  sorry

/-- Two boards are *rook-equivalent* when they have identical rook polynomials. -/
def rookEquivalent (B₁ B₂ : Board) : Prop :=
  ∀ k, rookNumber B₁ k = rookNumber B₂ k

end RookPolynomials
