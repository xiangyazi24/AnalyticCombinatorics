import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace CombinatorialInequalities

/-!
Bounded computational checks for small combinatorial inequalities and
convolution identities from elementary enumerative combinatorics.
-/

def catalanTable : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786]

def binomialRow10 : Fin 11 → ℕ :=
  ![1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1]

def stirling2Row8 : Fin 9 → ℕ :=
  ![0, 1, 127, 966, 1701, 1050, 266, 28, 1]

def sampleSetA : Fin 8 → Bool :=
  ![true, true, true, false, false, false, false, false]

def sampleSetB : Fin 8 → Bool :=
  ![false, true, true, true, true, false, false, false]

def sampleSetC : Fin 8 → Bool :=
  ![true, false, true, false, true, true, false, false]

theorem binomial_row10_table_matches_choose :
    binomialRow10 0 = Nat.choose 10 0 ∧
      binomialRow10 1 = Nat.choose 10 1 ∧
      binomialRow10 2 = Nat.choose 10 2 ∧
      binomialRow10 3 = Nat.choose 10 3 ∧
      binomialRow10 4 = Nat.choose 10 4 ∧
      binomialRow10 5 = Nat.choose 10 5 ∧
      binomialRow10 6 = Nat.choose 10 6 ∧
      binomialRow10 7 = Nat.choose 10 7 ∧
      binomialRow10 8 = Nat.choose 10 8 ∧
      binomialRow10 9 = Nat.choose 10 9 ∧
      binomialRow10 10 = Nat.choose 10 10 := by
  native_decide

theorem binomial_row10_log_concave :
    binomialRow10 1 ^ 2 ≥ binomialRow10 0 * binomialRow10 2 ∧
      binomialRow10 2 ^ 2 ≥ binomialRow10 1 * binomialRow10 3 ∧
      binomialRow10 3 ^ 2 ≥ binomialRow10 2 * binomialRow10 4 ∧
      binomialRow10 4 ^ 2 ≥ binomialRow10 3 * binomialRow10 5 ∧
      binomialRow10 5 ^ 2 ≥ binomialRow10 4 * binomialRow10 6 ∧
      binomialRow10 6 ^ 2 ≥ binomialRow10 5 * binomialRow10 7 ∧
      binomialRow10 7 ^ 2 ≥ binomialRow10 6 * binomialRow10 8 ∧
      binomialRow10 8 ^ 2 ≥ binomialRow10 7 * binomialRow10 9 ∧
      binomialRow10 9 ^ 2 ≥ binomialRow10 8 * binomialRow10 10 := by
  native_decide

theorem binomial_row10_unimodal :
    binomialRow10 0 ≤ binomialRow10 1 ∧
      binomialRow10 1 ≤ binomialRow10 2 ∧
      binomialRow10 2 ≤ binomialRow10 3 ∧
      binomialRow10 3 ≤ binomialRow10 4 ∧
      binomialRow10 4 ≤ binomialRow10 5 ∧
      binomialRow10 5 ≥ binomialRow10 6 ∧
      binomialRow10 6 ≥ binomialRow10 7 ∧
      binomialRow10 7 ≥ binomialRow10 8 ∧
      binomialRow10 8 ≥ binomialRow10 9 ∧
      binomialRow10 9 ≥ binomialRow10 10 := by
  native_decide

theorem catalan_table_initial_values :
    catalanTable 0 = 1 ∧ catalanTable 1 = 1 ∧ catalanTable 2 = 2 ∧
      catalanTable 3 = 5 ∧ catalanTable 4 = 14 ∧ catalanTable 5 = 42 := by
  native_decide

theorem catalan_reverse_turan_1_10 :
    catalanTable 1 ^ 2 ≤ catalanTable 0 * catalanTable 2 ∧
      catalanTable 2 ^ 2 ≤ catalanTable 1 * catalanTable 3 ∧
      catalanTable 3 ^ 2 ≤ catalanTable 2 * catalanTable 4 ∧
      catalanTable 4 ^ 2 ≤ catalanTable 3 * catalanTable 5 ∧
      catalanTable 5 ^ 2 ≤ catalanTable 4 * catalanTable 6 ∧
      catalanTable 6 ^ 2 ≤ catalanTable 5 * catalanTable 7 ∧
      catalanTable 7 ^ 2 ≤ catalanTable 6 * catalanTable 8 ∧
      catalanTable 8 ^ 2 ≤ catalanTable 7 * catalanTable 9 ∧
      catalanTable 9 ^ 2 ≤ catalanTable 8 * catalanTable 10 ∧
      catalanTable 10 ^ 2 ≤ catalanTable 9 * catalanTable 11 := by
  native_decide

theorem stirling2_row8_unimodal :
    stirling2Row8 0 ≤ stirling2Row8 1 ∧
      stirling2Row8 1 ≤ stirling2Row8 2 ∧
      stirling2Row8 2 ≤ stirling2Row8 3 ∧
      stirling2Row8 3 ≤ stirling2Row8 4 ∧
      stirling2Row8 4 ≥ stirling2Row8 5 ∧
      stirling2Row8 5 ≥ stirling2Row8 6 ∧
      stirling2Row8 6 ≥ stirling2Row8 7 ∧
      stirling2Row8 7 ≥ stirling2Row8 8 := by
  native_decide

theorem stirling2_row8_peak :
    stirling2Row8 0 ≤ stirling2Row8 4 ∧
      stirling2Row8 1 ≤ stirling2Row8 4 ∧
      stirling2Row8 2 ≤ stirling2Row8 4 ∧
      stirling2Row8 3 ≤ stirling2Row8 4 ∧
      stirling2Row8 5 ≤ stirling2Row8 4 ∧
      stirling2Row8 6 ≤ stirling2Row8 4 ∧
      stirling2Row8 7 ≤ stirling2Row8 4 ∧
      stirling2Row8 8 ≤ stirling2Row8 4 := by
  native_decide

def vandermondeSum (m n r : ℕ) : ℕ :=
  ∑ k : Fin (r + 1), Nat.choose m k.val * Nat.choose n (r - k.val)

theorem vandermonde_4_5_instances :
    vandermondeSum 4 5 0 = Nat.choose 9 0 ∧
      vandermondeSum 4 5 1 = Nat.choose 9 1 ∧
      vandermondeSum 4 5 2 = Nat.choose 9 2 ∧
      vandermondeSum 4 5 3 = Nat.choose 9 3 ∧
      vandermondeSum 4 5 4 = Nat.choose 9 4 ∧
      vandermondeSum 4 5 5 = Nat.choose 9 5 ∧
      vandermondeSum 4 5 6 = Nat.choose 9 6 ∧
      vandermondeSum 4 5 7 = Nat.choose 9 7 ∧
      vandermondeSum 4 5 8 = Nat.choose 9 8 ∧
      vandermondeSum 4 5 9 = Nat.choose 9 9 := by
  native_decide

theorem vandermonde_3_6_instances :
    vandermondeSum 3 6 0 = Nat.choose 9 0 ∧
      vandermondeSum 3 6 1 = Nat.choose 9 1 ∧
      vandermondeSum 3 6 2 = Nat.choose 9 2 ∧
      vandermondeSum 3 6 3 = Nat.choose 9 3 ∧
      vandermondeSum 3 6 4 = Nat.choose 9 4 ∧
      vandermondeSum 3 6 5 = Nat.choose 9 5 ∧
      vandermondeSum 3 6 6 = Nat.choose 9 6 ∧
      vandermondeSum 3 6 7 = Nat.choose 9 7 ∧
      vandermondeSum 3 6 8 = Nat.choose 9 8 ∧
      vandermondeSum 3 6 9 = Nat.choose 9 9 := by
  native_decide

def boolCard {n : ℕ} (p : Fin n → Bool) : ℕ :=
  ∑ x : Fin n, if p x then 1 else 0

def union3 {n : ℕ} (A B C : Fin n → Bool) : Fin n → Bool :=
  fun x => A x || B x || C x

def inter2 {n : ℕ} (A B : Fin n → Bool) : Fin n → Bool :=
  fun x => A x && B x

theorem bonferroni_sample_sets :
    boolCard (union3 sampleSetA sampleSetB sampleSetC) ≤
        boolCard sampleSetA + boolCard sampleSetB + boolCard sampleSetC ∧
      boolCard sampleSetA + boolCard sampleSetB + boolCard sampleSetC -
          (boolCard (inter2 sampleSetA sampleSetB) +
            boolCard (inter2 sampleSetA sampleSetC) +
            boolCard (inter2 sampleSetB sampleSetC)) ≤
        boolCard (union3 sampleSetA sampleSetB sampleSetC) := by
  native_decide

abbrev BoolSquare := Fin 2 → Bool

def eventCard (A : BoolSquare → Bool) : ℕ :=
  ∑ x : BoolSquare, if A x then 1 else 0

def meetEvent (A B : BoolSquare → Bool) : BoolSquare → Bool :=
  fun x => A x && B x

def firstCoordinateEvent (x : BoolSquare) : Bool :=
  x 0

def atLeastOneEvent (x : BoolSquare) : Bool :=
  x 0 || x 1

def bothCoordinatesEvent (x : BoolSquare) : Bool :=
  x 0 && x 1

theorem fkg_boolean_square_first_or :
    eventCard firstCoordinateEvent = 2 ∧
      eventCard atLeastOneEvent = 3 ∧
      eventCard (meetEvent firstCoordinateEvent atLeastOneEvent) = 2 ∧
      4 * eventCard (meetEvent firstCoordinateEvent atLeastOneEvent) ≥
        eventCard firstCoordinateEvent * eventCard atLeastOneEvent := by
  native_decide

theorem fkg_boolean_square_and_or :
    eventCard bothCoordinatesEvent = 1 ∧
      eventCard atLeastOneEvent = 3 ∧
      eventCard (meetEvent bothCoordinatesEvent atLeastOneEvent) = 1 ∧
      4 * eventCard (meetEvent bothCoordinatesEvent atLeastOneEvent) ≥
        eventCard bothCoordinatesEvent * eventCard atLeastOneEvent := by
  native_decide

end CombinatorialInequalities
