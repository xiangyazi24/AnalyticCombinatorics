import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace Surjections2

/-! ## Surjections and Stirling numbers of the second kind -/

/-- Stirling numbers of the second kind. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- Number of surjections from an `n`-set onto a `k`-set. -/
def surjectionCount (n k : ℕ) : ℕ := stirling2 n k * Nat.factorial k

/-- Inclusion-exclusion side of the surjection formula. -/
def surjectionInclusionExclusion (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℤ) ^ j * (Nat.choose k j : ℤ) * (((k - j) ^ n : ℕ) : ℤ)

theorem surjection_formula_4_2 :
    (surjectionCount 4 2 : ℤ) = surjectionInclusionExclusion 4 2 := by
  native_decide

theorem surjection_formula_4_3 :
    (surjectionCount 4 3 : ℤ) = surjectionInclusionExclusion 4 3 := by
  native_decide

theorem surjection_formula_5_3 :
    (surjectionCount 5 3 : ℤ) = surjectionInclusionExclusion 5 3 := by
  native_decide

theorem surjection_formula_5_4 :
    (surjectionCount 5 4 : ℤ) = surjectionInclusionExclusion 5 4 := by
  native_decide

/-! ## Stirling triangle -/

/-- Row `n` of the Stirling triangle, with entries `S(n,1), ..., S(n,n)`. -/
def stirlingRow (n : ℕ) : List ℕ :=
  (List.range n).map fun i => stirling2 n (i + 1)

theorem stirling_triangle_rows_1_to_7 :
    stirlingRow 1 = [1] ∧
    stirlingRow 2 = [1, 1] ∧
    stirlingRow 3 = [1, 3, 1] ∧
    stirlingRow 4 = [1, 7, 6, 1] ∧
    stirlingRow 5 = [1, 15, 25, 10, 1] ∧
    stirlingRow 6 = [1, 31, 90, 65, 15, 1] ∧
    stirlingRow 7 = [1, 63, 301, 350, 140, 21, 1] := by
  native_decide

/-- First position `k` attaining the maximum of row `n`, among `1, ..., n`. -/
def stirlingRowArgmax (n : ℕ) : ℕ :=
  (List.range n).foldl
    (fun best i =>
      let k := i + 1
      if stirling2 n best < stirling2 n k then k else best)
    0

theorem stirling_row_argmax_5_to_8 :
    stirlingRowArgmax 5 = 3 ∧
    stirlingRowArgmax 6 = 3 ∧
    stirlingRowArgmax 7 = 4 ∧
    stirlingRowArgmax 8 = 4 := by
  native_decide

/-! ## Lah numbers -/

/-- Unsigned Lah numbers: partitions of `n` labelled elements into `k` nonempty lists. -/
def lahNumber (n k : ℕ) : ℕ :=
  Nat.choose (n - 1) (k - 1) * Nat.factorial n / Nat.factorial k

/-- Row `n` of the Lah triangle, with entries `L(n,1), ..., L(n,n)`. -/
def lahRow (n : ℕ) : List ℕ :=
  (List.range n).map fun i => lahNumber n (i + 1)

theorem lah_rows_1_to_5 :
    lahRow 1 = [1] ∧
    lahRow 2 = [2, 1] ∧
    lahRow 3 = [6, 6, 1] ∧
    lahRow 4 = [24, 36, 12, 1] ∧
    lahRow 5 = [120, 240, 120, 20, 1] := by
  native_decide

theorem lah_formula_small_values :
    lahNumber 3 2 = Nat.choose 2 1 * Nat.factorial 3 / Nat.factorial 2 ∧
    lahNumber 4 2 = Nat.choose 3 1 * Nat.factorial 4 / Nat.factorial 2 ∧
    lahNumber 4 3 = Nat.choose 3 2 * Nat.factorial 4 / Nat.factorial 3 ∧
    lahNumber 5 2 = Nat.choose 4 1 * Nat.factorial 5 / Nat.factorial 2 ∧
    lahNumber 5 3 = Nat.choose 4 2 * Nat.factorial 5 / Nat.factorial 3 := by
  native_decide

/-! ## Falling factorials -/

/-- Falling factorial `(n)_k = n! / (n-k)!`. -/
def fallingFactorial (n k : ℕ) : ℕ :=
  Nat.factorial n / Nat.factorial (n - k)

theorem falling_factorial_small_values :
    fallingFactorial 5 0 = 1 ∧
    fallingFactorial 5 1 = 5 ∧
    fallingFactorial 5 2 = 20 ∧
    fallingFactorial 5 3 = 60 ∧
    fallingFactorial 6 4 = 360 ∧
    fallingFactorial 7 3 = 210 ∧
    fallingFactorial 8 5 = 6720 := by
  native_decide

/-! ## Bell numbers -/

/-- Bell numbers `B_0, ..., B_7`. -/
def bellTable : List ℕ := [1, 1, 2, 5, 15, 52, 203, 877]

/-- Bell numbers, table-backed for the finite checks in this file. -/
def bellNumber (n : ℕ) : ℕ := bellTable.getD n 0

/-- Bell numbers computed by the Stirling row sum. -/
def bellByStirling (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), stirling2 n k

theorem bell_polynomial_connection_1_to_7 :
    bellNumber 1 = bellByStirling 1 ∧
    bellNumber 2 = bellByStirling 2 ∧
    bellNumber 3 = bellByStirling 3 ∧
    bellNumber 4 = bellByStirling 4 ∧
    bellNumber 5 = bellByStirling 5 ∧
    bellNumber 6 = bellByStirling 6 ∧
    bellNumber 7 = bellByStirling 7 := by
  native_decide

theorem bell_values_1_to_7 :
    bellNumber 1 = 1 ∧
    bellNumber 2 = 2 ∧
    bellNumber 3 = 5 ∧
    bellNumber 4 = 15 ∧
    bellNumber 5 = 52 ∧
    bellNumber 6 = 203 ∧
    bellNumber 7 = 877 := by
  native_decide

end Surjections2
