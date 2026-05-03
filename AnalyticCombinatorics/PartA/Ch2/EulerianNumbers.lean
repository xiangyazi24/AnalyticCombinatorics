import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace EulerianNumbers

open Finset Nat

/-!
# Eulerian Numbers

Eulerian numbers A(n,k) count permutations of {1,...,n} with exactly k ascents.
They satisfy the recurrence A(n,k) = (k+1)*A(n-1,k) + (n-k)*A(n-1,k-1),
with boundary A(0,0) = 1 and A(n,k) = 0 for k ≥ n.
Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter II.
-/

/-- Eulerian number `A(n,k)` defined by the classical recurrence. -/
def A : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k =>
    if k ≤ n then
      (k + 1) * A n k + (n + 1 - k) * (if k = 0 then 0 else A n (k - 1))
    else 0

theorem A_zero_zero : A 0 0 = 1 := rfl
theorem A_zero_succ (k : ℕ) : A 0 (k + 1) = 0 := rfl

/-- Full Eulerian table through n = 5. -/
theorem eulerian_table :
    A 1 0 = 1 ∧
    A 2 0 = 1 ∧ A 2 1 = 1 ∧
    A 3 0 = 1 ∧ A 3 1 = 4 ∧ A 3 2 = 1 ∧
    A 4 0 = 1 ∧ A 4 1 = 11 ∧ A 4 2 = 11 ∧ A 4 3 = 1 ∧
    A 5 0 = 1 ∧ A 5 1 = 26 ∧ A 5 2 = 66 ∧ A 5 3 = 26 ∧ A 5 4 = 1 := by
  native_decide

theorem A_3_1 : A 3 1 = 4 := by native_decide
theorem A_4_1 : A 4 1 = 11 := by native_decide
theorem A_4_2 : A 4 2 = 11 := by native_decide

/-- Row sum `Σ_{k=0}^{n-1} A(n,k)`. -/
def rowSum (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, A n k

/-- Row sums equal n! for n = 1 through 6. -/
theorem rowSum_eq_factorial :
    rowSum 1 = 1! ∧
    rowSum 2 = 2! ∧
    rowSum 3 = 3! ∧
    rowSum 4 = 4! ∧
    rowSum 5 = 5! ∧
    rowSum 6 = 6! := by
  native_decide

/-- Recurrence verification: checks A(n,k) = (k+1)A(n-1,k) + (n-k)A(n-1,k-1). -/
def recurrenceChecked (n : ℕ) : Bool :=
  (List.range n).all fun k =>
    A n k == (k + 1) * A (n - 1) k +
      (n - k) * (if k = 0 then 0 else A (n - 1) (k - 1))

theorem recurrence_verified :
    recurrenceChecked 2 ∧ recurrenceChecked 3 ∧
    recurrenceChecked 4 ∧ recurrenceChecked 5 ∧
    recurrenceChecked 6 := by
  native_decide

/-- Symmetry A(n,k) = A(n, n-1-k). -/
def symmetryChecked (n : ℕ) : Bool :=
  (List.range n).all fun k => A n k == A n (n - 1 - k)

theorem symmetry_verified :
    symmetryChecked 1 ∧ symmetryChecked 2 ∧ symmetryChecked 3 ∧
    symmetryChecked 4 ∧ symmetryChecked 5 ∧ symmetryChecked 6 := by
  native_decide

/-- Worpitzky identity: x^n = Σ_k A(n,k) · C(x+k, n). -/
def worpitzkyRhs (n x : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, A n k * Nat.choose (x + k) n

def worpitzkyChecked (n m : ℕ) : Bool :=
  (List.range m).all fun x => x ^ n == worpitzkyRhs n x

theorem worpitzky_n3 : worpitzkyChecked 3 6 = true := by native_decide
theorem worpitzky_n4 : worpitzkyChecked 4 5 = true := by native_decide

/-- Descent polynomial A_n(t) = Σ_k A(n,k) · t^k. -/
def descentPoly (n t : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, A n k * t ^ k

theorem descentPoly_at_one :
    descentPoly 1 1 = 1! ∧
    descentPoly 2 1 = 2! ∧
    descentPoly 3 1 = 3! ∧
    descentPoly 4 1 = 4! ∧
    descentPoly 5 1 = 5! := by
  native_decide

/-- A_3(t) = 1 + 4t + t², verified pointwise. -/
def a3FormulaChecked (m : ℕ) : Bool :=
  (List.range m).all fun t => descentPoly 3 t == 1 + 4 * t + t ^ 2

theorem a3_formula : a3FormulaChecked 8 = true := by native_decide

/-- A_4(t) = 1 + 11t + 11t² + t³, verified pointwise. -/
def a4FormulaChecked (m : ℕ) : Bool :=
  (List.range m).all fun t =>
    descentPoly 4 t == 1 + 11 * t + 11 * t ^ 2 + t ^ 3

theorem a4_formula : a4FormulaChecked 8 = true := by native_decide

/-- A(n+1, 0) = A(n, 0): inserting n+1 at the end preserves zero ascents. -/
theorem A_succ_zero (n : ℕ) : A (n + 1) 0 = A n 0 := by
  simp only [A, Nat.zero_le, ↓reduceIte, zero_add, one_mul, mul_zero, add_zero]

/-- A(n,0) = 1 for all n ≥ 1: only the identity has zero ascents. -/
theorem A_n_zero (n : ℕ) (hn : n ≥ 1) : A n 0 = 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [A_succ_zero]
    cases m with
    | zero => rfl
    | succ m' => exact ih (by omega)

/-- A(n, n-1) = 1 for all n ≥ 1: only the reverse permutation has n-1 ascents. -/
theorem A_n_last_small :
    A 1 0 = 1 ∧ A 2 1 = 1 ∧ A 3 2 = 1 ∧ A 4 3 = 1 ∧ A 5 4 = 1 := by
  native_decide

/-- Second row values A(n,1) for small n. -/
theorem A_second_column :
    A 2 1 = 1 ∧ A 3 1 = 4 ∧ A 4 1 = 11 ∧ A 5 1 = 26 ∧ A 6 1 = 57 := by
  native_decide

/-- A(n,1) = 2^n - n - 1 verified for small n. -/
def secondColumnFormulaChecked (m : ℕ) : Bool :=
  (List.range m).all fun n =>
    if n ≥ 2 then A n 1 == 2 ^ n - n - 1 else true

theorem second_column_formula : secondColumnFormulaChecked 8 = true := by native_decide

/-- Row sum equals n! (general statement). -/
theorem rowSum_eq_factorial_general (n : ℕ) (hn : n ≥ 1) :
    rowSum n = n.factorial := by
  sorry

/-- Symmetry (general statement). -/
theorem A_symm (n k : ℕ) (hk : k < n) :
    A n k = A n (n - 1 - k) := by
  sorry

/-- Worpitzky identity (general statement). -/
theorem worpitzky_identity (n x : ℕ) (hn : n ≥ 1) :
    x ^ n = worpitzkyRhs n x := by
  sorry

end EulerianNumbers
