import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace PermutationDescents

open Finset

/-!
# Permutation descents and Eulerian numbers

Chapter II of Flajolet and Sedgewick uses Eulerian numbers to record the
distribution of descents in permutations.  This file keeps the definitions
computable: `eulerianNumber n k` counts permutations of `[n] = {0, ..., n-1}`
with exactly `k` descents, and the stated identities are checked by
`native_decide` over the finite ranges requested.
-/

/-- Number of descents in a finite list. -/
def descentCount : List ℕ → ℕ
  | a :: b :: xs => (if a > b then 1 else 0) + descentCount (b :: xs)
  | _ => 0

/-- Eulerian number `A(n,k)`, counted directly from permutations of `[n]`. -/
def eulerianNumber (n k : ℕ) : ℕ :=
  ((List.range n).permutations.filter fun p => descentCount p = k).length

/-- The row sum `Σ_k A(n,k)`, with `k = 0, ..., n-1`. -/
def eulerianRowSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, eulerianNumber n k

/-- The recurrence RHS, with the convention `A(n,-1)=0`. -/
def eulerianRecurrenceRhs (n k : ℕ) : ℕ :=
  (k + 1) * eulerianNumber (n - 1) k +
    (n - k) * if k = 0 then 0 else eulerianNumber (n - 1) (k - 1)

/-- The Eulerian recurrence on one row, for `k = 0, ..., n-1`. -/
def eulerianRecurrenceRowChecked (n : ℕ) : Bool :=
  (List.range n).all fun k => eulerianNumber n k == eulerianRecurrenceRhs n k

/-- Worpitzky RHS `Σ_k A(n,k) * C(x+k,n)`. -/
def worpitzkyRhs (n x : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, eulerianNumber n k * Nat.choose (x + k) n

/-- Descent polynomial evaluated at `t`: `A_n(t) = Σ_k A(n,k)t^k`. -/
def descentPolynomialEval (n t : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, eulerianNumber n k * t ^ k

/-- Descent polynomial coefficients `[A(n,0), ..., A(n,n-1)]`. -/
def descentPolynomialCoefficients (n : ℕ) : List ℕ :=
  (List.range n).map (eulerianNumber n)

/-- Worpitzky identity checked for `x = 0, ..., m-1`. -/
def worpitzkyCheckedUpTo (n m : ℕ) : Bool :=
  (List.range m).all fun x => x ^ n == worpitzkyRhs n x

/-- Polynomial formula `A_3(t)=1+4t+t^2` checked for `t = 0, ..., m-1`. -/
def descentPolynomialA3FormulaCheckedUpTo (m : ℕ) : Bool :=
  (List.range m).all fun t => descentPolynomialEval 3 t == 1 + 4 * t + t ^ 2

/-- Symmetry `A(n,k)=A(n,n-1-k)` checked for `k = 0, ..., n-1`. -/
def eulerianSymmetryRowChecked (n : ℕ) : Bool :=
  (List.range n).all fun k => eulerianNumber n k == eulerianNumber n (n - 1 - k)

/-- Eulerian table through `n=4`, counted from permutations. -/
theorem eulerian_table_small :
    eulerianNumber 1 0 = 1 ∧
    eulerianNumber 2 0 = 1 ∧ eulerianNumber 2 1 = 1 ∧
    eulerianNumber 3 0 = 1 ∧ eulerianNumber 3 1 = 4 ∧ eulerianNumber 3 2 = 1 ∧
    eulerianNumber 4 0 = 1 ∧ eulerianNumber 4 1 = 11 ∧
    eulerianNumber 4 2 = 11 ∧ eulerianNumber 4 3 = 1 := by
  native_decide

/-- Eulerian recurrence `A(n,k)=(k+1)A(n-1,k)+(n-k)A(n-1,k-1)` for `n=2..6`. -/
theorem eulerian_recurrence_checked :
    eulerianRecurrenceRowChecked 2 = true ∧
    eulerianRecurrenceRowChecked 3 = true ∧
    eulerianRecurrenceRowChecked 4 = true ∧
    eulerianRecurrenceRowChecked 5 = true ∧
    eulerianRecurrenceRowChecked 6 = true := by
  native_decide

/-- Row sums `Σ_k A(n,k)=n!` for `n=1..6`. -/
theorem eulerian_row_sums_1_to_6 :
    eulerianRowSum 1 = Nat.factorial 1 ∧
    eulerianRowSum 2 = Nat.factorial 2 ∧
    eulerianRowSum 3 = Nat.factorial 3 ∧
    eulerianRowSum 4 = Nat.factorial 4 ∧
    eulerianRowSum 5 = Nat.factorial 5 ∧
    eulerianRowSum 6 = Nat.factorial 6 := by
  native_decide

/-- Worpitzky identity `x^3 = Σ_k A(3,k) * C(x+k,3)` for `x=0..4`. -/
theorem worpitzky_n3_x0_to_4 :
    worpitzkyCheckedUpTo 3 5 = true := by
  native_decide

/-- `A_3(t)` has coefficient list `[1,4,1]`, i.e. `A_3(t)=1+4t+t^2`. -/
theorem descentPolynomial_A3_coefficients :
    descentPolynomialCoefficients 3 = [1, 4, 1] := by
  native_decide

/-- The checked polynomial form `A_3(t)=1+4t+t^2` for `t=0..6`. -/
theorem descentPolynomial_A3_formula_checked :
    descentPolynomialA3FormulaCheckedUpTo 7 = true := by
  native_decide

/-- `A_3(1)=6=3!`. -/
theorem descentPolynomial_A3_at_one :
    descentPolynomialEval 3 1 = 6 ∧ descentPolynomialEval 3 1 = Nat.factorial 3 := by
  native_decide

/-- Symmetry `A(4,k)=A(4,3-k)`. -/
theorem eulerian_symmetry_n4 :
    eulerianSymmetryRowChecked 4 = true := by
  native_decide

/-- Symmetry `A(5,k)=A(5,4-k)`. -/
theorem eulerian_symmetry_n5 :
    eulerianSymmetryRowChecked 5 = true := by
  native_decide

end PermutationDescents
