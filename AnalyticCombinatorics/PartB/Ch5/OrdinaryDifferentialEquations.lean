/-
  Analytic Combinatorics -- Part B
  Chapter V -- Ordinary Differential Equations

  Finite-table checks for holonomic recurrences and special sequences.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace OrdinaryDifferentialEquations

/-! ## 1. Catalan numbers -/

/-- Catalan numbers C(0)..C(10). -/
def catalanTable : Fin 11 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]

example : catalanTable 0 = 1 := by native_decide
example : catalanTable 1 = 1 := by native_decide
example : catalanTable 2 = 2 := by native_decide
example : catalanTable 3 = 5 := by native_decide
example : catalanTable 4 = 14 := by native_decide
example : catalanTable 5 = 42 := by native_decide
example : catalanTable 6 = 132 := by native_decide
example : catalanTable 7 = 429 := by native_decide
example : catalanTable 8 = 1430 := by native_decide
example : catalanTable 9 = 4862 := by native_decide
example : catalanTable 10 = 16796 := by native_decide

/-- Verify `(n+2) * C(n+1) = 2 * (2n+1) * C(n)` for n = 0..9. -/
example :
    ∀ n : Fin 10,
      (n.val + 2) * catalanTable ⟨n.val + 1, by omega⟩ =
        2 * (2 * n.val + 1) * catalanTable ⟨n.val, by omega⟩ := by
  native_decide

/-! ## 2. Central binomial coefficients -/

/-- Central binomial coefficients C(2n,n), n = 0..9. -/
def centralBinomialTable : Fin 10 → ℕ :=
  ![1, 2, 6, 20, 70, 252, 924, 3432, 12870, 48620]

example : centralBinomialTable 0 = 1 := by native_decide
example : centralBinomialTable 1 = 2 := by native_decide
example : centralBinomialTable 2 = 6 := by native_decide
example : centralBinomialTable 3 = 20 := by native_decide
example : centralBinomialTable 4 = 70 := by native_decide
example : centralBinomialTable 5 = 252 := by native_decide
example : centralBinomialTable 6 = 924 := by native_decide
example : centralBinomialTable 7 = 3432 := by native_decide
example : centralBinomialTable 8 = 12870 := by native_decide
example : centralBinomialTable 9 = 48620 := by native_decide

/-- Verify `(n+1) * C(2(n+1), n+1) = 2 * (2n+1) * C(2n,n)` for n = 0..8. -/
example :
    ∀ n : Fin 9,
      (n.val + 1) * centralBinomialTable ⟨n.val + 1, by omega⟩ =
        2 * (2 * n.val + 1) * centralBinomialTable ⟨n.val, by omega⟩ := by
  native_decide

/-! ## 3. Apery numbers -/

/-- Apery numbers A(0)..A(4). -/
def aperyTable : Fin 5 → ℕ :=
  ![1, 5, 73, 1445, 33001]

example : aperyTable 0 = 1 := by native_decide
example : aperyTable 1 = 5 := by native_decide
example : aperyTable 2 = 73 := by native_decide
example : aperyTable 3 = 1445 := by native_decide
example : aperyTable 4 = 33001 := by native_decide

/-! ## 4. Motzkin numbers -/

/-- Motzkin numbers M(0)..M(9). -/
def motzkinTable : Fin 10 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835]

example : motzkinTable 0 = 1 := by native_decide
example : motzkinTable 1 = 1 := by native_decide
example : motzkinTable 2 = 2 := by native_decide
example : motzkinTable 3 = 4 := by native_decide
example : motzkinTable 4 = 9 := by native_decide
example : motzkinTable 5 = 21 := by native_decide
example : motzkinTable 6 = 51 := by native_decide
example : motzkinTable 7 = 127 := by native_decide
example : motzkinTable 8 = 323 := by native_decide
example : motzkinTable 9 = 835 := by native_decide

/-- Verify `(n+3) * M(n+1) = (2n+3) * M(n) + 3*n*M(n-1)` for n = 1..8. -/
example :
    ∀ i : Fin 8,
      let n := i.val + 1
      (n + 3) * motzkinTable ⟨n + 1, by omega⟩ =
        (2 * n + 3) * motzkinTable ⟨n, by omega⟩ +
          3 * n * motzkinTable ⟨n - 1, by omega⟩ := by
  native_decide

/-! ## 5. Factorials -/

/-- Factorials n!, n = 0..10. -/
def factorialTable : Fin 11 → ℕ :=
  ![1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800]

example : factorialTable 0 = 1 := by native_decide
example : factorialTable 1 = 1 := by native_decide
example : factorialTable 2 = 2 := by native_decide
example : factorialTable 3 = 6 := by native_decide
example : factorialTable 4 = 24 := by native_decide
example : factorialTable 5 = 120 := by native_decide
example : factorialTable 6 = 720 := by native_decide
example : factorialTable 7 = 5040 := by native_decide
example : factorialTable 8 = 40320 := by native_decide
example : factorialTable 9 = 362880 := by native_decide
example : factorialTable 10 = 3628800 := by native_decide

/-- Verify `n! = n * (n-1)!` for n = 1..10. -/
example :
    ∀ i : Fin 10,
      let n := i.val + 1
      factorialTable ⟨n, by omega⟩ =
        n * factorialTable ⟨n - 1, by omega⟩ := by
  native_decide

/-! ## 6. Derangements -/

/-- Derangements D(0)..D(8). -/
def derangementTable : Fin 9 → ℕ :=
  ![1, 0, 1, 2, 9, 44, 265, 1854, 14833]

example : derangementTable 0 = 1 := by native_decide
example : derangementTable 1 = 0 := by native_decide
example : derangementTable 2 = 1 := by native_decide
example : derangementTable 3 = 2 := by native_decide
example : derangementTable 4 = 9 := by native_decide
example : derangementTable 5 = 44 := by native_decide
example : derangementTable 6 = 265 := by native_decide
example : derangementTable 7 = 1854 := by native_decide
example : derangementTable 8 = 14833 := by native_decide

/-- Verify the parity-split holonomic form for n = 2..8. -/
example :
    ∀ i : Fin 7,
      let n := i.val + 2
      if n % 2 = 0 then
        derangementTable ⟨n, by omega⟩ =
          n * derangementTable ⟨n - 1, by omega⟩ + 1
      else
        n * derangementTable ⟨n - 1, by omega⟩ =
          derangementTable ⟨n, by omega⟩ + 1 := by
  native_decide

end OrdinaryDifferentialEquations
