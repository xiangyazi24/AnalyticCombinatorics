import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AlgebraicFunctionCoefficients

/-!
  Coefficient extraction for algebraic functions, following Chapter VI of
  Flajolet and Sedgewick's Analytic Combinatorics.

  The algebraic generating functions recorded here are checked through their
  induced coefficient formulae and finite coefficient tables.
-/

-- ============================================================
-- Catalan numbers
-- ============================================================

/--
Catalan generating function:
`C(z) = (1 - sqrt(1 - 4*z)) / (2*z)`.

Coefficient formula:
`[z^n] C(z) = Nat.choose (2*n) n / (n+1)`.
-/
def catalanCoeff (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Catalan numbers `C_0, ..., C_9`. -/
def catalanTable : Fin 10 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]

/-- The closed coefficient formula gives the Catalan table for `n = 0, ..., 9`. -/
theorem catalan_formula_values_0_9 :
    ∀ n : Fin 10, catalanCoeff n = catalanTable n := by native_decide

/--
The constant term in the quadratic equation `C(z) = 1 + z*C(z)^2`, equivalent
to the displayed algebraic generating function.
-/
theorem catalan_GF_constant_term :
    catalanCoeff 0 = 1 := by native_decide

/--
The coefficients `C_1, ..., C_9` satisfy the coefficient recurrence extracted
from `C(z) = 1 + z*C(z)^2`.
-/
theorem catalan_GF_coefficients_1_9 :
    ∀ n : Fin 9,
      catalanCoeff ((n : ℕ) + 1) =
        (Finset.range ((n : ℕ) + 1)).sum
          (fun k => catalanCoeff k * catalanCoeff ((n : ℕ) - k)) := by native_decide

-- ============================================================
-- Motzkin numbers
-- ============================================================

/--
Motzkin generating function:
`M(z) = (1 - z - sqrt(1 - 2*z - 3*z^2)) / (2*z^2)`.

The coefficient formula below is
`M_n = sum_{j=0}^{floor(n/2)} Nat.choose n (2*j) * C_j`.
-/
def motzkinCoeff (n : ℕ) : ℕ :=
  (Finset.range (n / 2 + 1)).sum
    (fun j => Nat.choose n (2 * j) * catalanCoeff j)

/-- Motzkin numbers `M_0, ..., M_9`. -/
def motzkinTable : Fin 10 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835]

/-- The Motzkin coefficient formula gives the requested table. -/
theorem motzkin_values_0_9 :
    ∀ n : Fin 10, motzkinCoeff n = motzkinTable n := by native_decide

/-- The constant coefficient extracted from `M(z) = 1 + z*M(z) + z^2*M(z)^2`. -/
theorem motzkin_GF_constant_term :
    motzkinCoeff 0 = 1 := by native_decide

/-- The linear coefficient extracted from `M(z) = 1 + z*M(z) + z^2*M(z)^2`. -/
theorem motzkin_GF_linear_term :
    motzkinCoeff 1 = motzkinCoeff 0 := by native_decide

/-- The coefficients `M_2, ..., M_9` satisfy the recurrence from the Motzkin GF. -/
theorem motzkin_GF_coefficients_2_9 :
    ∀ n : Fin 8,
      motzkinCoeff ((n : ℕ) + 2) =
        motzkinCoeff ((n : ℕ) + 1) +
          (Finset.range ((n : ℕ) + 1)).sum
            (fun k => motzkinCoeff k * motzkinCoeff ((n : ℕ) - k)) := by native_decide

-- ============================================================
-- Central Delannoy numbers
-- ============================================================

/-- Central Delannoy numbers: `D(n) = sum_{k=0}^n C(n,k)^2 * 2^k`. -/
def centralDelannoy (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum
    (fun k => Nat.choose n k ^ 2 * 2 ^ k)

/-- Central Delannoy values `D(0), ..., D(5)`. -/
def centralDelannoyTable : Fin 6 → ℕ :=
  ![1, 3, 13, 63, 321, 1683]

/-- Requested central Delannoy checks. -/
theorem centralDelannoy_values_0_5 :
    ∀ n : Fin 6, centralDelannoy n = centralDelannoyTable n := by native_decide

-- ============================================================
-- Apéry numbers
-- ============================================================

/-- Apéry numbers: `A(n) = sum_{k=0}^n C(n,k)^2 * C(n+k,k)^2`. -/
def aperyNumber (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum
    (fun k => Nat.choose n k ^ 2 * Nat.choose (n + k) k ^ 2)

/-- Apéry values `A(0), ..., A(4)`. -/
def aperyTable : Fin 5 → ℕ :=
  ![1, 5, 73, 1445, 33001]

/-- Requested Apéry number checks. -/
theorem apery_values_0_4 :
    ∀ n : Fin 5, aperyNumber n = aperyTable n := by native_decide

-- ============================================================
-- Narayana numbers
-- ============================================================

/--
Narayana numbers:
`N(n,k) = (1/n) * C(n,k) * C(n,k-1)` for `n >= 1`.

The zero cases are set to `0` so that finite row sums can range over
`k = 0, ..., n`.
-/
def narayanaNumber (n k : ℕ) : ℕ :=
  if n = 0 ∨ k = 0 then
    0
  else
    (Nat.choose n k * Nat.choose n (k - 1)) / n

/-- Sum of the `n`th Narayana row. -/
def narayanaRowSum (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => narayanaNumber n k)

/-- Requested Narayana spot checks. -/
theorem narayana_values :
    narayanaNumber 3 1 = 1 ∧
    narayanaNumber 3 2 = 3 ∧
    narayanaNumber 3 3 = 1 ∧
    narayanaNumber 4 1 = 1 ∧
    narayanaNumber 4 2 = 6 ∧
    narayanaNumber 4 3 = 6 ∧
    narayanaNumber 4 4 = 1 := by native_decide

/-- The Narayana row sums agree with Catalan numbers for `n = 1, ..., 5`. -/
theorem narayana_row_sums_eq_catalan_1_5 :
    ∀ n : Fin 5, narayanaRowSum ((n : ℕ) + 1) = catalanCoeff ((n : ℕ) + 1) := by native_decide

end AlgebraicFunctionCoefficients
