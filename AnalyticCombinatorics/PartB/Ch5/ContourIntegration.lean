import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace ContourIntegration

/-!
# Contour Integration Methods

Executable certificates for bounded coefficient checks inspired by Chapter V of
Flajolet and Sedgewick's *Analytic Combinatorics*.

The analytic identities are represented by small integer tables:

* residues of rational functions,
* Cauchy coefficient extraction,
* circle-method partition values,
* Hayman saddle/admissibility checks,
* inverse Laplace coefficient recovery.

All proofs are deliberately finite and are discharged by `native_decide`.
-/

/-- Lookup in a finite natural-number table, extended by zero. -/
def tableNat {N : ℕ} (a : Fin N → ℕ) (n : ℕ) : ℕ :=
  if h : n < N then a ⟨n, h⟩ else 0

/-! ## Residue checks for rational functions -/

/--
Coefficients of `1 / ((1 - z) * (1 - 2*z))`.
The residue computation gives `[z^n] = 2^(n+1) - 1`.
-/
def twoPoleResidueCoeffs : Fin 10 → ℕ :=
  ![1, 3, 7, 15, 31, 63, 127, 255, 511, 1023]

theorem two_pole_residue_coefficients :
    ∀ i : Fin 10, twoPoleResidueCoeffs i = 2 ^ ((i : ℕ) + 1) - 1 := by
  native_decide

/--
Coefficients of `1 / ((1 - z)^2 * (1 - 3*z))`.
Equivalently, `sum_{k=0}^n (k+1) * 3^(n-k)`.
-/
def doublePoleThreeCoeffs : Fin 8 → ℕ :=
  ![1, 5, 18, 58, 179, 543, 1636, 4916]

def doublePoleThreeFormula (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 1 * 3 + 2
  | 2 => 1 * 9 + 2 * 3 + 3
  | 3 => 1 * 27 + 2 * 9 + 3 * 3 + 4
  | 4 => 1 * 81 + 2 * 27 + 3 * 9 + 4 * 3 + 5
  | 5 => 1 * 243 + 2 * 81 + 3 * 27 + 4 * 9 + 5 * 3 + 6
  | 6 => 1 * 729 + 2 * 243 + 3 * 81 + 4 * 27 + 5 * 9 + 6 * 3 + 7
  | 7 => 1 * 2187 + 2 * 729 + 3 * 243 + 4 * 81 + 5 * 27 + 6 * 9 + 7 * 3 + 8
  | _ => 0

theorem double_pole_three_residue_table :
    ∀ i : Fin 8, doublePoleThreeCoeffs i = doublePoleThreeFormula (i : ℕ) := by
  native_decide

/-! ## Cauchy coefficient formula instances -/

/-- Cauchy's formula extracts `[z^n] 1/(1 - 3*z) = 3^n`. -/
def cauchyGeometricThreeCoeffs : Fin 9 → ℕ :=
  ![1, 3, 9, 27, 81, 243, 729, 2187, 6561]

theorem cauchy_geometric_three_coefficients :
    ∀ i : Fin 9, cauchyGeometricThreeCoeffs i = 3 ^ (i : ℕ) := by
  native_decide

/-- Cauchy extraction for `[z^n] z/(1 - z - z^2) = Fibonacci(n)`. -/
def cauchyFibonacciCoeffs : Fin 12 → ℕ :=
  ![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]

theorem cauchy_fibonacci_coefficients :
    ∀ i : Fin 12, cauchyFibonacciCoeffs i = Nat.fib (i : ℕ) := by
  native_decide

/-! ## Circle-method coefficient tables -/

/--
Partition numbers `p(n)` for `0 <= n <= 11`, the initial values targeted by
Hardy-Ramanujan-Rademacher circle-method approximants.
-/
def partitionCircleTable : Fin 12 → ℕ :=
  ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56]

def partitionCircleInt (n : ℕ) : ℤ :=
  Int.ofNat (tableNat partitionCircleTable n)

def shiftedPartitionCircleInt (n k : ℕ) : ℤ :=
  if k ≤ n then partitionCircleInt (n - k) else 0

/--
Euler's pentagonal recurrence, checked for `1 <= n <= 11`.
For this range, generalized pentagonal numbers above `12` cannot contribute.
-/
def pentagonalRecurrenceRhs (n : ℕ) : ℤ :=
  shiftedPartitionCircleInt n 1 + shiftedPartitionCircleInt n 2
    - shiftedPartitionCircleInt n 5 - shiftedPartitionCircleInt n 7
    + shiftedPartitionCircleInt n 12

theorem partition_circle_pentagonal_recurrence :
    ∀ i : Fin 11,
      let n := (i : ℕ) + 1
      partitionCircleInt n = pentagonalRecurrenceRhs n := by
  native_decide

theorem partition_circle_table_monotone :
    ∀ i : Fin 11,
      tableNat partitionCircleTable (i : ℕ) ≤
        tableNat partitionCircleTable ((i : ℕ) + 1) := by
  native_decide

/-! ## Hayman admissibility checks -/

/--
For `A(z)=exp(z)`, Hayman's saddle equation has `a(r)=r`.
The integer saddle for coefficient index `n` is `r=n`.
-/
def haymanExpSaddleRadii : Fin 10 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def haymanExpA (r : ℕ) : ℕ := r

def haymanExpB (r : ℕ) : ℕ := r

theorem hayman_exp_saddle_matches_index :
    ∀ i : Fin 10,
      haymanExpA (haymanExpSaddleRadii i) = (i : ℕ) + 1 ∧
        0 < haymanExpB (haymanExpSaddleRadii i) := by
  native_decide

/--
For `1/(1-z)`, the rational saddle grid `r=k/(k+1)` has
`r/(1-r)=k`; this table records the denominators.
-/
def haymanGeometricDenominators : Fin 10 → ℕ :=
  ![2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

theorem hayman_geometric_integerized_saddles :
    ∀ i : Fin 10,
      let k := (i : ℕ) + 1
      let d := haymanGeometricDenominators i
      d = k + 1 ∧ k / (d - k) = k := by
  native_decide

/-! ## Inverse Laplace coefficient checks -/

/--
Inverse Laplace recovery for the Borel transform `1/(1 - 2*z)`:
ordinary coefficients are `n! * 2^n`.
-/
def inverseLaplaceTwoCoeffs : Fin 9 → ℕ :=
  ![1, 2, 8, 48, 384, 3840, 46080, 645120, 10321920]

theorem inverse_laplace_two_coefficients :
    ∀ i : Fin 9,
      inverseLaplaceTwoCoeffs i = Nat.factorial (i : ℕ) * 2 ^ (i : ℕ) := by
  native_decide

end ContourIntegration
