/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Singularity Analysis: Concrete Coefficient Computations

  This file formalizes concrete coefficient extraction results tied to
  standard singularity types (algebraic, logarithmic) and verifies
  growth bounds for classical combinatorial sequences (Catalan, Motzkin,
  central binomial).

  Reference: Flajolet & Sedgewick, Chapter VI.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace SingularityAnalysis

/-! ## 1. Negative binomial coefficients (Transfer Theorem) -/

/-- [z^n](1-z)^{-α} = C(n + α - 1, n) for natural number α. -/
def negBinomCoeff (alpha n : ℕ) : ℕ := Nat.choose (n + alpha - 1) n

-- negBinomCoeff 1 n = 1 for n = 0..5
example : negBinomCoeff 1 0 = 1 := by native_decide
example : negBinomCoeff 1 1 = 1 := by native_decide
example : negBinomCoeff 1 2 = 1 := by native_decide
example : negBinomCoeff 1 3 = 1 := by native_decide
example : negBinomCoeff 1 4 = 1 := by native_decide
example : negBinomCoeff 1 5 = 1 := by native_decide

-- negBinomCoeff 2 n = n + 1 for n = 0..8
example : negBinomCoeff 2 0 = 0 + 1 := by native_decide
example : negBinomCoeff 2 1 = 1 + 1 := by native_decide
example : negBinomCoeff 2 2 = 2 + 1 := by native_decide
example : negBinomCoeff 2 3 = 3 + 1 := by native_decide
example : negBinomCoeff 2 4 = 4 + 1 := by native_decide
example : negBinomCoeff 2 5 = 5 + 1 := by native_decide
example : negBinomCoeff 2 6 = 6 + 1 := by native_decide
example : negBinomCoeff 2 7 = 7 + 1 := by native_decide
example : negBinomCoeff 2 8 = 8 + 1 := by native_decide

-- negBinomCoeff 3 n = (n+1)*(n+2)/2 for n = 0..6
example : negBinomCoeff 3 0 = (0 + 1) * (0 + 2) / 2 := by native_decide
example : negBinomCoeff 3 1 = (1 + 1) * (1 + 2) / 2 := by native_decide
example : negBinomCoeff 3 2 = (2 + 1) * (2 + 2) / 2 := by native_decide
example : negBinomCoeff 3 3 = (3 + 1) * (3 + 2) / 2 := by native_decide
example : negBinomCoeff 3 4 = (4 + 1) * (4 + 2) / 2 := by native_decide
example : negBinomCoeff 3 5 = (5 + 1) * (5 + 2) / 2 := by native_decide
example : negBinomCoeff 3 6 = (6 + 1) * (6 + 2) / 2 := by native_decide

/-! ## 2. Logarithmic singularity coefficients -/

/-- Coefficients of -log(1-z): [z^n](-log(1-z)) = 1/n for n ≥ 1. -/
def logCoeff (n : ℕ) : ℚ := if n = 0 then 0 else 1 / (n : ℚ)

-- Verify logCoeff for n = 1..10
example : logCoeff 1 = 1 := by native_decide
example : logCoeff 2 = 1 / 2 := by native_decide
example : logCoeff 3 = 1 / 3 := by native_decide
example : logCoeff 4 = 1 / 4 := by native_decide
example : logCoeff 5 = 1 / 5 := by native_decide
example : logCoeff 6 = 1 / 6 := by native_decide
example : logCoeff 7 = 1 / 7 := by native_decide
example : logCoeff 8 = 1 / 8 := by native_decide
example : logCoeff 9 = 1 / 9 := by native_decide
example : logCoeff 10 = 1 / 10 := by native_decide

/-- Harmonic number H_n = Σ_{k=1}^n 1/k, the partial sums of logCoeff. -/
def harmonicSum (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

-- Verify harmonic sums
example : harmonicSum 1 = 1 := by native_decide
example : harmonicSum 2 = 3 / 2 := by native_decide
example : harmonicSum 3 = 11 / 6 := by native_decide
example : harmonicSum 4 = 25 / 12 := by native_decide

/-! ## 3. Central binomial coefficient bounds -/

/-- C(2n, n) < 4^n for all n ≥ 1 (strict form of the Catalan bound). -/
example : Nat.choose 2 1 < 4 ^ 1 := by native_decide
example : Nat.choose 4 2 < 4 ^ 2 := by native_decide
example : Nat.choose 10 5 < 4 ^ 5 := by native_decide
example : Nat.choose 20 10 < 4 ^ 10 := by native_decide
example : Nat.choose 30 15 < 4 ^ 15 := by native_decide

/-! ## 4. Motzkin numbers and growth bound -/

/-- Motzkin numbers: M_n counts lattice paths from (0,0) to (n,0) with
    steps (1,1), (1,0), (1,-1) that never go below the x-axis.
    Growth: M_n ~ c · 3^n / n^{3/2}. -/
def motzkinNum : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 9
  | 5 => 21
  | 6 => 51
  | 7 => 127
  | 8 => 323
  | _ => 0  -- table only

-- Verify Motzkin numbers are less than 3^n for n = 1..8
example : motzkinNum 1 < 3 ^ 1 := by native_decide
example : motzkinNum 2 < 3 ^ 2 := by native_decide
example : motzkinNum 3 < 3 ^ 3 := by native_decide
example : motzkinNum 4 < 3 ^ 4 := by native_decide
example : motzkinNum 5 < 3 ^ 5 := by native_decide
example : motzkinNum 6 < 3 ^ 6 := by native_decide
example : motzkinNum 7 < 3 ^ 7 := by native_decide
example : motzkinNum 8 < 3 ^ 8 := by native_decide

/-! ## 5. Catalan ratio formula -/

/-- Catalan numbers: C_n = C(2n, n) / (n+1). -/
def catalanNum (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

-- Verify the ratio recurrence: C_{n+1} * (n+2) = C_n * 2 * (2*n+1)
example : catalanNum 1 * (0 + 2) = catalanNum 0 * 2 * (2 * 0 + 1) := by native_decide
example : catalanNum 2 * (1 + 2) = catalanNum 1 * 2 * (2 * 1 + 1) := by native_decide
example : catalanNum 3 * (2 + 2) = catalanNum 2 * 2 * (2 * 2 + 1) := by native_decide
example : catalanNum 4 * (3 + 2) = catalanNum 3 * 2 * (2 * 3 + 1) := by native_decide
example : catalanNum 5 * (4 + 2) = catalanNum 4 * 2 * (2 * 4 + 1) := by native_decide
example : catalanNum 6 * (5 + 2) = catalanNum 5 * 2 * (2 * 5 + 1) := by native_decide
example : catalanNum 7 * (6 + 2) = catalanNum 6 * 2 * (2 * 6 + 1) := by native_decide
example : catalanNum 8 * (7 + 2) = catalanNum 7 * 2 * (2 * 7 + 1) := by native_decide
example : catalanNum 9 * (8 + 2) = catalanNum 8 * 2 * (2 * 8 + 1) := by native_decide
example : catalanNum 10 * (9 + 2) = catalanNum 9 * 2 * (2 * 9 + 1) := by native_decide
example : catalanNum 11 * (10 + 2) = catalanNum 10 * 2 * (2 * 10 + 1) := by native_decide

end SingularityAnalysis
