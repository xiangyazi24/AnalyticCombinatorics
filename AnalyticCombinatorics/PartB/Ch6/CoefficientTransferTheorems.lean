import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace CoefficientTransferTheorems

/-!
Chapter VI transfer-theorem coefficient checks from Flajolet--Sedgewick.

The analytic statements are represented here by finite, computable coefficient
tables and by rational checks of the numerical scales that occur in transfer
theorems.  Every theorem below is decidable and is verified by native
computation.
-/

/-! ## Standard scale: [z^n] (1 - z)^(-alpha) -/

/-- For positive integer `alpha`, the standard coefficient scale is
`[z^n] (1 - z)^(-alpha) = (n + alpha - 1).choose n`. -/
def standardScale (alpha n : ℕ) : ℕ :=
  (n + alpha - 1).choose n

/-- Coefficients of `(1 - z)^(-1)` for `n = 0, ..., 7`. -/
def poleOneTable : Fin 8 → ℕ := ![1, 1, 1, 1, 1, 1, 1, 1]

/-- Coefficients of `(1 - z)^(-2)` for `n = 0, ..., 7`. -/
def poleTwoTable : Fin 8 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8]

/-- Coefficients of `(1 - z)^(-3)` for `n = 0, ..., 7`. -/
def poleThreeTable : Fin 8 → ℕ := ![1, 3, 6, 10, 15, 21, 28, 36]

/-- Coefficients of `(1 - z)^(-4)` for `n = 0, ..., 7`. -/
def poleFourTable : Fin 8 → ℕ := ![1, 4, 10, 20, 35, 56, 84, 120]

theorem standard_scale_alpha_one_table :
    ∀ n : Fin 8, poleOneTable n = standardScale 1 n.val := by
  native_decide

theorem standard_scale_alpha_two_table :
    ∀ n : Fin 8, poleTwoTable n = standardScale 2 n.val := by
  native_decide

theorem standard_scale_alpha_three_table :
    ∀ n : Fin 8, poleThreeTable n = standardScale 3 n.val := by
  native_decide

theorem standard_scale_alpha_four_table :
    ∀ n : Fin 8, poleFourTable n = standardScale 4 n.val := by
  native_decide

theorem pole_one_coefficients :
    ∀ n : Fin 12, standardScale 1 n.val = 1 := by
  native_decide

theorem pole_two_coefficients :
    ∀ n : Fin 12, standardScale 2 n.val = n.val + 1 := by
  native_decide

theorem pole_three_coefficients :
    ∀ n : Fin 12, standardScale 3 n.val = (n.val + 2).choose 2 := by
  native_decide

/-! ## Logarithmic singularity: [z^n] log(1 / (1 - z)) = 1 / n -/

/-- Coefficient of `log(1 / (1 - z))`, with the constant coefficient set to `0`. -/
def logCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else 1 / (n : ℚ)

/-- Logarithmic coefficients for `n = 1, ..., 8`. -/
def logCoeffTable : Fin 8 → ℚ :=
  ![(1 : ℚ), (1 : ℚ) / 2, (1 : ℚ) / 3, (1 : ℚ) / 4,
    (1 : ℚ) / 5, (1 : ℚ) / 6, (1 : ℚ) / 7, (1 : ℚ) / 8]

theorem log_coeff_table :
    ∀ n : Fin 8, logCoeffTable n = logCoeff (n.val + 1) := by
  native_decide

theorem n_times_log_coeff :
    ∀ n : Fin 10, ((n.val + 1 : ℕ) : ℚ) * logCoeff (n.val + 1) = 1 := by
  native_decide

/-- Harmonic number `H_n = sum_{k=1}^n 1/k`, as a rational. -/
def harmonicQ (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

/-- Partial sums of logarithmic coefficients. -/
def logCoeffPartialSum (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, logCoeff (k + 1)

theorem log_coeff_partial_sums_are_harmonic :
    ∀ n : Fin 10, logCoeffPartialSum (n.val + 1) = harmonicQ (n.val + 1) := by
  native_decide

/-- Harmonic numbers `H_1, ..., H_10`. -/
def harmonicTable : Fin 10 → ℚ :=
  ![(1 : ℚ), (3 : ℚ) / 2, (11 : ℚ) / 6, (25 : ℚ) / 12,
    (137 : ℚ) / 60, (49 : ℚ) / 20, (363 : ℚ) / 140,
    (761 : ℚ) / 280, (7129 : ℚ) / 2520, (7381 : ℚ) / 2520]

/-- Numerators of `H_1, ..., H_10` in lowest terms. -/
def harmonicNumeratorTable : Fin 10 → ℤ :=
  ![1, 3, 11, 25, 137, 49, 363, 761, 7129, 7381]

/-- Denominators of `H_1, ..., H_10` in lowest terms. -/
def harmonicDenominatorTable : Fin 10 → ℕ :=
  ![1, 2, 6, 12, 60, 20, 140, 280, 2520, 2520]

theorem harmonic_table_values :
    ∀ n : Fin 10, harmonicTable n = harmonicQ (n.val + 1) := by
  native_decide

theorem harmonic_table_numerators :
    ∀ n : Fin 10, (harmonicQ (n.val + 1)).num = harmonicNumeratorTable n := by
  native_decide

theorem harmonic_table_denominators :
    ∀ n : Fin 10, (harmonicQ (n.val + 1)).den = harmonicDenominatorTable n := by
  native_decide

/-- Values of `n * H_n` for `n = 1, ..., 10`. -/
def nTimesHarmonicTable : Fin 10 → ℚ :=
  ![(1 : ℚ), (3 : ℚ), (11 : ℚ) / 2, (25 : ℚ) / 3,
    (137 : ℚ) / 12, (147 : ℚ) / 10, (363 : ℚ) / 20,
    (761 : ℚ) / 35, (7129 : ℚ) / 280, (7381 : ℚ) / 252]

theorem n_times_harmonic_table :
    ∀ n : Fin 10,
      nTimesHarmonicTable n = ((n.val + 1 : ℕ) : ℚ) * harmonicQ (n.val + 1) := by
  native_decide

/-! ## Algebraic singularity: sqrt(1 - z) -/

/-- Coefficient of `sqrt(1 - z)`.  For `n >= 1` it is
`- (2n choose n) / (4^n * (2n - 1))`. -/
def sqrtOneMinusCoeff (n : ℕ) : ℚ :=
  if n = 0 then 1
  else -(((2 * n).choose n : ℚ) / (((4 : ℕ) ^ n * (2 * n - 1) : ℕ) : ℚ))

/-- Coefficients of `sqrt(1 - z)` for `n = 0, ..., 7`. -/
def sqrtOneMinusCoeffTable : Fin 8 → ℚ :=
  ![(1 : ℚ), -((1 : ℚ) / 2), -((1 : ℚ) / 8), -((1 : ℚ) / 16),
    -((5 : ℚ) / 128), -((7 : ℚ) / 256), -((21 : ℚ) / 1024),
    -((33 : ℚ) / 2048)]

theorem sqrt_one_minus_coeff_table :
    ∀ n : Fin 8, sqrtOneMinusCoeffTable n = sqrtOneMinusCoeff n.val := by
  native_decide

theorem sqrt_one_minus_central_binomial_relation :
    ∀ n : Fin 8,
      let m := n.val + 1
      sqrtOneMinusCoeff m * (((4 : ℕ) ^ m * (2 * m - 1 : ℕ) : ℕ) : ℚ) =
        -(((2 * m).choose m : ℕ) : ℚ) := by
  native_decide

/-! ## Catalan transfer scale: C_n ~ 4^n / (n^(3/2) * sqrt(pi)) -/

/-- Catalan number `C_n = (2n choose n) / (n + 1)`. -/
def catalanNumber (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

/-- Catalan numbers for `n = 0, ..., 12`. -/
def catalanTable : Fin 13 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012]

theorem catalan_table_values :
    ∀ n : Fin 13, catalanTable n = catalanNumber n.val := by
  native_decide

/-- Squared Catalan transfer scale:
`C_n^2 * n^3 / 16^n`, which tends to `1 / pi` if
`C_n ~ 4^n / (n^(3/2) * sqrt(pi))`. -/
def catalanTransferSquareScale (n : ℕ) : ℚ :=
  ((catalanNumber n : ℚ) ^ 2 * ((n : ℚ) ^ 3)) / ((16 : ℚ) ^ n)

theorem catalan_transfer_square_scale_window_5_to_12 :
    ∀ n : Fin 8,
      (1 : ℚ) / 5 < catalanTransferSquareScale (n.val + 5) ∧
        catalanTransferSquareScale (n.val + 5) < (1 : ℚ) / 3 := by
  native_decide

theorem catalan_transfer_square_scale_increases_5_to_12 :
    ∀ n : Fin 7,
      catalanTransferSquareScale (n.val + 5) <
        catalanTransferSquareScale (n.val + 6) := by
  native_decide

/-! ## Central binomial ratio: (2n choose n) / 4^n ~ 1 / sqrt(pi n) -/

/-- Central binomial coefficient `(2n choose n)`. -/
def centralBinomial (n : ℕ) : ℕ :=
  (2 * n).choose n

/-- Ratios `(2n choose n) / 4^n` for `n = 1, ..., 8`. -/
def centralBinomialRatioTable : Fin 8 → ℚ :=
  ![(1 : ℚ) / 2, (3 : ℚ) / 8, (5 : ℚ) / 16, (35 : ℚ) / 128,
    (63 : ℚ) / 256, (231 : ℚ) / 1024, (429 : ℚ) / 2048,
    (6435 : ℚ) / 32768]

/-- The central-binomial ratio `(2n choose n) / 4^n`. -/
def centralBinomialRatio (n : ℕ) : ℚ :=
  (centralBinomial n : ℚ) / ((4 : ℚ) ^ n)

theorem central_binomial_ratio_table :
    ∀ n : Fin 8, centralBinomialRatioTable n = centralBinomialRatio (n.val + 1) := by
  native_decide

theorem central_binomial_ratio_decreases_1_to_8 :
    ∀ n : Fin 7,
      centralBinomialRatio (n.val + 2) < centralBinomialRatio (n.val + 1) := by
  native_decide

/-- Squared scale for `(2n choose n) / 4^n ~ 1 / sqrt(pi n)`.
It is `n * ((2n choose n) / 4^n)^2`, tending to `1 / pi`. -/
def centralBinomialSquareScale (n : ℕ) : ℚ :=
  (n : ℚ) * (centralBinomialRatio n) ^ 2

theorem central_binomial_square_scale_window_5_to_12 :
    ∀ n : Fin 8,
      (3 : ℚ) / 10 < centralBinomialSquareScale (n.val + 5) ∧
        centralBinomialSquareScale (n.val + 5) < (1 : ℚ) / 3 := by
  native_decide

theorem central_binomial_square_scale_increases_1_to_8 :
    ∀ n : Fin 7,
      centralBinomialSquareScale (n.val + 1) <
        centralBinomialSquareScale (n.val + 2) := by
  native_decide

end CoefficientTransferTheorems
