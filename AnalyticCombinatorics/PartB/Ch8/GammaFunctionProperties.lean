import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace GammaFunctionProperties

/-!
  Properties of the Gamma function relevant to asymptotic analysis in
  Chapter VIII of Flajolet and Sedgewick, recorded as finite arithmetic
  certificates.

  The analytic constants are represented by integer functions, tables, and
  cross-multiplied rational identities so that every check is decidable by
  `native_decide`.
-/

/-! ## 1. Gamma values at small integers -/

/-- Integer-specialized Gamma values: `Gamma(n) = (n - 1)!` for `n >= 1`. -/
def gammaInteger : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.factorial n

theorem gamma_integer_values_as_factorials :
    gammaInteger 1 = Nat.factorial 0 ∧
      gammaInteger 2 = Nat.factorial 1 ∧
      gammaInteger 3 = Nat.factorial 2 ∧
      gammaInteger 4 = Nat.factorial 3 ∧
      gammaInteger 5 = Nat.factorial 4 := by
  native_decide

theorem gamma_integer_small_values :
    gammaInteger 1 = 1 ∧
      gammaInteger 2 = 1 ∧
      gammaInteger 3 = 2 ∧
      gammaInteger 4 = 6 ∧
      gammaInteger 5 = 24 := by
  native_decide

theorem gamma_integer_formula_1_to_12 :
    ∀ n : Fin 13, 1 ≤ n.val →
      gammaInteger n.val = Nat.factorial (n.val - 1) := by
  native_decide

/-! ## 2. Doubling-formula numerical checks -/

/--
Numerator of the coefficient of `sqrt(pi)` in
`Gamma(n + 1/2) = (2n)! sqrt(pi) / (4^n n!)`.
-/
def gammaHalfCoeffNumerator (n : ℕ) : ℕ :=
  Nat.factorial (2 * n)

/--
Denominator of the coefficient of `sqrt(pi)` in
`Gamma(n + 1/2) = (2n)! sqrt(pi) / (4^n n!)`.
-/
def gammaHalfCoeffDenominator (n : ℕ) : ℕ :=
  4^n * Nat.factorial n

/-- Reduced numerators for `Gamma(n + 1/2) / sqrt(pi)`, for `0 <= n <= 7`. -/
def gammaHalfCoeffReducedNumeratorTable : Fin 8 → ℕ :=
  ![1, 1, 3, 15, 105, 945, 10395, 135135]

/-- Reduced denominators for `Gamma(n + 1/2) / sqrt(pi)`, for `0 <= n <= 7`. -/
def gammaHalfCoeffReducedDenominatorTable : Fin 8 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128]

theorem gamma_half_coeff_table_matches_factorial_formula :
    ∀ n : Fin 8,
      gammaHalfCoeffReducedNumeratorTable n * gammaHalfCoeffDenominator n.val =
        gammaHalfCoeffReducedDenominatorTable n * gammaHalfCoeffNumerator n.val := by
  native_decide

/--
Cross-multiplied check of
`Gamma(n) Gamma(n + 1/2) / sqrt(pi) = (2n)! / (4^n n)`, for `1 <= n <= 7`.
-/
theorem gamma_integer_half_product_doubling_check_1_to_7 :
    ∀ n : Fin 8, 1 ≤ n.val →
      gammaInteger n.val * gammaHalfCoeffNumerator n.val * (4^n.val * n.val) =
        gammaHalfCoeffDenominator n.val * Nat.factorial (2 * n.val) := by
  native_decide

theorem gamma_integer_half_product_examples :
    gammaInteger 1 * gammaHalfCoeffNumerator 1 * (4^1 * 1) =
        gammaHalfCoeffDenominator 1 * Nat.factorial 2 ∧
      gammaInteger 3 * gammaHalfCoeffNumerator 3 * (4^3 * 3) =
        gammaHalfCoeffDenominator 3 * Nat.factorial 6 ∧
      gammaInteger 5 * gammaHalfCoeffNumerator 5 * (4^5 * 5) =
        gammaHalfCoeffDenominator 5 * Nat.factorial 10 := by
  native_decide

/-! ## 3. Catalan numbers from central binomial coefficients -/

/-- Catalan number `C_n = binomial(2n,n)/(n+1)`. -/
def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Catalan values `C_0` through `C_10`. -/
def catalanTable : Fin 11 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]

theorem catalan_table_matches_central_binomial :
    ∀ n : Fin 11,
      catalanTable n = catalanNumber n.val ∧
        catalanTable n * (n.val + 1) = Nat.choose (2 * n.val) n.val := by
  native_decide

theorem catalan_selected_values :
    catalanNumber 0 = 1 ∧
      catalanNumber 3 = 5 ∧
      catalanNumber 5 = 42 ∧
      catalanNumber 8 = 1430 ∧
      catalanNumber 10 = 16796 := by
  native_decide

/-! ## 4. Stirling approximation quality -/

/--
Tabulated values of
`floor(sqrt(2*pi*n) * (n/e)^n)` for `0 <= n <= 12`, with the `n = 0`
slot unused by the positive-`n` checks.
-/
def stirlingFloorApproxTable : Fin 13 → ℕ :=
  ![0, 0, 1, 5, 23, 118, 710, 4980, 39902, 359536, 3598695, 39615625, 475687486]

theorem stirling_floor_approx_lower_bound_1_to_12 :
    ∀ n : Fin 13, 1 ≤ n.val →
      stirlingFloorApproxTable n ≤ Nat.factorial n.val := by
  native_decide

theorem stirling_floor_approx_factor_two_2_to_12 :
    ∀ n : Fin 13, 2 ≤ n.val →
      Nat.factorial n.val ≤ 2 * stirlingFloorApproxTable n := by
  native_decide

theorem stirling_floor_approx_twelve_tenths_3_to_12 :
    ∀ n : Fin 13, 3 ≤ n.val →
      10 * Nat.factorial n.val ≤ 12 * stirlingFloorApproxTable n := by
  native_decide

theorem stirling_floor_selected_values :
    stirlingFloorApproxTable 3 = 5 ∧
      stirlingFloorApproxTable 5 = 118 ∧
      stirlingFloorApproxTable 8 = 39902 ∧
      stirlingFloorApproxTable 12 = 475687486 := by
  native_decide

/-! ## 5. Wallis product partial evaluations -/

/-- Double factorial with `0!! = 1` and `1!! = 1`. -/
def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * doubleFactorial n

/-- Numerator of the `k`th Wallis partial product. -/
def wallisNumerator (k : ℕ) : ℕ :=
  doubleFactorial (2 * k) ^ 2

/-- Denominator of the `k`th Wallis partial product. -/
def wallisDenominator (k : ℕ) : ℕ :=
  doubleFactorial (2 * k - 1) * doubleFactorial (2 * k + 1)

/-- Reduced numerators for Wallis partial products, for `0 <= k <= 8`. -/
def wallisReducedNumeratorTable : Fin 9 → ℕ :=
  ![1, 4, 64, 256, 16384, 65536, 1048576, 4194304, 1073741824]

/-- Reduced denominators for Wallis partial products, for `0 <= k <= 8`. -/
def wallisReducedDenominatorTable : Fin 9 → ℕ :=
  ![1, 3, 45, 175, 11025, 43659, 693693, 2760615, 703956825]

theorem wallis_partial_table_matches_double_factorials :
    ∀ k : Fin 9,
      wallisNumerator k.val * wallisReducedDenominatorTable k =
        wallisDenominator k.val * wallisReducedNumeratorTable k := by
  native_decide

theorem wallis_partials_increase_0_to_8 :
    ∀ k : Fin 8,
      wallisNumerator k.val * wallisDenominator (k.val + 1) ≤
        wallisNumerator (k.val + 1) * wallisDenominator k.val := by
  native_decide

theorem wallis_partials_bounded_by_two_0_to_8 :
    ∀ k : Fin 9,
      wallisNumerator k.val < 2 * wallisDenominator k.val := by
  native_decide

/-! ## 6. Beta function at integers -/

/-- Numerator of `B(m,n)` at positive integers. -/
def betaIntegerNumerator (m n : ℕ) : ℕ :=
  gammaInteger m * gammaInteger n

/-- Denominator of `B(m,n)` at positive integers. -/
def betaIntegerDenominator (m n : ℕ) : ℕ :=
  gammaInteger (m + n)

/--
Cross-multiplied integer form of
`B(m,n) = (m-1)! (n-1)! / (m+n-1)!`, checked for `1 <= m,n <= 8`.
-/
theorem beta_integer_factorial_formula_1_to_8 :
    ∀ m n : Fin 9, 1 ≤ m.val → 1 ≤ n.val →
      betaIntegerNumerator m.val n.val * Nat.factorial (m.val + n.val - 1) =
        betaIntegerDenominator m.val n.val *
          (Nat.factorial (m.val - 1) * Nat.factorial (n.val - 1)) := by
  native_decide

theorem beta_integer_selected_values :
    betaIntegerNumerator 1 1 = 1 ∧ betaIntegerDenominator 1 1 = 1 ∧
      betaIntegerNumerator 1 2 = 1 ∧ betaIntegerDenominator 1 2 = 2 ∧
      betaIntegerNumerator 2 3 = 2 ∧ betaIntegerDenominator 2 3 = 24 ∧
      betaIntegerNumerator 3 4 = 12 ∧ betaIntegerDenominator 3 4 = 720 ∧
      betaIntegerNumerator 5 5 = 576 ∧ betaIntegerDenominator 5 5 = 362880 := by
  native_decide

end GammaFunctionProperties
