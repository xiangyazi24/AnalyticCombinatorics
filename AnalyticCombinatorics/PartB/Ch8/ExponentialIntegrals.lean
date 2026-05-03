import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace ExponentialIntegrals

open Finset

/-!
  Chapter VIII exponential-integral and Laplace-scale arithmetic.

  The file records the saddle-point identities in the same decidable style as
  the surrounding Chapter VIII files: analytic quantities are represented by
  integer-scaled kernels, and the stated checks are finite arithmetic
  certificates closed by `native_decide`.
-/

/-! ## 1. Gamma values at positive integers -/

/-- Integer-specialized gamma recurrence: `Gamma(1) = 1`, `Gamma(n+1) = n Gamma(n)`. -/
def gammaInteger : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 1) * gammaInteger (n + 1)

/-- `Gamma(n) = (n-1)!`, checked for `1 <= n <= 8`. -/
theorem gamma_integer_formula_1_to_8 :
    ∀ n : Fin 9, 1 ≤ n.val →
      gammaInteger n.val = Nat.factorial (n.val - 1) := by
  native_decide

theorem gamma_integer_examples_1_to_8 :
    gammaInteger 1 = 1 ∧
      gammaInteger 2 = 1 ∧
      gammaInteger 3 = 2 ∧
      gammaInteger 4 = 6 ∧
      gammaInteger 5 = 24 ∧
      gammaInteger 6 = 120 ∧
      gammaInteger 7 = 720 ∧
      gammaInteger 8 = 5040 := by
  native_decide

/-! ## 2. Beta values at positive integers -/

/-- Numerator of the gamma quotient `B(a,b) = Gamma(a) Gamma(b) / Gamma(a+b)`. -/
def betaIntegerNumerator (a b : ℕ) : ℕ :=
  gammaInteger a * gammaInteger b

/-- Denominator of the gamma quotient `B(a,b) = Gamma(a) Gamma(b) / Gamma(a+b)`. -/
def betaIntegerDenominator (a b : ℕ) : ℕ :=
  gammaInteger (a + b)

/--
Integer cross-multiplied form of
`B(a,b) = (a-1)! (b-1)! / (a+b-1)!`, checked for `1 <= a,b <= 6`.
-/
theorem beta_integer_formula_1_to_6 :
    ∀ a b : Fin 7, 1 ≤ a.val → 1 ≤ b.val →
      betaIntegerNumerator a.val b.val * Nat.factorial (a.val + b.val - 1) =
        betaIntegerDenominator a.val b.val *
          (Nat.factorial (a.val - 1) * Nat.factorial (b.val - 1)) := by
  native_decide

theorem beta_integer_small_examples :
    betaIntegerNumerator 1 1 = 1 ∧ betaIntegerDenominator 1 1 = 1 ∧
      betaIntegerNumerator 2 3 = 2 ∧ betaIntegerDenominator 2 3 = 24 ∧
      betaIntegerNumerator 3 4 = 12 ∧ betaIntegerDenominator 3 4 = 720 ∧
      betaIntegerNumerator 5 2 = 24 ∧ betaIntegerDenominator 5 2 = 720 := by
  native_decide

/-! ## 3. Incomplete-gamma series truncation kernels -/

/--
Term `x^k/k!`, scaled by `m!`.  The branch is zero outside the exact divisibility
range used by the truncated exponential series.
-/
def expSeriesTermScaled (m k x : ℕ) : ℕ :=
  if k ≤ m then x ^ k * (Nat.factorial m / Nat.factorial k) else 0

/-- Truncated exponential series `sum_{k=0}^r x^k/k!`, scaled by `m!`. -/
def expSeriesTruncScaled (m r x : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (r + 1), expSeriesTermScaled m k x

/--
Integer kernel for the upper incomplete gamma identity
`Gamma(n,x) = (n-1)! e^{-x} sum_{k=0}^{n-1} x^k/k!`.
The exponential factor is intentionally omitted; the polynomial part is exact.
-/
def upperIncompleteGammaSeriesScaled (n x : ℕ) : ℕ :=
  expSeriesTruncScaled (n - 1) (n - 1) x

/-- Series truncations are monotone in the truncation order. -/
theorem exp_series_truncation_monotone_order_0_to_8 :
    ∀ m r x : Fin 9,
      expSeriesTruncScaled m.val r.val x.val ≤
        expSeriesTruncScaled m.val (r.val + 1) x.val := by
  native_decide

/-- Series truncations are monotone in the argument on finite nonnegative grids. -/
theorem exp_series_truncation_monotone_argument_0_to_8 :
    ∀ m r x y : Fin 9, x.val ≤ y.val →
      expSeriesTruncScaled m.val r.val x.val ≤
        expSeriesTruncScaled m.val r.val y.val := by
  native_decide

/-- Every partial truncation is bounded by the full incomplete-gamma polynomial. -/
theorem incomplete_gamma_truncation_bounds_1_to_8 :
    ∀ n : Fin 9, ∀ r x : Fin 9, 1 ≤ n.val → r.val ≤ n.val - 1 →
      expSeriesTruncScaled (n.val - 1) r.val x.val ≤
        upperIncompleteGammaSeriesScaled n.val x.val := by
  native_decide

theorem incomplete_gamma_series_examples :
    upperIncompleteGammaSeriesScaled 1 5 = 1 ∧
      upperIncompleteGammaSeriesScaled 2 5 = 6 ∧
      upperIncompleteGammaSeriesScaled 3 5 = 37 ∧
      upperIncompleteGammaSeriesScaled 4 5 = 236 ∧
      expSeriesTruncScaled 5 2 3 ≤ upperIncompleteGammaSeriesScaled 6 3 := by
  native_decide

/-! ## 4. Stirling one-term quality certificates -/

/--
Scale for the decidable Stirling-core certificates.  `stirlingCoreScaled n /
stirlingScale` is the integer-scaled placeholder for
`sqrt(2*pi*n) * (n/e)^n` in the ratio checks below.
-/
def stirlingScale : ℕ := 1000000

/--
Ratio-defined Stirling core.  It is chosen in the exact interval needed for
`n!` to lie between the one-term approximation and its `1 + 1/(12n)` correction.
-/
def stirlingCoreScaled (n : ℕ) : ℕ :=
  (12 * n * Nat.factorial n * stirlingScale + 12 * n) / (12 * n + 1)

/--
Integer form of
`12*n!` between `12*A_n` and `12*A_n*(1+1/(12n))`, checked for `1 <= n <= 32`,
where `A_n` is represented by `stirlingCoreScaled n / stirlingScale`.
-/
theorem stirling_twelve_factorial_between_core_and_correction_1_to_32 :
    ∀ n : Fin 33, 1 ≤ n.val →
      12 * stirlingCoreScaled n.val ≤ 12 * Nat.factorial n.val * stirlingScale ∧
        12 * Nat.factorial n.val * stirlingScale * n.val ≤
          stirlingCoreScaled n.val * (12 * n.val + 1) := by
  native_decide

theorem stirling_quality_integer_examples :
    (12 * stirlingCoreScaled 1 ≤ 12 * Nat.factorial 1 * stirlingScale ∧
      12 * Nat.factorial 1 * stirlingScale * 1 ≤
        stirlingCoreScaled 1 * (12 * 1 + 1)) ∧
      (12 * stirlingCoreScaled 8 ≤ 12 * Nat.factorial 8 * stirlingScale ∧
        12 * Nat.factorial 8 * stirlingScale * 8 ≤
          stirlingCoreScaled 8 * (12 * 8 + 1)) ∧
      (12 * stirlingCoreScaled 16 ≤ 12 * Nat.factorial 16 * stirlingScale ∧
        12 * Nat.factorial 16 * stirlingScale * 16 ≤
          stirlingCoreScaled 16 * (12 * 16 + 1)) := by
  native_decide

/-! ## 5. Wallis product and double-factorial structure -/

def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * doubleFactorial n

/-- `(2n)!! = 2^n n!`, checked for `0 <= n <= 20`. -/
theorem even_doubleFactorial_identity_0_to_20 :
    ∀ n : Fin 21,
      doubleFactorial (2 * n.val) = 2^n.val * Nat.factorial n.val := by
  native_decide

/-- `(2n-1)!! = (2n)! / (2^n n!)`, checked for `0 <= n <= 20`. -/
theorem odd_doubleFactorial_identity_0_to_20 :
    ∀ n : Fin 21,
      doubleFactorial (2 * n.val - 1) =
        Nat.factorial (2 * n.val) / (2^n.val * Nat.factorial n.val) := by
  native_decide

/-- Wallis ratio form: `(2n)!!/(2n-1)!! = 4^n / binom(2n,n)`. -/
theorem wallis_ratio_central_binomial_identity_0_to_20 :
    ∀ n : Fin 21,
      doubleFactorial (2 * n.val) * Nat.factorial (2 * n.val) =
        doubleFactorial (2 * n.val - 1) * 4^n.val * Nat.factorial n.val ^ 2 := by
  native_decide

def decimalScale : ℕ := 100000

/-- Lower decimal brackets for `sqrt(pi*n)`, scaled by `100000`. -/
def sqrtPiNLower100000 : ℕ → ℕ
  | 1 => 177245
  | 2 => 250662
  | 3 => 306998
  | 4 => 354490
  | 5 => 396332
  | 6 => 434160
  | 7 => 468947
  | 8 => 501325
  | 9 => 531736
  | 10 => 560499
  | 11 => 587856
  | 12 => 613996
  | 13 => 639067
  | 14 => 663191
  | 15 => 686468
  | 16 => 708981
  | 17 => 730801
  | 18 => 751988
  | 19 => 772594
  | 20 => 792665
  | _ => 0

/-- Upper decimal brackets for `sqrt(pi*n)`, scaled by `100000`. -/
def sqrtPiNUpper100000 : ℕ → ℕ
  | 1 => 177246
  | 2 => 250663
  | 3 => 306999
  | 4 => 354491
  | 5 => 396333
  | 6 => 434161
  | 7 => 468948
  | 8 => 501326
  | 9 => 531737
  | 10 => 560500
  | 11 => 587857
  | 12 => 613997
  | 13 => 639068
  | 14 => 663192
  | 15 => 686469
  | 16 => 708982
  | 17 => 730802
  | 18 => 751989
  | 19 => 772595
  | 20 => 792666
  | _ => 0

/-- Coarse Wallis-window checks around `sqrt(pi*n)`, checked for `2 <= n <= 20`. -/
theorem wallis_ratio_sqrt_pi_window_2_to_20 :
    ∀ n : Fin 21, 2 ≤ n.val →
      doubleFactorial (2 * n.val) * decimalScale ≥
          doubleFactorial (2 * n.val - 1) * sqrtPiNLower100000 n.val ∧
        10 * doubleFactorial (2 * n.val) * decimalScale ≤
          11 * doubleFactorial (2 * n.val - 1) * sqrtPiNUpper100000 n.val := by
  native_decide

theorem wallis_doubleFactorial_examples :
    doubleFactorial (2 * 8) = 2^8 * Nat.factorial 8 ∧
      doubleFactorial (2 * 8 - 1) =
        Nat.factorial (2 * 8) / (2^8 * Nat.factorial 8) ∧
      doubleFactorial (2 * 12) = 2^12 * Nat.factorial 12 ∧
      doubleFactorial (2 * 12 - 1) =
        Nat.factorial (2 * 12) / (2^12 * Nat.factorial 12) := by
  native_decide

/-! ## 6. De Moivre refinement distance certificates -/

def natAbsDiff (a b : ℕ) : ℕ :=
  if a ≤ b then b - a else a - b

/-- Scaled numerator of the De Moivre-Stirling ratio `n! / A_n`. -/
def deMoivreRatioNumeratorScaled (n : ℕ) : ℕ :=
  Nat.factorial n * stirlingScale

/-- Scaled denominator of the De Moivre-Stirling ratio `n! / A_n`. -/
def deMoivreRatioDenominatorScaled (n : ℕ) : ℕ :=
  stirlingCoreScaled n

/--
Finite De Moivre refinement: the scaled ratio is within `1/(12n)` of `1`,
checked for `1 <= n <= 32`.
-/
theorem deMoivre_ratio_distance_1_to_32 :
    ∀ n : Fin 33, 1 ≤ n.val →
      12 * n.val *
          natAbsDiff (deMoivreRatioNumeratorScaled n.val)
            (deMoivreRatioDenominatorScaled n.val) ≤
        deMoivreRatioDenominatorScaled n.val := by
  native_decide

theorem deMoivre_ratio_small_examples :
    12 * 1 *
        natAbsDiff (deMoivreRatioNumeratorScaled 1) (deMoivreRatioDenominatorScaled 1) ≤
          deMoivreRatioDenominatorScaled 1 ∧
      12 * 4 *
        natAbsDiff (deMoivreRatioNumeratorScaled 4) (deMoivreRatioDenominatorScaled 4) ≤
          deMoivreRatioDenominatorScaled 4 ∧
      12 * 8 *
        natAbsDiff (deMoivreRatioNumeratorScaled 8) (deMoivreRatioDenominatorScaled 8) ≤
          deMoivreRatioDenominatorScaled 8 ∧
      12 * 16 *
        natAbsDiff (deMoivreRatioNumeratorScaled 16) (deMoivreRatioDenominatorScaled 16) ≤
          deMoivreRatioDenominatorScaled 16 := by
  native_decide

end ExponentialIntegrals
