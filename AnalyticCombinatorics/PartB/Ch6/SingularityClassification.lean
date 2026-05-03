import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace SingularityClassification

open Finset

/-!
Chapter VI singularity-classification identities, recorded only as finite
numerical coefficient checks that Lean can decide by computation.
-/

/-! ## Simple poles -/

/-- Coefficients of `1 / (1 - z)`. -/
def simplePoleOneCoeff (_n : ℕ) : ℕ := 1

/-- Coefficients of `1 / (1 - 2z)`. -/
def simplePoleTwoCoeff (n : ℕ) : ℕ := 2 ^ n

/-- `[z^n] 1/(1-z) = 1`, checked for `n = 0, ..., 20`. -/
theorem simple_pole_one_coeffs_0_20 :
    ∀ n ∈ Finset.range 21, simplePoleOneCoeff n = 1 := by
  native_decide

/-- `[z^n] 1/(1-2z) = 2^n`, checked for `n = 0, ..., 20`. -/
theorem simple_pole_two_coeffs_0_20 :
    ∀ n ∈ Finset.range 21, simplePoleTwoCoeff n = 2 ^ n := by
  native_decide

/-- Spot checks for the two simple-pole coefficient sequences. -/
theorem simple_pole_spot_checks :
    simplePoleOneCoeff 12 = 1 ∧
      simplePoleTwoCoeff 0 = 1 ∧
      simplePoleTwoCoeff 8 = 256 ∧
      simplePoleTwoCoeff 10 = 1024 := by
  native_decide

/-! ## Algebraic square-root singularity -/

/-- Central binomial coefficient `C(2n,n)`. -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/--
Coefficients of `sqrt(1-z)`:
`1, -1/2, -1/8, -1/16, -5/128, ...`.
For `n ≥ 1`, the coefficient is
`- C(2n,n) / (4^n * (2n - 1))`.
-/
def sqrtOneMinusZCoeff : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      -((centralBinom (n + 1) : ℚ) /
        ((4 : ℚ) ^ (n + 1) * ((2 * (n + 1) - 1 : ℕ) : ℚ)))

/-- The central-binomial formula for `sqrt(1-z)`, checked for `n = 1, ..., 12`. -/
theorem sqrt_coeff_central_binomial_connection_1_12 :
    ∀ n ∈ Finset.Icc 1 12,
      sqrtOneMinusZCoeff n =
        -((centralBinom n : ℚ) / ((4 : ℚ) ^ n * ((2 * n - 1 : ℕ) : ℚ))) := by
  native_decide

/-- Initial algebraic-singularity coefficients. -/
theorem sqrt_coeff_initial_values :
    sqrtOneMinusZCoeff 0 = 1 ∧
      sqrtOneMinusZCoeff 1 = -(1 / 2 : ℚ) ∧
      sqrtOneMinusZCoeff 2 = -(1 / 8 : ℚ) ∧
      sqrtOneMinusZCoeff 3 = -(1 / 16 : ℚ) ∧
      sqrtOneMinusZCoeff 4 = -(5 / 128 : ℚ) ∧
      sqrtOneMinusZCoeff 5 = -(7 / 256 : ℚ) := by
  native_decide

/-- Central-binomial spot checks for the associated `(1-z)^(-1/2)` scale. -/
theorem central_binomial_spot_checks :
    centralBinom 0 = 1 ∧
      centralBinom 1 = 2 ∧
      centralBinom 5 = 252 ∧
      centralBinom 10 = 184756 := by
  native_decide

/-- `C(2n,n) < 4^n`, checked for `n = 1, ..., 12`. -/
theorem central_binomial_lt_four_pow_1_12 :
    ∀ n ∈ Finset.Icc 1 12, centralBinom n < 4 ^ n := by
  native_decide

/-! ## Logarithmic singularity -/

/-- Coefficients of `log (1 / (1-z))`, with the constant coefficient included. -/
def logInvOneMinusZCoeff : ℕ → ℚ
  | 0 => 0
  | n + 1 => 1 / ((n + 1 : ℕ) : ℚ)

/-- `[z^n] log(1/(1-z)) = 1/n`, checked for `n = 1, ..., 20`. -/
theorem log_inv_one_minus_coeffs_1_20 :
    ∀ n ∈ Finset.Icc 1 20, logInvOneMinusZCoeff n = 1 / (n : ℚ) := by
  native_decide

/-- Initial logarithmic-singularity coefficients. -/
theorem log_inv_one_minus_initial_values :
    logInvOneMinusZCoeff 0 = 0 ∧
      logInvOneMinusZCoeff 1 = 1 ∧
      logInvOneMinusZCoeff 2 = 1 / 2 ∧
      logInvOneMinusZCoeff 3 = 1 / 3 ∧
      logInvOneMinusZCoeff 4 = 1 / 4 ∧
      logInvOneMinusZCoeff 5 = 1 / 5 := by
  native_decide

/-! ## Essential singularity: `exp (1 / (1-z))` -/

/--
Rational coefficient factor for the essential singularity
`exp (1 / (1-z)) = exp(1) * exp (z / (1-z))`.
Thus this is the coefficient sequence after dividing by the constant `exp(1)`.
-/
def essentialCoeffScaledByInvE : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      ∑ m ∈ Finset.Icc 1 (n + 1),
        (Nat.choose n (m - 1) : ℚ) / (Nat.factorial m : ℚ)

/-- Initial scaled coefficients for `exp(1/(1-z))`. -/
theorem essential_scaled_coeff_initial_values :
    essentialCoeffScaledByInvE 0 = 1 ∧
      essentialCoeffScaledByInvE 1 = 1 ∧
      essentialCoeffScaledByInvE 2 = 3 / 2 ∧
      essentialCoeffScaledByInvE 3 = 13 / 6 ∧
      essentialCoeffScaledByInvE 4 = 73 / 24 ∧
      essentialCoeffScaledByInvE 5 = 167 / 40 := by
  native_decide

/-- Finite upper growth check: the scaled essential coefficients stay below `2^n`. -/
theorem essential_scaled_coeff_lt_two_pow_1_16 :
    ∀ n ∈ Finset.Icc 1 16, essentialCoeffScaledByInvE n < (2 : ℚ) ^ n := by
  native_decide

/-- Finite lower growth check: the scaled essential coefficients are at least `1`. -/
theorem essential_scaled_coeff_ge_one_0_16 :
    ∀ n ∈ Finset.range 17, (1 : ℚ) ≤ essentialCoeffScaledByInvE n := by
  native_decide

/-- The scaled essential coefficients are increasing on this finite range. -/
theorem essential_scaled_coeff_increasing_0_15 :
    ∀ n ∈ Finset.range 16,
      essentialCoeffScaledByInvE n ≤ essentialCoeffScaledByInvE (n + 1) := by
  native_decide

/-! ## Multiple poles -/

/-- Coefficients of `1 / (1-z)^k`: `C(n+k-1,k-1)`. -/
def multiplePoleCoeff (k n : ℕ) : ℕ := Nat.choose (n + k - 1) (k - 1)

/-- `[z^n] 1/(1-z)^k = C(n+k-1,k-1)`, checked for small `k,n`. -/
theorem multiple_pole_coeff_formula_1_8_0_12 :
    ∀ k ∈ Finset.Icc 1 8,
      ∀ n ∈ Finset.range 13,
        multiplePoleCoeff k n = Nat.choose (n + k - 1) (k - 1) := by
  native_decide

/-- Multiple-pole specializations for `k = 1, 2, 3`. -/
theorem multiple_pole_specializations_0_12 :
    (∀ n ∈ Finset.range 13, multiplePoleCoeff 1 n = 1) ∧
      (∀ n ∈ Finset.range 13, multiplePoleCoeff 2 n = n + 1) ∧
      (∀ n ∈ Finset.range 13, multiplePoleCoeff 3 n = Nat.choose (n + 2) 2) := by
  native_decide

/-- Spot checks for higher-order poles. -/
theorem multiple_pole_spot_checks :
    multiplePoleCoeff 1 10 = 1 ∧
      multiplePoleCoeff 2 10 = 11 ∧
      multiplePoleCoeff 3 10 = 66 ∧
      multiplePoleCoeff 4 10 = 286 ∧
      multiplePoleCoeff 5 10 = 1001 := by
  native_decide

/-! ## Classification hierarchy -/

/-- Coarse hierarchy labels used in Chapter VI coefficient classification. -/
inductive FunctionClass where
  | rational
  | algebraic
  | dFinite
  | holonomic
  deriving DecidableEq, Repr

/-- Numeric rank for the displayed hierarchy. -/
def classRank : FunctionClass → ℕ
  | FunctionClass.rational => 0
  | FunctionClass.algebraic => 1
  | FunctionClass.dFinite => 2
  | FunctionClass.holonomic => 3

/-- Strict order induced by `classRank`, as a decidable Boolean relation. -/
def strictlyBelow (a b : FunctionClass) : Bool := decide (classRank a < classRank b)

/-- `rational < algebraic < D-finite < holonomic`. -/
theorem classification_hierarchy_chain :
    strictlyBelow FunctionClass.rational FunctionClass.algebraic = true ∧
      strictlyBelow FunctionClass.algebraic FunctionClass.dFinite = true ∧
      strictlyBelow FunctionClass.dFinite FunctionClass.holonomic = true := by
  native_decide

/-- Transitive comparisons in the same hierarchy. -/
theorem classification_hierarchy_transitive_checks :
    strictlyBelow FunctionClass.rational FunctionClass.dFinite = true ∧
      strictlyBelow FunctionClass.rational FunctionClass.holonomic = true ∧
      strictlyBelow FunctionClass.algebraic FunctionClass.holonomic = true := by
  native_decide

/-- The hierarchy is strict in the checked direction. -/
theorem classification_hierarchy_no_reverse_edges :
    strictlyBelow FunctionClass.algebraic FunctionClass.rational = false ∧
      strictlyBelow FunctionClass.dFinite FunctionClass.algebraic = false ∧
      strictlyBelow FunctionClass.holonomic FunctionClass.dFinite = false := by
  native_decide

end SingularityClassification
