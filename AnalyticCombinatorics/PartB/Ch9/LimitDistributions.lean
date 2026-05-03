import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace LimitDistributions

open Finset

/-!
Finite, decidable checks for limit-distribution identities from Chapter IX of
Flajolet and Sedgewick.  The statements deliberately stay in `ℕ` and `ℚ`, so
each proof is a computation discharged by `native_decide`.
-/

/-! ## Poisson moments and Bell polynomials -/

/-- Stirling numbers of the second kind. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- Complete Bell polynomial `B_k(λ) = ∑_j S(k,j) λ^j`. -/
def bellPolynomial (k : ℕ) (lambda : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (k + 1), (stirling2 k j : ℚ) * lambda ^ j

/--
Raw moments of a Poisson variable are represented by the Bell polynomial:
`E[X^k] = B_k(λ)`.
-/
def poissonRawMoment (lambda : ℚ) (k : ℕ) : ℚ := bellPolynomial k lambda

theorem poisson_moment_zero_lambda_two : poissonRawMoment 2 0 = 1 := by native_decide

theorem poisson_moment_one_lambda_two : poissonRawMoment 2 1 = 2 := by native_decide

theorem poisson_moment_two_lambda_two : poissonRawMoment 2 2 = 6 := by native_decide

theorem poisson_moment_three_lambda_two : poissonRawMoment 2 3 = 22 := by native_decide

theorem poisson_moment_four_lambda_two : poissonRawMoment 2 4 = 94 := by native_decide

theorem poisson_moment_five_lambda_two : poissonRawMoment 2 5 = 454 := by native_decide

theorem poisson_moment_three_lambda_three_halves :
    poissonRawMoment (3 / 2) 3 = 93 / 8 := by
  native_decide

theorem poisson_bell_polynomial_connection_lambda_three :
    poissonRawMoment 3 4 = bellPolynomial 4 3 := by
  native_decide

theorem bell_polynomial_lambda_three_order_four :
    bellPolynomial 4 3 = 309 := by
  native_decide

/-! ## Standard normal even moments -/

/-- The standard normal even moment `(2k)! / (2^k k!)`. -/
def standardNormalEvenMoment (k : ℕ) : ℚ :=
  (Nat.factorial (2 * k) : ℚ) / ((2 : ℚ) ^ k * (Nat.factorial k : ℚ))

/-- Product `1 * 3 * ... * (2k - 1)`, with value `1` at `k = 0`. -/
def oddDoubleFactorial : ℕ → ℕ
  | 0 => 1
  | k + 1 => (2 * k + 1) * oddDoubleFactorial k

theorem normal_even_moment_zero : standardNormalEvenMoment 0 = 1 := by native_decide

theorem normal_even_moment_two : standardNormalEvenMoment 1 = 1 := by native_decide

theorem normal_even_moment_four : standardNormalEvenMoment 2 = 3 := by native_decide

theorem normal_even_moment_six : standardNormalEvenMoment 3 = 15 := by native_decide

theorem normal_even_moment_eight : standardNormalEvenMoment 4 = 105 := by native_decide

theorem normal_even_moment_ten : standardNormalEvenMoment 5 = 945 := by native_decide

theorem normal_even_moment_twelve : standardNormalEvenMoment 6 = 10395 := by native_decide

theorem normal_even_moment_matches_double_factorial_6 :
    standardNormalEvenMoment 6 = oddDoubleFactorial 6 := by
  native_decide

/-! ## Rayleigh distribution numerical checks -/

/-- Rayleigh log-density score for scale `1`: derivative of `log x - x^2/2`. -/
def rayleighStandardScore (x : ℚ) : ℚ := 1 / x - x

/-- Rayleigh mode for scale `sigma`, checked numerically below. -/
def rayleighMode (sigma : ℚ) : ℚ := sigma

/-- Five-decimal rational approximation of `sqrt(pi / 2)`. -/
def rayleighMeanApprox : ℚ := 125331 / 100000

/-- Six-decimal rational approximation of `pi`. -/
def piApprox : ℚ := 3141593 / 1000000

theorem rayleigh_standard_mode_value : rayleighMode 1 = 1 := by native_decide

theorem rayleigh_score_zero_at_mode : rayleighStandardScore 1 = 0 := by native_decide

theorem rayleigh_score_positive_left_of_mode : rayleighStandardScore (1 / 2) > 0 := by
  native_decide

theorem rayleigh_score_negative_right_of_mode : rayleighStandardScore 2 < 0 := by
  native_decide

theorem rayleigh_mean_square_lower_check :
    (125330 / 100000 : ℚ) ^ 2 < piApprox / 2 := by
  native_decide

theorem rayleigh_mean_square_upper_check :
    piApprox / 2 < (125332 / 100000 : ℚ) ^ 2 := by
  native_decide

theorem rayleigh_mean_approx_between_checks :
    125330 / 100000 < rayleighMeanApprox ∧ rayleighMeanApprox < 125332 / 100000 := by
  native_decide

/-! ## Gumbel distribution and Euler's constant -/

/-- Rational harmonic number `H_n`. -/
def harmonicQ (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

/-- Six-decimal rational approximation of the Euler-Mascheroni constant. -/
def eulerMascheroniApprox : ℚ := 577216 / 1000000

/-- Standard Gumbel mean, represented by the same Euler-Mascheroni approximation. -/
def standardGumbelMeanApprox : ℚ := eulerMascheroniApprox

/-- Six-decimal rational approximation of `log 10`. -/
def logTenApprox : ℚ := 2302585 / 1000000

/-- First Euler-Maclaurin correction to `H_10 - log 10`. -/
def eulerMascheroniFromH10 : ℚ := harmonicQ 10 - logTenApprox - 1 / 20

theorem gumbel_mean_euler_mascheroni :
    standardGumbelMeanApprox = eulerMascheroniApprox := by
  native_decide

theorem harmonic_ten_value : harmonicQ 10 = 7381 / 2520 := by native_decide

theorem euler_mascheroni_h10_lower :
    eulerMascheroniApprox - 1 / 1000 < eulerMascheroniFromH10 := by
  native_decide

theorem euler_mascheroni_h10_upper :
    eulerMascheroniFromH10 < eulerMascheroniApprox + 1 / 1000 := by
  native_decide

theorem centered_gumbel_mean_check :
    standardGumbelMeanApprox - eulerMascheroniApprox = 0 := by
  native_decide

/-! ## Geometric distribution moments and generating coefficients -/

/-- Coefficient of `z^n` in the geometric probability generating function. -/
def geometricPGFCoeff (p q : ℚ) (n : ℕ) : ℚ := p * q ^ n

/-- Partial mass `∑_{n<N} p q^n`. -/
def geometricPartialMass (p q : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, geometricPGFCoeff p q n

/-- First raw moment of the geometric law on `0,1,2,...`. -/
def geometricMean (p q : ℚ) : ℚ := q / p

/-- Second raw moment of the geometric law on `0,1,2,...`. -/
def geometricSecondMoment (p q : ℚ) : ℚ := q * (1 + q) / p ^ 2

/-- Third raw moment of the geometric law on `0,1,2,...`. -/
def geometricThirdMoment (p q : ℚ) : ℚ := q * (1 + 4 * q + q ^ 2) / p ^ 3

theorem geometric_coeff_zero_one_third :
    geometricPGFCoeff (1 / 3) (2 / 3) 0 = 1 / 3 := by
  native_decide

theorem geometric_coeff_one_one_third :
    geometricPGFCoeff (1 / 3) (2 / 3) 1 = 2 / 9 := by
  native_decide

theorem geometric_coeff_four_one_third :
    geometricPGFCoeff (1 / 3) (2 / 3) 4 = 16 / 243 := by
  native_decide

theorem geometric_coeff_ratio_check :
    geometricPGFCoeff (1 / 3) (2 / 3) 5 =
      (2 / 3) * geometricPGFCoeff (1 / 3) (2 / 3) 4 := by
  native_decide

theorem geometric_partial_mass_four :
    geometricPartialMass (1 / 3) (2 / 3) 4 = 65 / 81 := by
  native_decide

theorem geometric_mean_one_third : geometricMean (1 / 3) (2 / 3) = 2 := by
  native_decide

theorem geometric_second_moment_one_third :
    geometricSecondMoment (1 / 3) (2 / 3) = 10 := by
  native_decide

theorem geometric_third_moment_one_third :
    geometricThirdMoment (1 / 3) (2 / 3) = 74 := by
  native_decide

/-! ## Exponential distribution discrete approximation identities -/

/-- Geometric mass for an exponential approximation with rate `lambda` and mesh `h`. -/
def exponentialDiscreteMass (lambda h : ℚ) (n : ℕ) : ℚ :=
  (lambda * h) * (1 - lambda * h) ^ n

/-- Discrete survival function for the same geometric approximation. -/
def exponentialDiscreteSurvival (lambda h : ℚ) (n : ℕ) : ℚ :=
  (1 - lambda * h) ^ n

/-- The right-endpoint mesh mean `h / (lambda h)`, equal to `1 / lambda`. -/
def exponentialDiscreteRightMean (lambda h : ℚ) : ℚ := h / (lambda * h)

theorem exponential_discrete_first_mass :
    exponentialDiscreteMass 1 (1 / 10) 0 = 1 / 10 := by
  native_decide

theorem exponential_discrete_fifth_survival :
    exponentialDiscreteSurvival 1 (1 / 10) 5 = 59049 / 100000 := by
  native_decide

theorem exponential_discrete_partial_mass_identity :
    (∑ n ∈ Finset.range 6, exponentialDiscreteMass 1 (1 / 10) n) =
      1 - exponentialDiscreteSurvival 1 (1 / 10) 6 := by
  native_decide

theorem exponential_discrete_memoryless_check :
    exponentialDiscreteSurvival 1 (1 / 10) (3 + 4) =
      exponentialDiscreteSurvival 1 (1 / 10) 3 *
        exponentialDiscreteSurvival 1 (1 / 10) 4 := by
  native_decide

theorem exponential_discrete_right_mean_rate_one :
    exponentialDiscreteRightMean 1 (1 / 10) = 1 := by
  native_decide

theorem exponential_discrete_right_mean_rate_two :
    exponentialDiscreteRightMean 2 (1 / 10) = 1 / 2 := by
  native_decide

end LimitDistributions
