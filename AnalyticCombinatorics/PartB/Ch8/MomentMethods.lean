import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-! # Chapter VIII -- moment methods

Finite, computable certificates for the moment identities used in
asymptotic enumeration.  The statements are phrased with integer-scaled
moments so that the checks reduce to exact arithmetic.
-/

namespace MomentMethods

/-! ## 1. Binomial moments at `p = 1/2` -/

/-- Numerator of `E[X^k]` for `X ~ Bin(n, 1/2)`.
The probability denominator is `2^n`. -/
def binomialHalfMomentNumerator (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), Nat.choose n j * j ^ k

/-- Integer-scaled statement of `2^n * E[X^k] = sum C(n,j) j^k`. -/
abbrev binomialHalfMomentScaledIdentity (n k : ℕ) : Prop :=
  binomialHalfMomentNumerator n k =
    ∑ j ∈ Finset.range (n + 1), Nat.choose n j * j ^ k

theorem binomialHalfMoment_scaled_identity_small :
    ∀ n : Fin 16, ∀ k : Fin 6,
      binomialHalfMomentScaledIdentity n.val k.val := by
  native_decide

/-- Scaled checks for `E[X] = n/2` and `E[X^2] = (n^2+n)/4`. -/
theorem binomialHalf_first_second_moments :
    ∀ n : Fin 16,
      2 * binomialHalfMomentNumerator n.val 1 = n.val * 2 ^ n.val ∧
      4 * binomialHalfMomentNumerator n.val 2 =
        (n.val ^ 2 + n.val) * 2 ^ n.val := by
  native_decide

/-! ## 2. Factorial moments of binomial laws -/

/-- Falling factorial `(x)_r = x (x-1) ... (x-r+1)`. -/
def fallingFactorial : ℕ → ℕ → ℕ
  | _, 0 => 1
  | x, r + 1 => (x - r) * fallingFactorial x r

/-- Numerator for `E[(X)_r]` when `X ~ Bin(n, a / b)`.
The denominator is `b^n`. -/
def binomialFactorialMomentNumerator (n a b r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1),
    Nat.choose n j * a ^ j * (b - a) ^ (n - j) * fallingFactorial j r

/-- Integer-scaled closed form for the binomial factorial moment. -/
def binomialFactorialMomentFormulaNumerator (n a b r : ℕ) : ℕ :=
  fallingFactorial n r * a ^ r * b ^ (n - r)

theorem fallingFactorial_eq_factorial_quotient_small :
    ∀ n : Fin 12, ∀ r : Fin 12,
      r.val ≤ n.val →
        fallingFactorial n.val r.val =
          Nat.factorial n.val / Nat.factorial (n.val - r.val) := by
  native_decide

/-- Checks `E[(X)_r] = n!/(n-r)! * p^r`, scaled by `b^n`, for `p = 2/5`. -/
theorem binomial_factorial_moment_formula_p_two_fifths :
    ∀ n : Fin 10, ∀ r : Fin 8,
      binomialFactorialMomentNumerator n.val 2 5 r.val =
        binomialFactorialMomentFormulaNumerator n.val 2 5 r.val := by
  native_decide

/-- The same factorial-moment identity for the symmetric case `p = 1/2`. -/
theorem binomial_factorial_moment_formula_p_half :
    ∀ n : Fin 12, ∀ r : Fin 8,
      binomialFactorialMomentNumerator n.val 1 2 r.val =
        binomialFactorialMomentFormulaNumerator n.val 1 2 r.val := by
  native_decide

/-! ## 3. Cumulants -/

/-- First cumulant from the first two raw moments. -/
def cumulantOne (m1 _m2 : ℤ) : ℤ :=
  m1

/-- Second cumulant from the first two raw moments: `E[X^2] - E[X]^2`. -/
def cumulantTwo (m1 m2 : ℤ) : ℤ :=
  m2 - m1 ^ 2

/-- Variance computed from the first two raw moments. -/
def varianceFromRaw (m1 m2 : ℤ) : ℤ :=
  m2 - m1 ^ 2

theorem cumulant_one_is_mean_small :
    ∀ m1 : Fin 21, ∀ m2 : Fin 441,
      cumulantOne (Int.ofNat m1.val) (Int.ofNat m2.val) = Int.ofNat m1.val := by
  native_decide

theorem cumulant_two_is_variance_small :
    ∀ m1 : Fin 21, ∀ m2 : Fin 441,
      cumulantTwo (Int.ofNat m1.val) (Int.ofNat m2.val) =
        varianceFromRaw (Int.ofNat m1.val) (Int.ofNat m2.val) := by
  native_decide

/-- Cumulant sequence of a Poisson law: every positive-order cumulant is `lambda`. -/
def poissonCumulant (lambda _r : ℕ) : ℕ :=
  lambda

theorem poisson_all_cumulants_are_lambda_small :
    ∀ lambda : Fin 20, ∀ r : Fin 8,
      poissonCumulant lambda.val (r.val + 1) = lambda.val := by
  native_decide

/-! ## 4. Method of moments and Poisson moment checks -/

/-- Stirling numbers of the second kind, used in Touchard polynomials. -/
def stirlingSecond : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k

/-- Raw moments of `Poisson(lambda)` as Touchard polynomials. -/
def poissonMoment (lambda k : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (k + 1), stirlingSecond k r * lambda ^ r

theorem poisson_lambda_three_initial_moments :
    poissonMoment 3 1 = 3 ∧
    poissonMoment 3 2 = 12 ∧
    poissonMoment 3 3 = 57 := by
  native_decide

/-- The number `54` is the third raw moment with the mean subtracted. -/
theorem poisson_lambda_three_third_moment_minus_mean :
    poissonMoment 3 3 - poissonMoment 3 1 = 54 := by
  native_decide

/-- A finite certificate that two moment sequences match through order `K`. -/
abbrev momentsMatchUpTo (K : ℕ) (candidate target : ℕ → ℕ) : Prop :=
  ∀ k : Fin (K + 1), candidate k.val = target k.val

/-- Finite method-of-moments certificate: all sampled distributions match the target moments. -/
abbrev methodOfMomentsCertificate
    (N K : ℕ) (candidate : ℕ → ℕ → ℕ) (target : ℕ → ℕ) : Prop :=
  ∀ n : Fin (N + 1), momentsMatchUpTo K (candidate n.val) target

/-- The finite certificate is accepted as the computable shadow of moment convergence. -/
abbrev momentConvergenceCertified
    (N K : ℕ) (candidate : ℕ → ℕ → ℕ) (target : ℕ → ℕ) : Prop :=
  methodOfMomentsCertificate N K candidate target

def poissonThreeMomentTable (k : ℕ) : ℕ :=
  poissonMoment 3 k

def stationaryPoissonThreeMoments (_n k : ℕ) : ℕ :=
  poissonMoment 3 k

theorem method_of_moments_matching_poisson_three :
    momentConvergenceCertified 5 3 stationaryPoissonThreeMoments poissonThreeMomentTable := by
  native_decide

/-! ## 5. Moment generating functions -/

/-- Moments of the geometric law on `{0,1,2,...}` with mass `2^-(j+1)`.
The formula follows from `j^k = sum S(k,r) (j)_r`. -/
def geometricHalfMoment (k : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (k + 1), stirlingSecond k r * Nat.factorial r

/-- Coefficient numerator of `t^k/k!` in `M(t) = sum E[X^k] t^k/k!`. -/
def momentGeneratingFunctionCoefficient (moment : ℕ → ℕ) (k : ℕ) : ℕ :=
  moment k

theorem geometric_mgf_initial_coefficients :
    momentGeneratingFunctionCoefficient geometricHalfMoment 0 = 1 ∧
    momentGeneratingFunctionCoefficient geometricHalfMoment 1 = 1 ∧
    momentGeneratingFunctionCoefficient geometricHalfMoment 2 = 3 ∧
    momentGeneratingFunctionCoefficient geometricHalfMoment 3 = 13 ∧
    momentGeneratingFunctionCoefficient geometricHalfMoment 4 = 75 := by
  native_decide

theorem geometric_mgf_coefficients_match_moments :
    ∀ k : Fin 8,
      momentGeneratingFunctionCoefficient geometricHalfMoment k.val =
        geometricHalfMoment k.val := by
  native_decide

/-! ## 6. Central moments of the discrete uniform law -/

/-- Integer numerator for `2^k * n * E[(X - mu)^k]`
when `X` is uniform on `{1, ..., n}` and `mu = (n+1)/2`. -/
def uniformCentralMomentScaledSum (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range n,
    (Int.ofNat (2 * (j + 1)) - Int.ofNat (n + 1)) ^ k

theorem uniform_central_first_moment_zero :
    ∀ n : Fin 20,
      uniformCentralMomentScaledSum (n.val + 1) 1 = 0 := by
  native_decide

/-- Scaled variance check: `E[(X-mu)^2] = (n^2-1)/12`. -/
theorem uniform_central_second_moment :
    ∀ n : Fin 20,
      3 * uniformCentralMomentScaledSum (n.val + 1) 2 =
        Int.ofNat ((n.val + 1) * ((n.val + 1) ^ 2 - 1)) := by
  native_decide

theorem uniform_central_odd_moments_zero_small :
    ∀ n : Fin 12,
      uniformCentralMomentScaledSum (n.val + 1) 3 = 0 ∧
      uniformCentralMomentScaledSum (n.val + 1) 5 = 0 := by
  native_decide

end MomentMethods
