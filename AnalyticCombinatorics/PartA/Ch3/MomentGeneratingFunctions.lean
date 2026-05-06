import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.MomentGeneratingFunctions

/-! # Ch III — Moment and probability generating functions

Finite rational checks for the probability distributions that occur in
combinatorial-parameter analysis: binomial, Poisson, geometric waiting times,
negative binomial laws, and hypergeometric laws.
-/


/-! ## Finite probability and moment generating functions -/

/-- Probability generating function of a finite distribution. -/
def finitePGF {n : ℕ} (mass : Fin n → ℚ) (z : ℚ) : ℚ :=
  ∑ k : Fin n, mass k * z ^ k.val

/-- Moment generating function after substituting the rational value `y = exp t`. -/
def finiteMGFSubst {n : ℕ} (mass : Fin n → ℚ) (y : ℚ) : ℚ :=
  ∑ k : Fin n, mass k * y ^ k.val

/-! ## Binomial distribution -/

/-- The binomial mass `P(X = k) = C(n,k) p^k (1-p)^(n-k)`. -/
def binomialPMF (n k : ℕ) (p : ℚ) : ℚ :=
  (Nat.choose n k : ℚ) * p ^ k * (1 - p) ^ (n - k)

/-- The binomial probability generating function, evaluated at a rational point. -/
def binomialPGF (n : ℕ) (p z : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), binomialPMF n k p * z ^ k

/-- Raw moment `E[X^m]` for a finite binomial law. -/
def binomialRawMoment (n m : ℕ) (p : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), ((k ^ m : ℕ) : ℚ) * binomialPMF n k p

/-- Mean of a binomial law. -/
def binomialMean (n : ℕ) (p : ℚ) : ℚ :=
  binomialRawMoment n 1 p

/-- Second raw moment of a binomial law. -/
def binomialSecondMoment (n : ℕ) (p : ℚ) : ℚ :=
  binomialRawMoment n 2 p

/-- Variance of a binomial law. -/
def binomialVariance (n : ℕ) (p : ℚ) : ℚ :=
  binomialSecondMoment n p - (binomialMean n p) ^ 2

/-- Checks of `E[X] = np` and `Var(X) = np(1-p)` at rational parameters. -/
theorem binomial_mean_variance_rational_checks :
    binomialMean 4 ((1 : ℚ) / 3) = (4 : ℚ) * ((1 : ℚ) / 3) ∧
      binomialVariance 4 ((1 : ℚ) / 3) =
        (4 : ℚ) * ((1 : ℚ) / 3) * (1 - (1 : ℚ) / 3) ∧
      binomialMean 6 ((2 : ℚ) / 5) = (6 : ℚ) * ((2 : ℚ) / 5) ∧
      binomialVariance 6 ((2 : ℚ) / 5) =
        (6 : ℚ) * ((2 : ℚ) / 5) * (1 - (2 : ℚ) / 5) := by
  native_decide

/-- For `Bin(5,1/2)`, the mean is `5/2`, the second raw moment is `15/2`,
and the variance is `5/4`. -/
theorem binomial_five_half_moments :
    binomialMean 5 ((1 : ℚ) / 2) = (5 : ℚ) / 2 ∧
      binomialSecondMoment 5 ((1 : ℚ) / 2) = (15 : ℚ) / 2 ∧
      binomialVariance 5 ((1 : ℚ) / 2) = (5 : ℚ) / 4 := by
  native_decide

/-- The value `35/4` is not the second raw moment of `Bin(5,1/2)`. -/
theorem binomial_five_half_second_moment_not_thirty_five_fourths :
    binomialSecondMoment 5 ((1 : ℚ) / 2) ≠ (35 : ℚ) / 4 := by
  native_decide

/-- Small checks of the binomial probability generating function. -/
theorem binomial_pgf_rational_checks :
    binomialPGF 3 ((1 : ℚ) / 2) 0 = (1 : ℚ) / 8 ∧
      binomialPGF 3 ((1 : ℚ) / 2) 1 = 1 ∧
      binomialPGF 3 ((1 : ℚ) / 2) 2 = (27 : ℚ) / 8 := by
  native_decide

/-! ## Factorial moments -/

/-- Falling factorial `(x)_k = x (x-1) ... (x-k+1)`. -/
def fallingFactorial (x k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (x - i)

/-- Binomial factorial moment `E[(X)_k]`. -/
def binomialFactorialMoment (n k : ℕ) (p : ℚ) : ℚ :=
  ∑ x ∈ Finset.range (n + 1), (fallingFactorial x k : ℚ) * binomialPMF n x p

/-- Formula side `(n)_k p^k = n!/(n-k)! p^k`, used when `k ≤ n`. -/
def binomialFactorialMomentFormula (n k : ℕ) (p : ℚ) : ℚ :=
  (fallingFactorial n k : ℚ) * p ^ k

/-- Checks of `(n)_k = n!/(n-k)!`. -/
theorem falling_factorial_factorial_ratio_checks :
    fallingFactorial 5 0 = Nat.factorial 5 / Nat.factorial (5 - 0) ∧
      fallingFactorial 5 1 = Nat.factorial 5 / Nat.factorial (5 - 1) ∧
      fallingFactorial 5 2 = Nat.factorial 5 / Nat.factorial (5 - 2) ∧
      fallingFactorial 5 3 = Nat.factorial 5 / Nat.factorial (5 - 3) ∧
      fallingFactorial 5 5 = Nat.factorial 5 / Nat.factorial (5 - 5) := by
  native_decide

/-- Binomial factorial moments agree with `(n)_k p^k` in small rational cases. -/
theorem binomial_factorial_moment_checks :
    binomialFactorialMoment 5 0 ((1 : ℚ) / 2) =
        binomialFactorialMomentFormula 5 0 ((1 : ℚ) / 2) ∧
      binomialFactorialMoment 5 1 ((1 : ℚ) / 2) =
        binomialFactorialMomentFormula 5 1 ((1 : ℚ) / 2) ∧
      binomialFactorialMoment 5 2 ((1 : ℚ) / 2) =
        binomialFactorialMomentFormula 5 2 ((1 : ℚ) / 2) ∧
      binomialFactorialMoment 5 3 ((1 : ℚ) / 2) =
        binomialFactorialMomentFormula 5 3 ((1 : ℚ) / 2) ∧
      binomialFactorialMoment 6 4 ((1 : ℚ) / 3) =
        binomialFactorialMomentFormula 6 4 ((1 : ℚ) / 3) := by
  native_decide

/-- Explicit values for factorial moments of `Bin(5,1/2)`. -/
theorem binomial_five_half_factorial_moment_values :
    binomialFactorialMoment 5 1 ((1 : ℚ) / 2) = (5 : ℚ) / 2 ∧
      binomialFactorialMoment 5 2 ((1 : ℚ) / 2) = 5 ∧
      binomialFactorialMoment 5 3 ((1 : ℚ) / 2) = (15 : ℚ) / 2 := by
  native_decide

/-! ## Poisson moments -/

/-- The first raw moment of a Poisson law with parameter `λ`. -/
def poissonFirstMoment (lambda : ℚ) : ℚ :=
  lambda

/-- The second raw moment of a Poisson law with parameter `λ`. -/
def poissonSecondMoment (lambda : ℚ) : ℚ :=
  lambda ^ 2 + lambda

/-- The third raw moment of a Poisson law with parameter `λ`. -/
def poissonThirdMoment (lambda : ℚ) : ℚ :=
  lambda ^ 3 + 3 * lambda ^ 2 + lambda

/-- Rational checks of `E[X] = λ`, `E[X²] = λ² + λ`, and
`E[X³] = λ³ + 3λ² + λ`. -/
theorem poisson_moment_rational_checks :
    poissonFirstMoment ((3 : ℚ) / 2) = (3 : ℚ) / 2 ∧
      poissonSecondMoment ((3 : ℚ) / 2) = (15 : ℚ) / 4 ∧
      poissonThirdMoment ((3 : ℚ) / 2) = (93 : ℚ) / 8 ∧
      poissonFirstMoment 2 = 2 ∧
      poissonSecondMoment 2 = 6 ∧
      poissonThirdMoment 2 = 22 := by
  native_decide

/-! ## Bernoulli waiting times and partial sums -/

/-- Probability that the first success occurs at trial `k`. -/
def firstSuccessPMF (k : ℕ) (p : ℚ) : ℚ :=
  (1 - p) ^ (k - 1) * p

/-- Partial sum `Σ_{k=1}^m (1-p)^(k-1)p`. -/
def firstSuccessPartialSum (m : ℕ) (p : ℚ) : ℚ :=
  ∑ i ∈ Finset.range m, firstSuccessPMF (i + 1) p

/-- Formula and partial-sum checks for first success in Bernoulli trials. -/
theorem first_success_rational_checks :
    firstSuccessPMF 1 ((1 : ℚ) / 3) = (1 : ℚ) / 3 ∧
      firstSuccessPMF 2 ((1 : ℚ) / 3) = (2 : ℚ) / 9 ∧
      firstSuccessPMF 4 ((1 : ℚ) / 3) = (8 : ℚ) / 81 ∧
      firstSuccessPartialSum 1 ((1 : ℚ) / 2) = (1 : ℚ) / 2 ∧
      firstSuccessPartialSum 2 ((1 : ℚ) / 2) = (3 : ℚ) / 4 ∧
      firstSuccessPartialSum 3 ((1 : ℚ) / 2) = (7 : ℚ) / 8 ∧
      firstSuccessPartialSum 4 ((1 : ℚ) / 2) = (15 : ℚ) / 16 ∧
      firstSuccessPartialSum 4 ((1 : ℚ) / 3) =
        1 - (1 - (1 : ℚ) / 3) ^ 4 := by
  native_decide

/-! ## Negative binomial distribution -/

/-- Probability that the `r`-th success occurs at trial `k`. -/
def negativeBinomialPMF (r k : ℕ) (p : ℚ) : ℚ :=
  (Nat.choose (k - 1) (r - 1) : ℚ) * p ^ r * (1 - p) ^ (k - r)

/-- Numerators over denominator `16` for `r = 2`, `p = 1/2`, and `k = 2,3,4,5`. -/
def negativeBinomialR2HalfNumerators : Fin 4 → ℕ :=
  ![4, 4, 3, 2]

/-- Values for `P(the second success occurs at k)` when `p = 1/2`. -/
theorem negative_binomial_r_two_half_values :
    negativeBinomialPMF 2 2 ((1 : ℚ) / 2) = (1 : ℚ) / 4 ∧
      negativeBinomialPMF 2 3 ((1 : ℚ) / 2) = (1 : ℚ) / 4 ∧
      negativeBinomialPMF 2 4 ((1 : ℚ) / 2) = (3 : ℚ) / 16 ∧
      negativeBinomialPMF 2 5 ((1 : ℚ) / 2) = (1 : ℚ) / 8 := by
  native_decide

/-- The table records the same four probabilities with common denominator `16`. -/
theorem negative_binomial_r_two_half_table :
    ∀ i : Fin 4,
      (negativeBinomialR2HalfNumerators i : ℚ) / 16 =
        negativeBinomialPMF 2 (i.val + 2) ((1 : ℚ) / 2) := by
  native_decide

/-! ## Hypergeometric distribution -/

/-- Hypergeometric numerator `C(K,k) C(N-K,n-k)`. -/
def hypergeometricNumerator (N K n k : ℕ) : ℕ :=
  Nat.choose K k * Nat.choose (N - K) (n - k)

/-- Hypergeometric mass `P(X=k) = C(K,k) C(N-K,n-k) / C(N,n)`. -/
def hypergeometricPMF (N K n k : ℕ) : ℚ :=
  (hypergeometricNumerator N K n k : ℚ) / (Nat.choose N n : ℚ)

/-- Hypergeometric numerators for `N = 10`, `K = 4`, `n = 3`, and `k = 0,1,2,3`. -/
def hypergeometricTenFourThreeNumerators : Fin 4 → ℕ :=
  ![20, 60, 36, 4]

/-- Numerator checks for `N = 10`, `K = 4`, `n = 3`. -/
theorem hypergeometric_ten_four_three_numerators :
    ∀ k : Fin 4,
      hypergeometricTenFourThreeNumerators k =
        hypergeometricNumerator 10 4 3 k.val := by
  native_decide

/-- Probability checks for `N = 10`, `K = 4`, `n = 3`. -/
theorem hypergeometric_ten_four_three_probabilities :
    hypergeometricPMF 10 4 3 0 = (1 : ℚ) / 6 ∧
      hypergeometricPMF 10 4 3 1 = (1 : ℚ) / 2 ∧
      hypergeometricPMF 10 4 3 2 = (3 : ℚ) / 10 ∧
      hypergeometricPMF 10 4 3 3 = (1 : ℚ) / 30 ∧
      (∑ k : Fin 4, hypergeometricTenFourThreeNumerators k) = Nat.choose 10 3 := by
  native_decide

/-- Another small hypergeometric instance: `N = 6`, `K = 2`, `n = 2`. -/
theorem hypergeometric_six_two_two_probabilities :
    hypergeometricPMF 6 2 2 0 = (2 : ℚ) / 5 ∧
      hypergeometricPMF 6 2 2 1 = (8 : ℚ) / 15 ∧
      hypergeometricPMF 6 2 2 2 = (1 : ℚ) / 15 := by
  native_decide



structure MomentGeneratingFunctionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MomentGeneratingFunctionsBudgetCertificate.controlled
    (c : MomentGeneratingFunctionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MomentGeneratingFunctionsBudgetCertificate.budgetControlled
    (c : MomentGeneratingFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MomentGeneratingFunctionsBudgetCertificate.Ready
    (c : MomentGeneratingFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MomentGeneratingFunctionsBudgetCertificate.size
    (c : MomentGeneratingFunctionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem momentGeneratingFunctions_budgetCertificate_le_size
    (c : MomentGeneratingFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMomentGeneratingFunctionsBudgetCertificate :
    MomentGeneratingFunctionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleMomentGeneratingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [MomentGeneratingFunctionsBudgetCertificate.controlled,
      sampleMomentGeneratingFunctionsBudgetCertificate]
  · norm_num [MomentGeneratingFunctionsBudgetCertificate.budgetControlled,
      sampleMomentGeneratingFunctionsBudgetCertificate]

example :
    sampleMomentGeneratingFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleMomentGeneratingFunctionsBudgetCertificate.size := by
  apply momentGeneratingFunctions_budgetCertificate_le_size
  constructor
  · norm_num [MomentGeneratingFunctionsBudgetCertificate.controlled,
      sampleMomentGeneratingFunctionsBudgetCertificate]
  · norm_num [MomentGeneratingFunctionsBudgetCertificate.budgetControlled,
      sampleMomentGeneratingFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMomentGeneratingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [MomentGeneratingFunctionsBudgetCertificate.controlled,
      sampleMomentGeneratingFunctionsBudgetCertificate]
  · norm_num [MomentGeneratingFunctionsBudgetCertificate.budgetControlled,
      sampleMomentGeneratingFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMomentGeneratingFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleMomentGeneratingFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MomentGeneratingFunctionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMomentGeneratingFunctionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMomentGeneratingFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.MomentGeneratingFunctions
