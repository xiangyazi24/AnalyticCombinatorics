import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.AnalyticDepoissonization


/-! # Ch III -- Analytic depoissonization and Poisson transforms

Finite rational checks for the Poisson distribution, Poisson transforms,
Charlier polynomial initial cases, and birthday probabilities.
-/

/-! ## Poisson probabilities -/

/-- `n!` as a rational number. -/
def ratFactorial (n : ℕ) : ℚ :=
  (Nat.factorial n : ℚ)

/--
The rational factor in the Poisson probability
`P(X = k) = lambda^k * exp(-lambda) / k!`.

Equivalently, this is `exp(lambda) * P(X = k)`.
-/
def poissonScaledProb (lambda k : ℕ) : ℚ :=
  (lambda ^ k : ℚ) / ratFactorial k

/-- For `lambda = 1`, these entries represent `P(k) = entry / e`. -/
def poissonLambdaOneProbFactors : Fin 7 → ℚ :=
  ![1, 1, 1 / 2, 1 / 6, 1 / 24, 1 / 120, 1 / 720]

/-- `P(0)=1/e, P(1)=1/e, P(2)=1/(2e), P(3)=1/(6e), ...`. -/
theorem poissonLambdaOneProbFactors_eq :
    ∀ k : Fin 7, poissonLambdaOneProbFactors k = poissonScaledProb 1 k.val := by native_decide

/-- Multiplying `P(k)` by `e` gives `1/k!` for `lambda = 1`. -/
theorem poissonLambdaOne_scaled_by_e :
    ∀ k : Fin 7, poissonScaledProb 1 k.val = 1 / ratFactorial k.val := by native_decide

/-- Rational factors `exp(2) * P(X=k)` for `Poisson(2)`, `k = 0..6`. -/
def poissonLambdaTwoProbFactors : Fin 7 → ℚ :=
  ![1, 2, 2, 4 / 3, 2 / 3, 4 / 15, 4 / 45]

/-- The rational Poisson factors are `lambda^k/k!` for integer `lambda`. -/
theorem poissonLambdaTwoProbFactors_eq :
    ∀ k : Fin 7, poissonLambdaTwoProbFactors k = poissonScaledProb 2 k.val := by native_decide

/-! ## Partial sums for `e` -/

/-- The partial sum `sum_{k=0}^n 1/k!`. -/
def reciprocalFactorialPartialSum (n : ℕ) : ℚ :=
  ∑ k : Fin (n + 1), 1 / ratFactorial k.val

/-- The first partial sums approaching `e`. -/
def expPartialSums : Fin 7 → ℚ :=
  ![1, 2, 5 / 2, 8 / 3, 65 / 24, 163 / 60, 1957 / 720]

/-- `1, 2, 5/2, 8/3, 65/24, 163/60, 1957/720`. -/
theorem expPartialSums_eq :
    ∀ n : Fin 7, expPartialSums n = reciprocalFactorialPartialSum n.val := by native_decide

/-! ## CDF partial sums for `Poisson(2)` -/

/-- The rational factor `exp(lambda) * P(X <= n)`. -/
def poissonCDFScaled (lambda n : ℕ) : ℚ :=
  ∑ k : Fin (n + 1), poissonScaledProb lambda k.val

/-- Scaled CDF factors for `Poisson(2)`, `n = 0..6`. -/
def poissonLambdaTwoCDFScaled : Fin 7 → ℚ :=
  ![1, 3, 5, 19 / 3, 7, 109 / 15, 331 / 45]

/-- The scaled CDF table is `sum_{k=0}^n 2^k/k!`. -/
theorem poissonLambdaTwoCDFScaled_eq :
    ∀ n : Fin 7, poissonLambdaTwoCDFScaled n = poissonCDFScaled 2 n.val := by native_decide

/--
A rational CDF approximation obtained by replacing `exp(2)` with its
degree-six partial sum `331/45`.
-/
def poissonCDFRatApprox (lambda cutoff n : ℕ) : ℚ :=
  poissonCDFScaled lambda n / poissonCDFScaled lambda cutoff

/-- Rational approximations to `P(X <= n)` for `Poisson(2)`, `n = 0..5`. -/
def poissonLambdaTwoCDFApprox : Fin 6 → ℚ :=
  ![45 / 331, 135 / 331, 225 / 331, 285 / 331, 315 / 331, 327 / 331]

/-- These use the common denominator `sum_{k=0}^6 2^k/k! = 331/45`. -/
theorem poissonLambdaTwoCDFApprox_eq :
    ∀ n : Fin 6, poissonLambdaTwoCDFApprox n = poissonCDFRatApprox 2 6 n.val := by native_decide

/-! ## Poissonization -/

/-- The coefficient of `z^m` in `exp(-z) * sum_n a_n z^n/n!`. -/
def poissonizedCoeff (a : ℕ → ℚ) (m : ℕ) : ℚ :=
  ∑ r : Fin (m + 1),
    (if (m - r.val) % 2 = 0 then 1 else -1) *
      a r.val / (ratFactorial (m - r.val) * ratFactorial r.val)

/-- The sequence `a_n = 1`. -/
def seqOne (n : ℕ) : ℚ :=
  (n : ℚ) - (n : ℚ) + 1

/-- The sequence `a_n = n`. -/
def seqN (n : ℕ) : ℚ :=
  (n : ℚ)

/-- The sequence `a_n = n^2`. -/
def seqNSq (n : ℕ) : ℚ :=
  (n : ℚ) ^ 2

/-- Coefficients of the constant series `1`. -/
def coeffOne (m : ℕ) : ℚ :=
  if m = 0 then 1 else 0

/-- Coefficients of `z`. -/
def coeffZ (m : ℕ) : ℚ :=
  if m = 1 then 1 else 0

/-- Coefficients of `z^2 + z`. -/
def coeffZSqPlusZ (m : ℕ) : ℚ :=
  if m = 1 then 1 else if m = 2 then 1 else 0

/-- For `a_n = 1`, `exp(-z) * exp(z) = 1`, checked through degree six. -/
theorem poissonizedCoeff_one :
    ∀ m : Fin 7, poissonizedCoeff seqOne m.val = coeffOne m.val := by native_decide

/-- For `a_n = n`, `exp(-z) * sum n*z^n/n! = exp(-z) * z*exp(z) = z`. -/
theorem poissonizedCoeff_n :
    ∀ m : Fin 7, poissonizedCoeff seqN m.val = coeffZ m.val := by native_decide

/-- For `a_n = n^2`, the Poisson transform is `z^2 + z`, checked through degree six. -/
theorem poissonizedCoeff_n_sq :
    ∀ m : Fin 7, poissonizedCoeff seqNSq m.val = coeffZSqPlusZ m.val := by native_decide

/-! ## Charlier polynomials -/

/-- Initial Charlier polynomials: `C_0(x;a)=1`, `C_1(x;a)=x-a`. -/
def charlierC (n : ℕ) (x a : ℤ) : ℤ :=
  if n = 0 then 1 else if n = 1 then x - a else 0

/-- Sample `x` values for finite verification. -/
def charlierSampleX : Fin 5 → ℤ :=
  ![-2, -1, 0, 1, 4]

/-- Sample `a` values for finite verification. -/
def charlierSampleA : Fin 4 → ℤ :=
  ![-1, 0, 2, 5]

/-- `C_0(x;a) = 1` on the sample grid. -/
theorem charlierC_zero :
    ∀ x : Fin 5, ∀ a : Fin 4,
      charlierC 0 (charlierSampleX x) (charlierSampleA a) = 1 := by native_decide

/-- `C_1(x;a) = x-a` on the sample grid. -/
theorem charlierC_one :
    ∀ x : Fin 5, ∀ a : Fin 4,
      charlierC 1 (charlierSampleX x) (charlierSampleA a) =
        charlierSampleX x - charlierSampleA a := by native_decide

/-! ## Birthday asymptotics -/

/-- `d! / (d^n * (d-n)!)`, the probability of no collision. -/
def birthdayNoCollision (d n : ℕ) : ℚ :=
  (Nat.factorial d : ℚ) / ((d ^ n : ℚ) * ratFactorial (d - n))

/-- No-collision probabilities for `d = 365`, `n = 1..5`. -/
def birthday365NoCollision : Fin 5 → ℚ :=
  ![1, 364 / 365, 132132 / 133225, 47831784 / 48627125,
    17267274024 / 17748900625]

/-- Verify `Q(n,d) = d!/(d^n * (d-n)!)` for `d = 365`, `n = 1..5`. -/
theorem birthday365NoCollision_eq :
    ∀ n : Fin 5, birthday365NoCollision n = birthdayNoCollision 365 (n.val + 1) := by native_decide



structure AnalyticDepoissonizationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticDepoissonizationBudgetCertificate.controlled
    (c : AnalyticDepoissonizationBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticDepoissonizationBudgetCertificate.budgetControlled
    (c : AnalyticDepoissonizationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticDepoissonizationBudgetCertificate.Ready
    (c : AnalyticDepoissonizationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticDepoissonizationBudgetCertificate.size
    (c : AnalyticDepoissonizationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticDepoissonization_budgetCertificate_le_size
    (c : AnalyticDepoissonizationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticDepoissonizationBudgetCertificate :
    AnalyticDepoissonizationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAnalyticDepoissonizationBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticDepoissonizationBudgetCertificate.controlled,
      sampleAnalyticDepoissonizationBudgetCertificate]
  · norm_num [AnalyticDepoissonizationBudgetCertificate.budgetControlled,
      sampleAnalyticDepoissonizationBudgetCertificate]

example :
    sampleAnalyticDepoissonizationBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticDepoissonizationBudgetCertificate.size := by
  apply analyticDepoissonization_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticDepoissonizationBudgetCertificate.controlled,
      sampleAnalyticDepoissonizationBudgetCertificate]
  · norm_num [AnalyticDepoissonizationBudgetCertificate.budgetControlled,
      sampleAnalyticDepoissonizationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAnalyticDepoissonizationBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticDepoissonizationBudgetCertificate.controlled,
      sampleAnalyticDepoissonizationBudgetCertificate]
  · norm_num [AnalyticDepoissonizationBudgetCertificate.budgetControlled,
      sampleAnalyticDepoissonizationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticDepoissonizationBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticDepoissonizationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AnalyticDepoissonizationBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticDepoissonizationBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticDepoissonizationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.AnalyticDepoissonization
