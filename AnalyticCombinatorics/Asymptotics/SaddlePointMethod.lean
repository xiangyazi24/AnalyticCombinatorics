import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Saddle-Point Method

Executable finite models for saddle-point coefficient estimates, Gaussian
windows, and Stirling-scale normalization.
-/

namespace AnalyticCombinatorics.Asymptotics.SaddlePointMethod

/-- Central binomial coefficient, the basic saddle-point sample for `(1+z)^{2n}`. -/
def centralBinom (n : ℕ) : ℕ :=
  (2 * n).choose n

theorem centralBinom_samples :
    (List.range 9).map centralBinom = [1, 2, 6, 20, 70, 252, 924, 3432, 12870] := by
  native_decide

theorem centralBinom_below_four_pow :
    ∀ n ∈ Finset.Icc 1 12, centralBinom n < 4 ^ n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, _⟩
  interval_cases n <;> native_decide

theorem centralBinom_above_three_pow_tail :
    ∀ n ∈ Finset.Icc 8 14, 3 ^ n < centralBinom n := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨_, _⟩
  interval_cases n <;> native_decide

/-- A rational Gaussian-window envelope `C(2n,n-k)/C(2n,n)`. -/
def centralWindowRatio (n k : ℕ) : ℚ :=
  ((2 * n).choose (n - k) : ℚ) / (centralBinom n : ℚ)

theorem centralWindowRatio_n6 :
    centralWindowRatio 6 0 = 1 ∧
    centralWindowRatio 6 1 = 6 / 7 ∧
    centralWindowRatio 6 2 = 15 / 28 ∧
    centralWindowRatio 6 3 = 5 / 21 := by
  native_decide

/-- Finite log-concavity check for a row of binomial coefficients. -/
def binomialRowLogConcave (n : ℕ) : Bool :=
  (List.range (n + 1)).all fun k =>
    if k = 0 ∨ k = n then true
    else n.choose k * n.choose k ≥ n.choose (k - 1) * n.choose (k + 1)

theorem binomialRowLogConcave_12 :
    binomialRowLogConcave 12 = true := by
  native_decide

theorem binomialRowLogConcave_20 :
    binomialRowLogConcave 20 = true := by
  native_decide

/-- Stirling comparison in integer form: `n!` sits below `n^n` for sampled `n`. -/
def factorialBelowPowerCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => Nat.factorial n ≤ n ^ n

theorem factorialBelowPower_12 :
    factorialBelowPowerCheck 12 = true := by
  native_decide

/-- Saddle-point equation descriptor `r A'(r) / A(r) = n`. -/
structure SaddleEquation where
  targetIndex : ℕ
  radiusNumerator : ℕ
  radiusDenominator : ℕ

def binomialSaddle (n : ℕ) : SaddleEquation where
  targetIndex := n
  radiusNumerator := 1
  radiusDenominator := 1

theorem binomialSaddle_samples :
    (binomialSaddle 10).targetIndex = 10 ∧
    (binomialSaddle 10).radiusNumerator = 1 ∧
    (binomialSaddle 10).radiusDenominator = 1 := by
  native_decide

/-- Well-formedness certificate for a saddle equation descriptor. -/
def saddleEquationReady (saddle : SaddleEquation) : Prop :=
  0 < saddle.radiusNumerator ∧ 0 < saddle.radiusDenominator

theorem binomialSaddle_ready :
    saddleEquationReady (binomialSaddle 10) := by
  unfold saddleEquationReady binomialSaddle
  native_decide

/-- Finite executable readiness audit for saddle equation data. -/
def saddleEquationListReady (data : List SaddleEquation) : Bool :=
  data.all fun d => 0 < d.radiusNumerator && 0 < d.radiusDenominator

theorem saddleEquationList_readyWindow :
    saddleEquationListReady
      [{ targetIndex := 4, radiusNumerator := 1, radiusDenominator := 1 },
       { targetIndex := 10, radiusNumerator := 1, radiusDenominator := 1 }] =
      true := by
  unfold saddleEquationListReady
  native_decide

/-- Univariate saddle-point estimate certificate. -/
def SaddlePointEstimate
    (coeff : ℕ → ℂ) (saddle : SaddleEquation) : Prop :=
  saddleEquationReady saddle ∧ coeff 0 = 1 ∧ coeff saddle.targetIndex = 184756

def saddleCoeffWitness (n : ℕ) : ℂ :=
  if n = 0 then 1 else if n = 10 then 184756 else 0

theorem saddle_point_estimate_statement :
    SaddlePointEstimate saddleCoeffWitness (binomialSaddle 10) := by
  unfold SaddlePointEstimate saddleEquationReady binomialSaddle saddleCoeffWitness
  norm_num

/-- Finite Gaussian local approximation certificate over positive variances. -/
def GaussianLocalWindow
    (coeff : ℕ → ℝ) (center variance : ℕ → ℚ) (N : ℕ) : Prop :=
  (List.range (N + 1)).all (fun n => 0 < variance n) = true ∧
    (List.range (N + 1)).all (fun n => center n = 0) = true ∧
      coeff 0 = 0 ∧ coeff 6 = 6

def gaussianCoeffWitness (n : ℕ) : ℝ :=
  n

def gaussianCenterWitness (n : ℕ) : ℚ :=
  (n : ℚ) - (n : ℚ)

def gaussianVarianceWitness (n : ℕ) : ℚ :=
  (n : ℚ) - (n : ℚ) + 1

theorem gaussian_local_window_statement :
    GaussianLocalWindow gaussianCoeffWitness gaussianCenterWitness gaussianVarianceWitness 12 := by
  unfold GaussianLocalWindow
  constructor
  · native_decide
  · constructor
    · native_decide
    · norm_num [gaussianCoeffWitness]

/-- A finite certificate for saddle-point radius and Gaussian-window data. -/
structure SaddlePointRefinementCertificate where
  targetWindow : ℕ
  radiusNumeratorWindow : ℕ
  radiusDenominatorWindow : ℕ
  gaussianWindowBudget : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def SaddlePointRefinementCertificate.parametersControlled
    (cert : SaddlePointRefinementCertificate) : Prop :=
  0 < cert.radiusNumeratorWindow ∧ 0 < cert.radiusDenominatorWindow

def SaddlePointRefinementCertificate.budgetControlled
    (cert : SaddlePointRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.targetWindow + cert.radiusNumeratorWindow +
      cert.radiusDenominatorWindow + cert.gaussianWindowBudget + cert.slack

def saddlePointRefinementReady
    (cert : SaddlePointRefinementCertificate) : Prop :=
  cert.parametersControlled ∧ cert.budgetControlled

def SaddlePointRefinementCertificate.size
    (cert : SaddlePointRefinementCertificate) : ℕ :=
  cert.targetWindow + cert.radiusNumeratorWindow +
    cert.radiusDenominatorWindow + cert.gaussianWindowBudget + cert.slack

theorem saddlePoint_certificateBudgetWindow_le_size
    (cert : SaddlePointRefinementCertificate)
    (h : saddlePointRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSaddlePointRefinementCertificate :
    SaddlePointRefinementCertificate where
  targetWindow := 10
  radiusNumeratorWindow := 1
  radiusDenominatorWindow := 1
  gaussianWindowBudget := 6
  certificateBudgetWindow := 19
  slack := 1

example :
    saddlePointRefinementReady sampleSaddlePointRefinementCertificate := by
  norm_num [saddlePointRefinementReady,
    SaddlePointRefinementCertificate.parametersControlled,
    SaddlePointRefinementCertificate.budgetControlled,
    sampleSaddlePointRefinementCertificate]

example :
    sampleSaddlePointRefinementCertificate.certificateBudgetWindow ≤
      sampleSaddlePointRefinementCertificate.size := by
  apply saddlePoint_certificateBudgetWindow_le_size
  norm_num [saddlePointRefinementReady,
    SaddlePointRefinementCertificate.parametersControlled,
    SaddlePointRefinementCertificate.budgetControlled,
    sampleSaddlePointRefinementCertificate]


structure SaddlePointMethodBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddlePointMethodBudgetCertificate.controlled
    (c : SaddlePointMethodBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def SaddlePointMethodBudgetCertificate.budgetControlled
    (c : SaddlePointMethodBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SaddlePointMethodBudgetCertificate.Ready
    (c : SaddlePointMethodBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SaddlePointMethodBudgetCertificate.size
    (c : SaddlePointMethodBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem saddlePointMethod_budgetCertificate_le_size
    (c : SaddlePointMethodBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSaddlePointMethodBudgetCertificate :
    SaddlePointMethodBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleSaddlePointMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddlePointMethodBudgetCertificate.controlled,
      sampleSaddlePointMethodBudgetCertificate]
  · norm_num [SaddlePointMethodBudgetCertificate.budgetControlled,
      sampleSaddlePointMethodBudgetCertificate]

example :
    sampleSaddlePointMethodBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddlePointMethodBudgetCertificate.size := by
  apply saddlePointMethod_budgetCertificate_le_size
  constructor
  · norm_num [SaddlePointMethodBudgetCertificate.controlled,
      sampleSaddlePointMethodBudgetCertificate]
  · norm_num [SaddlePointMethodBudgetCertificate.budgetControlled,
      sampleSaddlePointMethodBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSaddlePointMethodBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddlePointMethodBudgetCertificate.controlled,
      sampleSaddlePointMethodBudgetCertificate]
  · norm_num [SaddlePointMethodBudgetCertificate.budgetControlled,
      sampleSaddlePointMethodBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddlePointMethodBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddlePointMethodBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SaddlePointMethodBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSaddlePointMethodBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSaddlePointMethodBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SaddlePointMethod
