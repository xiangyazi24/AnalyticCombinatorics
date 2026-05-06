import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch8.StirlingApproximation


/-!
  Chapter VIII saddle-point numerics: finite, decidable checks around
  Stirling scales, central binomial coefficients, factorial ratios, and
  double factorial identities.

  The Stirling and central-binomial estimates below use fixed decimal
  rational brackets for `e`, `sqrt (2*pi*n)`, and `sqrt (pi*n)`.  This keeps
  the formal statements in integer arithmetic while recording the usual
  scales

    `sqrt (2*pi*n) * (n/e)^n`
    `4^n / sqrt (pi*n)`.
-/

/-! ## 1. Stirling factorial bounds -/

def decimalScale : ℕ := 100000

def eLower100000 : ℕ := 271828
def eUpper100000 : ℕ := 271829

/-- Lower decimal brackets for `sqrt (2*pi*n)`, scaled by `100000`. -/
def sqrtTwoPiNLower100000 : ℕ → ℕ
  | 1 => 250662
  | 2 => 354490
  | 3 => 434160
  | 4 => 501325
  | 5 => 560499
  | 6 => 613996
  | 7 => 663191
  | 8 => 708981
  | 9 => 751988
  | 10 => 792665
  | 11 => 831354
  | 12 => 868321
  | _ => 0

/-- Upper decimal brackets for `sqrt (2*pi*n)`, scaled by `100000`. -/
def sqrtTwoPiNUpper100000 : ℕ → ℕ
  | 1 => 250663
  | 2 => 354491
  | 3 => 434161
  | 4 => 501326
  | 5 => 560500
  | 6 => 613997
  | 7 => 663192
  | 8 => 708982
  | 9 => 751989
  | 10 => 792666
  | 11 => 831355
  | 12 => 868322
  | _ => 0

/--
Integer form of
`sqrt (2*pi*n) * (n/e)^n <= n!`, checked for `1 <= n <= 12`.
-/
theorem stirling_factorial_lower_1_to_12 :
    ∀ n : Fin 13, 1 ≤ n.val →
      sqrtTwoPiNLower100000 n.val * n.val ^ n.val * decimalScale ^ (n.val - 1) ≤
        Nat.factorial n.val * eUpper100000 ^ n.val := by
  native_decide

/--
Coarse integer form of
`n! <= 1.1 * sqrt (2*pi*n) * (n/e)^n`, checked for `1 <= n <= 12`.
-/
theorem stirling_factorial_upper_1_to_12 :
    ∀ n : Fin 13, 1 ≤ n.val →
      10 * Nat.factorial n.val * eLower100000 ^ n.val ≤
        11 * sqrtTwoPiNUpper100000 n.val * n.val ^ n.val *
          decimalScale ^ (n.val - 1) := by
  native_decide

theorem stirling_factorial_bound_examples :
    (sqrtTwoPiNLower100000 8 * 8^8 * decimalScale^7 ≤
        Nat.factorial 8 * eUpper100000^8) ∧
      (10 * Nat.factorial 8 * eLower100000^8 ≤
        11 * sqrtTwoPiNUpper100000 8 * 8^8 * decimalScale^7) ∧
      (sqrtTwoPiNLower100000 12 * 12^12 * decimalScale^11 ≤
        Nat.factorial 12 * eUpper100000^12) ∧
      (10 * Nat.factorial 12 * eLower100000^12 ≤
        11 * sqrtTwoPiNUpper100000 12 * 12^12 * decimalScale^11) := by
  native_decide

/-! ## 2. Central binomial coefficient bounds -/

/-- Lower decimal brackets for `sqrt (pi*n)`, scaled by `100000`. -/
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

/-- Upper decimal brackets for `sqrt (pi*n)`, scaled by `100000`. -/
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

/--
Central binomial form of `Nat.choose (2*n) n ~ 4^n / sqrt (pi*n)`:
the scaled ratio lies between `0.95` and `1.05`, checked for `3 <= n <= 20`.
-/
theorem central_binomial_stirling_window_3_to_20 :
    ∀ n : Fin 21, 3 ≤ n.val →
      95 * 4^n.val * decimalScale ≤
          100 * Nat.choose (2 * n.val) n.val * sqrtPiNLower100000 n.val ∧
        100 * Nat.choose (2 * n.val) n.val * sqrtPiNUpper100000 n.val ≤
          105 * 4^n.val * decimalScale := by
  native_decide

/-- Standard coarse central-binomial sandwich checks. -/
theorem central_binomial_coarse_bounds_1_to_20 :
    ∀ n : Fin 21, 1 ≤ n.val →
      Nat.choose (2 * n.val) n.val < 4^n.val ∧
        4^n.val ≤ (2 * n.val + 1) * Nat.choose (2 * n.val) n.val := by
  native_decide

/-! ## 3. Log-factorial superadditivity -/

/--
Decidable multiplicative kernel of
`log(n!) + log(m!) <= log((n+m)!)`, checked for `0 <= n,m <= 20`.
-/
theorem log_factorial_superadditivity_kernel_0_to_20 :
    ∀ n m : Fin 21,
      Nat.factorial n.val * Nat.factorial m.val ≤ Nat.factorial (n.val + m.val) := by
  native_decide

theorem log_factorial_superadditivity_examples :
    Nat.factorial 4 * Nat.factorial 7 ≤ Nat.factorial (4 + 7) ∧
      Nat.factorial 10 * Nat.factorial 10 ≤ Nat.factorial (10 + 10) ∧
      Nat.factorial 20 * Nat.factorial 5 ≤ Nat.factorial (20 + 5) := by
  native_decide

/-! ## 4. Ratio asymptotics: `n!/(n-k)!` versus `n^k` -/

def factorialRatio (n k : ℕ) : ℕ :=
  Nat.factorial n / Nat.factorial (n - k)

/-- Exact falling-factorial expansions for small fixed `k`. -/
theorem factorial_ratio_polynomial_forms_4_to_40 :
    ∀ n : Fin 41, 4 ≤ n.val →
      factorialRatio n.val 0 = 1 ∧
        factorialRatio n.val 1 = n.val ∧
        factorialRatio n.val 2 = n.val * (n.val - 1) ∧
        factorialRatio n.val 3 = n.val * (n.val - 1) * (n.val - 2) ∧
        factorialRatio n.val 4 =
          n.val * (n.val - 1) * (n.val - 2) * (n.val - 3) := by
  native_decide

/--
For `k <= 4` and `10 <= n <= 40`, the factorial ratio is within a factor
`2` of `n^k`, a coarse finite version of the fixed-`k` asymptotic.
-/
theorem factorial_ratio_within_factor_two_k_le_4_10_to_40 :
    ∀ n : Fin 41, ∀ k : Fin 5, 10 ≤ n.val →
      factorialRatio n.val k.val ≤ n.val ^ k.val ∧
        n.val ^ k.val ≤ 2 * factorialRatio n.val k.val := by
  native_decide

/--
For `k <= 3` and `20 <= n <= 60`, the same ratio is within `20%` below
`n^k`, and never above `n^k`.
-/
theorem factorial_ratio_within_twenty_percent_k_le_3_20_to_60 :
    ∀ n : Fin 61, ∀ k : Fin 4, 20 ≤ n.val →
      factorialRatio n.val k.val ≤ n.val ^ k.val ∧
        4 * n.val ^ k.val ≤ 5 * factorialRatio n.val k.val := by
  native_decide

/-! ## 5. Double factorial identities -/

def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * doubleFactorial n

/-- `(2n)!! = 2^n * n!`, checked for `0 <= n <= 20`. -/
theorem even_doubleFactorial_identity_0_to_20 :
    ∀ n : Fin 21,
      doubleFactorial (2 * n.val) = 2^n.val * Nat.factorial n.val := by
  native_decide

/-- `(2n-1)!! = (2n)! / (2^n * n!)`, checked for `0 <= n <= 20`. -/
theorem odd_doubleFactorial_identity_0_to_20 :
    ∀ n : Fin 21,
      doubleFactorial (2 * n.val - 1) =
        Nat.factorial (2 * n.val) / (2^n.val * Nat.factorial n.val) := by
  native_decide

theorem doubleFactorial_identity_examples :
    doubleFactorial (2 * 8) = 2^8 * Nat.factorial 8 ∧
      doubleFactorial (2 * 8 - 1) = Nat.factorial (2 * 8) / (2^8 * Nat.factorial 8) ∧
      doubleFactorial (2 * 12) = 2^12 * Nat.factorial 12 ∧
      doubleFactorial (2 * 12 - 1) =
        Nat.factorial (2 * 12) / (2^12 * Nat.factorial 12) := by
  native_decide



structure StirlingApproximationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StirlingApproximationBudgetCertificate.controlled
    (c : StirlingApproximationBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def StirlingApproximationBudgetCertificate.budgetControlled
    (c : StirlingApproximationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def StirlingApproximationBudgetCertificate.Ready
    (c : StirlingApproximationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StirlingApproximationBudgetCertificate.size
    (c : StirlingApproximationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem stirlingApproximation_budgetCertificate_le_size
    (c : StirlingApproximationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleStirlingApproximationBudgetCertificate :
    StirlingApproximationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleStirlingApproximationBudgetCertificate.Ready := by
  constructor
  · norm_num [StirlingApproximationBudgetCertificate.controlled,
      sampleStirlingApproximationBudgetCertificate]
  · norm_num [StirlingApproximationBudgetCertificate.budgetControlled,
      sampleStirlingApproximationBudgetCertificate]

example :
    sampleStirlingApproximationBudgetCertificate.certificateBudgetWindow ≤
      sampleStirlingApproximationBudgetCertificate.size := by
  apply stirlingApproximation_budgetCertificate_le_size
  constructor
  · norm_num [StirlingApproximationBudgetCertificate.controlled,
      sampleStirlingApproximationBudgetCertificate]
  · norm_num [StirlingApproximationBudgetCertificate.budgetControlled,
      sampleStirlingApproximationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleStirlingApproximationBudgetCertificate.Ready := by
  constructor
  · norm_num [StirlingApproximationBudgetCertificate.controlled,
      sampleStirlingApproximationBudgetCertificate]
  · norm_num [StirlingApproximationBudgetCertificate.budgetControlled,
      sampleStirlingApproximationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleStirlingApproximationBudgetCertificate.certificateBudgetWindow ≤
      sampleStirlingApproximationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List StirlingApproximationBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleStirlingApproximationBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleStirlingApproximationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.StirlingApproximation
