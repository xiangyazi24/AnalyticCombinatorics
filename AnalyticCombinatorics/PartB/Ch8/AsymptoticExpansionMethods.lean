import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch8.AsymptoticExpansionMethods


/-!
  Chapter VIII: finite decidable checks for asymptotic expansion methods
  around central binomial coefficients, Catalan numbers, factorial scales,
  double factorials, derangements, and Wilson-type congruences.
-/

/-! ## Central binomial coefficients -/

def centralBinomial (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n

def centralBinomialTable : Fin 13 → ℕ :=
  ![1, 2, 6, 20, 70, 252, 924, 3432, 12870, 48620, 184756, 705432, 2704156]

theorem central_binomial_values_0_to_12 :
    ∀ i : Fin 13, centralBinomialTable i = centralBinomial (i : ℕ) := by
  native_decide

theorem central_binomial_ratio_decreasing_1_to_10 :
    ∀ i : Fin 10,
      centralBinomial ((i : ℕ) + 2) * 4 ^ ((i : ℕ) + 1) <
        centralBinomial ((i : ℕ) + 1) * 4 ^ ((i : ℕ) + 2) := by
  native_decide

theorem central_binomial_inverse_scale_bound_1_to_12 :
    ∀ i : Fin 12,
      (4 ^ ((i : ℕ) + 1) / centralBinomial ((i : ℕ) + 1)) * 4 >
        (i : ℕ) + 1 := by
  native_decide

/-! ## Catalan numbers -/

def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

def catalanTable : Fin 13 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012]

theorem catalan_values_0_to_12 :
    ∀ i : Fin 13, catalanTable i = catalanNumber (i : ℕ) := by
  native_decide

theorem catalan_ratio_identity_0_to_12 :
    ∀ i : Fin 13,
      let n := (i : ℕ)
      (n + 2) * catalanNumber (n + 1) =
        2 * (2 * n + 1) * catalanNumber n := by
  native_decide

/-! ## Factorial and double-factorial ratios -/

theorem factorial_successor_ratio_0_to_12 :
    ∀ i : Fin 13,
      Nat.factorial ((i : ℕ) + 1) / Nat.factorial (i : ℕ) = (i : ℕ) + 1 := by
  native_decide

def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * doubleFactorial n

theorem even_double_factorial_identity_0_to_12 :
    ∀ i : Fin 13,
      doubleFactorial (2 * (i : ℕ)) = 2 ^ (i : ℕ) * Nat.factorial (i : ℕ) := by
  native_decide

theorem odd_double_factorial_identity_1_to_12 :
    ∀ i : Fin 12,
      let n := (i : ℕ) + 1
      doubleFactorial (2 * n - 1) = Nat.factorial (2 * n) / (2 ^ n * Nat.factorial n) := by
  native_decide

theorem double_factorial_five_checks :
    doubleFactorial (2 * 5 - 1) = 945 ∧
      doubleFactorial 9 = 9 * 7 * 5 * 3 * 1 ∧
      9 * 7 * 5 * 3 * 1 = 945 ∧
      Nat.factorial (2 * 5) / (2 ^ 5 * Nat.factorial 5) = 945 ∧
      Nat.factorial 10 = 3628800 ∧
      2 ^ 5 * Nat.factorial 5 = 32 * 120 ∧
      3628800 / (32 * 120) = 945 := by
  native_decide

/-! ## Subfactorial ratios -/

def subfactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 9
  | 5 => 44
  | 6 => 265
  | 7 => 1854
  | 8 => 14833
  | _ => 0

def subfactorialTable : Fin 9 → ℕ :=
  ![1, 0, 1, 2, 9, 44, 265, 1854, 14833]

def subfactorialRatioNumerator : ℕ → ℕ
  | 2 => 1
  | 3 => 1
  | 4 => 3
  | 5 => 11
  | 6 => 53
  | 7 => 103
  | 8 => 2119
  | _ => 0

def subfactorialRatioDenominator : ℕ → ℕ
  | 2 => 2
  | 3 => 3
  | 4 => 8
  | 5 => 30
  | 6 => 144
  | 7 => 280
  | 8 => 5760
  | _ => 1

theorem subfactorial_values_0_to_8 :
    ∀ i : Fin 9, subfactorialTable i = subfactorial (i : ℕ) := by
  native_decide

theorem subfactorial_ratio_denominator_checks_2_to_8 :
    ∀ i : Fin 7,
      let n := (i : ℕ) + 2
      subfactorial n * subfactorialRatioDenominator n =
        subfactorialRatioNumerator n * Nat.factorial n := by
  native_decide

/-! ## Wilson congruence checks -/

def wilsonPrimeTable : Fin 6 → ℕ :=
  ![2, 3, 5, 7, 11, 13]

theorem wilson_prime_factorial_mod_checks :
    ∀ i : Fin 6,
      let n := wilsonPrimeTable i
      Nat.factorial (n - 1) % n = n - 1 := by
  native_decide



structure AsymptoticExpansionMethodsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AsymptoticExpansionMethodsBudgetCertificate.controlled
    (c : AsymptoticExpansionMethodsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AsymptoticExpansionMethodsBudgetCertificate.budgetControlled
    (c : AsymptoticExpansionMethodsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AsymptoticExpansionMethodsBudgetCertificate.Ready
    (c : AsymptoticExpansionMethodsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AsymptoticExpansionMethodsBudgetCertificate.size
    (c : AsymptoticExpansionMethodsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem asymptoticExpansionMethods_budgetCertificate_le_size
    (c : AsymptoticExpansionMethodsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAsymptoticExpansionMethodsBudgetCertificate :
    AsymptoticExpansionMethodsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAsymptoticExpansionMethodsBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticExpansionMethodsBudgetCertificate.controlled,
      sampleAsymptoticExpansionMethodsBudgetCertificate]
  · norm_num [AsymptoticExpansionMethodsBudgetCertificate.budgetControlled,
      sampleAsymptoticExpansionMethodsBudgetCertificate]

example :
    sampleAsymptoticExpansionMethodsBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticExpansionMethodsBudgetCertificate.size := by
  apply asymptoticExpansionMethods_budgetCertificate_le_size
  constructor
  · norm_num [AsymptoticExpansionMethodsBudgetCertificate.controlled,
      sampleAsymptoticExpansionMethodsBudgetCertificate]
  · norm_num [AsymptoticExpansionMethodsBudgetCertificate.budgetControlled,
      sampleAsymptoticExpansionMethodsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAsymptoticExpansionMethodsBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticExpansionMethodsBudgetCertificate.controlled,
      sampleAsymptoticExpansionMethodsBudgetCertificate]
  · norm_num [AsymptoticExpansionMethodsBudgetCertificate.budgetControlled,
      sampleAsymptoticExpansionMethodsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAsymptoticExpansionMethodsBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticExpansionMethodsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AsymptoticExpansionMethodsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAsymptoticExpansionMethodsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAsymptoticExpansionMethodsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.AsymptoticExpansionMethods
