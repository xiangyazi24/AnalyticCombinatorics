import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.EulerMaclaurin


/-!
Finite, decidable Euler-Maclaurin and Faulhaber certificates.

All statements below are closed numerical checks, or finite universal checks
over `Fin m`, so that `native_decide` can verify them directly.
-/

/-! ## Bernoulli numbers, stored as natural numerator/denominator data -/

/-- Numerators of the Bernoulli values used in this file. -/
def bernoulliNumerator : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 4 => 1
  | 6 => 1
  | 8 => 1
  | 10 => 5
  | _ => 0

/-- Denominators of the Bernoulli values used in this file. -/
def bernoulliDenominator : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 4 => 30
  | 6 => 42
  | 8 => 30
  | 10 => 66
  | _ => 1

/-- Sign bit for the Bernoulli values used in this file. -/
def bernoulliNegative : ℕ → Bool
  | 1 => true
  | 4 => true
  | 8 => true
  | _ => false

/-- The same Bernoulli data, interpreted as rational numbers. -/
def bernoulliRat (n : ℕ) : ℚ :=
  let q := (bernoulliNumerator n : ℚ) / (bernoulliDenominator n : ℚ)
  if bernoulliNegative n then -q else q

theorem bernoulli_B0_parts :
    bernoulliNumerator 0 = 1 ∧ bernoulliDenominator 0 = 1 ∧
      bernoulliNegative 0 = false := by native_decide

theorem bernoulli_B1_parts :
    bernoulliNumerator 1 = 1 ∧ bernoulliDenominator 1 = 2 ∧
      bernoulliNegative 1 = true := by native_decide

theorem bernoulli_B2_parts :
    bernoulliNumerator 2 = 1 ∧ bernoulliDenominator 2 = 6 ∧
      bernoulliNegative 2 = false := by native_decide

theorem bernoulli_B4_parts :
    bernoulliNumerator 4 = 1 ∧ bernoulliDenominator 4 = 30 ∧
      bernoulliNegative 4 = true := by native_decide

theorem bernoulli_B6_parts :
    bernoulliNumerator 6 = 1 ∧ bernoulliDenominator 6 = 42 ∧
      bernoulliNegative 6 = false := by native_decide

theorem bernoulli_B0_value : bernoulliRat 0 = 1 := by native_decide
theorem bernoulli_B1_value : bernoulliRat 1 = -1 / 2 := by native_decide
theorem bernoulli_B2_value : bernoulliRat 2 = 1 / 6 := by native_decide
theorem bernoulli_B4_value : bernoulliRat 4 = -1 / 30 := by native_decide
theorem bernoulli_B6_value : bernoulliRat 6 = 1 / 42 := by native_decide

/-! ## Power sums and Faulhaber identities -/

/-- `powerSum p n = Σ_{k=1}^n k^p`. -/
def powerSum (p n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (k + 1) ^ p

theorem power_sum_linear_formula_checked :
    ∀ n : Fin 101,
      2 * powerSum 1 n.val = n.val * (n.val + 1) := by native_decide

theorem power_sum_square_formula_checked :
    ∀ n : Fin 101,
      6 * powerSum 2 n.val = n.val * (n.val + 1) * (2 * n.val + 1) := by
  native_decide

theorem power_sum_cubic_faulhaber_checked :
    ∀ n : Fin 101,
      powerSum 3 n.val = (powerSum 1 n.val) ^ 2 := by native_decide

theorem power_sum_linear_n10 :
    powerSum 1 10 = 10 * (10 + 1) / 2 := by native_decide

theorem power_sum_square_n10 :
    powerSum 2 10 = 10 * (10 + 1) * (2 * 10 + 1) / 6 := by native_decide

theorem faulhaber_cubic_n10 :
    powerSum 3 10 = (powerSum 1 10) ^ 2 := by native_decide

/-! ## Harmonic number bounds by rational logarithm certificates -/

/-- `harmonicRat n = H_n = Σ_{k=1}^n 1/k`, as a rational number. -/
def harmonicRat (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

/--
Lower decimal certificates for `log n`, scaled by 100.
These are used only for decidable rational checks on `n = 1, ..., 10`.
-/
def logLowerHundred : ℕ → ℕ
  | 1 => 0
  | 2 => 69
  | 3 => 109
  | 4 => 138
  | 5 => 160
  | 6 => 179
  | 7 => 194
  | 8 => 207
  | 9 => 219
  | 10 => 230
  | _ => 0

/--
Upper decimal certificates for `log n`, scaled by 100.
For each checked `n`, `log n` lies below this rational certificate.
-/
def logUpperHundred : ℕ → ℕ
  | 1 => 0
  | 2 => 70
  | 3 => 110
  | 4 => 139
  | 5 => 161
  | 6 => 180
  | 7 => 195
  | 8 => 208
  | 9 => 220
  | 10 => 231
  | _ => 0

def logLowerRat (n : ℕ) : ℚ := (logLowerHundred n : ℚ) / 100
def logUpperRat (n : ℕ) : ℚ := (logUpperHundred n : ℚ) / 100

theorem harmonic_log_bounds_small_checked :
    ∀ n : Fin 10,
      logUpperRat (n.val + 1) <= harmonicRat (n.val + 1) ∧
        harmonicRat (n.val + 1) <= logLowerRat (n.val + 1) + 1 := by
  native_decide

theorem harmonic_values_small_checked :
    harmonicRat 1 = 1 ∧ harmonicRat 2 = 3 / 2 ∧ harmonicRat 3 = 11 / 6 ∧
      harmonicRat 4 = 25 / 12 ∧ harmonicRat 5 = 137 / 60 := by
  native_decide

/-! ## Euler-Maclaurin polynomial exactness checks -/

theorem euler_maclaurin_constant_remainder_zero_checked :
    ∀ n : Fin 101,
      (∑ _ ∈ Finset.range n.val, (7 : ℕ)) = 7 * n.val := by native_decide

theorem euler_maclaurin_linear_remainder_zero_checked :
    ∀ n : Fin 101,
      2 * powerSum 1 n.val = n.val * (n.val + 1) := by native_decide

theorem euler_maclaurin_quadratic_remainder_zero_checked :
    ∀ n : Fin 101,
      6 * powerSum 2 n.val = n.val * (n.val + 1) * (2 * n.val + 1) := by
  native_decide

theorem euler_maclaurin_cubic_remainder_zero_checked :
    ∀ n : Fin 101,
      4 * powerSum 3 n.val = n.val ^ 2 * (n.val + 1) ^ 2 := by
  native_decide

/-! ## Tangent numbers and their Bernoulli relation -/

/-- Tangent numbers `1, 2, 16, 272, 7936`. -/
def tangentNumber : Fin 5 → ℕ :=
  ![1, 2, 16, 272, 7936]

theorem tangent_numbers_table :
    tangentNumber 0 = 1 ∧ tangentNumber 1 = 2 ∧ tangentNumber 2 = 16 ∧
      tangentNumber 3 = 272 ∧ tangentNumber 4 = 7936 := by
  native_decide

theorem bernoulli_abs_even_extra_values_for_tangent :
    bernoulliNumerator 8 = 1 ∧ bernoulliDenominator 8 = 30 ∧
      bernoulliNegative 8 = true ∧ bernoulliNumerator 10 = 5 ∧
        bernoulliDenominator 10 = 66 ∧ bernoulliNegative 10 = false := by
  native_decide

/--
Cross-multiplied tangent/Bernoulli identity
`T_m = 2^(2m) * (2^(2m)-1) * |B_(2m)| / (2m)` for `m = 1, ..., 5`.
-/
theorem tangent_bernoulli_relation_checked :
    ∀ j : Fin 5,
      let m := j.val + 1
      2 ^ (2 * m) * (2 ^ (2 * m) - 1) * bernoulliNumerator (2 * m) =
        tangentNumber j * (2 * m) * bernoulliDenominator (2 * m) := by
  native_decide



structure EulerMaclaurinBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EulerMaclaurinBudgetCertificate.controlled
    (c : EulerMaclaurinBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def EulerMaclaurinBudgetCertificate.budgetControlled
    (c : EulerMaclaurinBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def EulerMaclaurinBudgetCertificate.Ready
    (c : EulerMaclaurinBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EulerMaclaurinBudgetCertificate.size
    (c : EulerMaclaurinBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem eulerMaclaurin_budgetCertificate_le_size
    (c : EulerMaclaurinBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEulerMaclaurinBudgetCertificate :
    EulerMaclaurinBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleEulerMaclaurinBudgetCertificate.Ready := by
  constructor
  · norm_num [EulerMaclaurinBudgetCertificate.controlled,
      sampleEulerMaclaurinBudgetCertificate]
  · norm_num [EulerMaclaurinBudgetCertificate.budgetControlled,
      sampleEulerMaclaurinBudgetCertificate]

example :
    sampleEulerMaclaurinBudgetCertificate.certificateBudgetWindow ≤
      sampleEulerMaclaurinBudgetCertificate.size := by
  apply eulerMaclaurin_budgetCertificate_le_size
  constructor
  · norm_num [EulerMaclaurinBudgetCertificate.controlled,
      sampleEulerMaclaurinBudgetCertificate]
  · norm_num [EulerMaclaurinBudgetCertificate.budgetControlled,
      sampleEulerMaclaurinBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleEulerMaclaurinBudgetCertificate.Ready := by
  constructor
  · norm_num [EulerMaclaurinBudgetCertificate.controlled,
      sampleEulerMaclaurinBudgetCertificate]
  · norm_num [EulerMaclaurinBudgetCertificate.budgetControlled,
      sampleEulerMaclaurinBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleEulerMaclaurinBudgetCertificate.certificateBudgetWindow ≤
      sampleEulerMaclaurinBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List EulerMaclaurinBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEulerMaclaurinBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleEulerMaclaurinBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.EulerMaclaurin
