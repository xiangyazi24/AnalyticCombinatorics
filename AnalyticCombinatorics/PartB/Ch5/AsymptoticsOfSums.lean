import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.AsymptoticsOfSums


open Finset

/-!
# Asymptotics of Sums

Finite arithmetic certificates for Chapter V-style asymptotic analysis of sums:
power sums, harmonic sums, generalized and alternating harmonic sums, and
digit-sum congruences.  Euler-Maclaurin analysis explains the asymptotic scale;
the Lean content here records exact finite checks by computation.
-/

/-! ## Power sums -/

/-- `1 + 2 + ... + n`. -/
def powerSum1 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (k + 1)

/-- `1^2 + 2^2 + ... + n^2`. -/
def powerSum2 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (k + 1) ^ 2

/-- `1^3 + 2^3 + ... + n^3`. -/
def powerSum3 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (k + 1) ^ 3

theorem power_sum_formulas_checked_1_to_15 :
    ∀ i : Fin 15,
      let n := i.val + 1
      powerSum1 n = n * (n + 1) / 2 ∧
      powerSum2 n = n * (n + 1) * (2 * n + 1) / 6 ∧
      powerSum3 n = (n * (n + 1) / 2) ^ 2 := by native_decide

/-! ## Harmonic numbers -/

/-- `H_n = 1 + 1/2 + ... + 1/n`. -/
def harmonicNumber (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 : ℚ) / (k + 1 : ℚ)

/-- Exact values of `H_n` for `1 <= n <= 12`. -/
def harmonicTable : Fin 12 → ℚ :=
  ![1, 3 / 2, 11 / 6, 25 / 12, 137 / 60, 49 / 20,
    363 / 140, 761 / 280, 7129 / 2520, 7381 / 2520,
    83711 / 27720, 86021 / 27720]

theorem harmonic_values_1_to_12 :
    ∀ i : Fin 12, harmonicNumber (i.val + 1) = harmonicTable i := by native_decide

/-- `lcm(1, 2, ..., n)`, with `lcmUpTo 0 = 1`. -/
def lcmUpTo : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmUpTo n) (n + 1)

/-- Values of `lcm(1, ..., n) * H_n` for `1 <= n <= 12`. -/
def harmonicLcmNumeratorTable : Fin 12 → ℕ :=
  ![1, 3, 11, 25, 137, 147, 1089, 2283, 7129, 7381, 83711, 86021]

theorem harmonic_lcm_scaled_numerators_1_to_12 :
    ∀ i : Fin 12,
      harmonicNumber (i.val + 1) * (lcmUpTo (i.val + 1) : ℚ) =
        harmonicLcmNumeratorTable i := by native_decide

/-! ## Generalized harmonic numbers -/

/-- `H_n^(2) = 1 + 1/2^2 + ... + 1/n^2`. -/
def generalizedHarmonicTwo (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 : ℚ) / ((k + 1 : ℚ) ^ 2)

/-- Exact values of `H_n^(2)` for `1 <= n <= 8`. -/
def generalizedHarmonicTwoTable : Fin 8 → ℚ :=
  ![1, 5 / 4, 49 / 36, 205 / 144, 5269 / 3600, 5369 / 3600,
    266681 / 176400, 1077749 / 705600]

theorem generalized_harmonic_two_values_1_to_8 :
    ∀ i : Fin 8,
      generalizedHarmonicTwo (i.val + 1) = generalizedHarmonicTwoTable i := by native_decide

theorem generalized_harmonic_two_eight_expanded :
    generalizedHarmonicTwo 8 =
      (1 : ℚ) + 1 / 4 + 1 / 9 + 1 / 16 + 1 / 25 + 1 / 36 + 1 / 49 + 1 / 64 := by
  native_decide

/-! ## Alternating harmonic sums -/

/-- `1 - 1/2 + 1/3 - ... + (-1)^(n+1)/n`. -/
def alternatingHarmonic (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n,
    if (k + 1) % 2 = 1 then
      (1 : ℚ) / (k + 1 : ℚ)
    else
      -((1 : ℚ) / (k + 1 : ℚ))

/-- Exact alternating harmonic partial sums for `1 <= n <= 12`. -/
def alternatingHarmonicTable : Fin 12 → ℚ :=
  ![1, 1 / 2, 5 / 6, 7 / 12, 47 / 60, 37 / 60,
    319 / 420, 533 / 840, 1879 / 2520, 1627 / 2520,
    20417 / 27720, 18107 / 27720]

theorem alternating_harmonic_values_1_to_12 :
    ∀ i : Fin 12,
      alternatingHarmonic (i.val + 1) = alternatingHarmonicTable i := by native_decide

/-! ## Digit sums and digital roots -/

/-- Fuel-limited digit sum in base `b`; the public wrapper supplies enough fuel for
    base `b >= 2`. -/
def digitSumBaseAux (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      if n < b then
        n
      else
        n % b + digitSumBaseAux b fuel (n / b)

/-- Sum of digits of `n` in base `b`. -/
def digitSumBase (b n : ℕ) : ℕ :=
  digitSumBaseAux b (n + 1) n

theorem digit_sum_base10_123 : digitSumBase 10 123 = 6 := by native_decide

theorem digit_sum_base10_999 : digitSumBase 10 999 = 27 := by native_decide

/-- Sample pairs for checking `s(a+b) ≡ s(a)+s(b) (mod 9)` in base 10. -/
def digitSumAddPairsA : Fin 8 → ℕ :=
  ![0, 1, 9, 37, 99, 123, 456, 999]

/-- Second coordinates for the base-10 digit-sum congruence checks. -/
def digitSumAddPairsB : Fin 8 → ℕ :=
  ![0, 8, 91, 64, 901, 999, 789, 1]

theorem digit_sum_add_mod9_base10_checked_pairs :
    ∀ i : Fin 8,
      digitSumBase 10 (digitSumAddPairsA i + digitSumAddPairsB i) % 9 =
        (digitSumBase 10 (digitSumAddPairsA i) + digitSumBase 10 (digitSumAddPairsB i)) % 9 := by
  native_decide

theorem digit_sum_456_789_mod9 :
    (digitSumBase 10 456 + digitSumBase 10 789) % 9 =
        digitSumBase 10 (456 + 789) % 9 ∧
      digitSumBase 10 (456 + 789) % 9 = digitSumBase 10 1245 % 9 ∧
      digitSumBase 10 1245 = 12 ∧
      digitSumBase 10 456 = 15 ∧
      digitSumBase 10 789 = 24 := by native_decide



structure AsymptoticsOfSumsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AsymptoticsOfSumsBudgetCertificate.controlled
    (c : AsymptoticsOfSumsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AsymptoticsOfSumsBudgetCertificate.budgetControlled
    (c : AsymptoticsOfSumsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AsymptoticsOfSumsBudgetCertificate.Ready
    (c : AsymptoticsOfSumsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AsymptoticsOfSumsBudgetCertificate.size
    (c : AsymptoticsOfSumsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem asymptoticsOfSums_budgetCertificate_le_size
    (c : AsymptoticsOfSumsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAsymptoticsOfSumsBudgetCertificate :
    AsymptoticsOfSumsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAsymptoticsOfSumsBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticsOfSumsBudgetCertificate.controlled,
      sampleAsymptoticsOfSumsBudgetCertificate]
  · norm_num [AsymptoticsOfSumsBudgetCertificate.budgetControlled,
      sampleAsymptoticsOfSumsBudgetCertificate]

example :
    sampleAsymptoticsOfSumsBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticsOfSumsBudgetCertificate.size := by
  apply asymptoticsOfSums_budgetCertificate_le_size
  constructor
  · norm_num [AsymptoticsOfSumsBudgetCertificate.controlled,
      sampleAsymptoticsOfSumsBudgetCertificate]
  · norm_num [AsymptoticsOfSumsBudgetCertificate.budgetControlled,
      sampleAsymptoticsOfSumsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAsymptoticsOfSumsBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticsOfSumsBudgetCertificate.controlled,
      sampleAsymptoticsOfSumsBudgetCertificate]
  · norm_num [AsymptoticsOfSumsBudgetCertificate.budgetControlled,
      sampleAsymptoticsOfSumsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAsymptoticsOfSumsBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticsOfSumsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AsymptoticsOfSumsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAsymptoticsOfSumsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAsymptoticsOfSumsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.AsymptoticsOfSums
