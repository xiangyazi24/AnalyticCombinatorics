import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.ProbabilityDistributions

/-! # Ch III — Probability distributions and combinatorial coefficients

Finite table checks for elementary distributions and their combinatorial
normalizing identities.
-/


/-! ## 1. Binomial distribution -/

/-- Binomial coefficients `C(10,k)` for `k = 0..10`. -/
def binomial10Table : Fin 11 → ℕ :=
  ![1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1]

/-- The table entries are the binomial coefficients `C(10,k)`. -/
theorem binomial10Table_eq_choose :
    ∀ k : Fin 11, binomial10Table k = Nat.choose 10 k.val := by
  native_decide

/-- The row sum is `2^10 = 1024`. -/
theorem binomial10Table_sum :
    (∑ k : Fin 11, binomial10Table k) = 2 ^ 10 ∧
      (∑ k : Fin 11, binomial10Table k) = 1024 := by
  native_decide

/-! ## 2. Poisson-like scaled terms -/

/-- Scaled Poisson-like terms `6! * 2^k / k!` for `k = 0..6`. -/
def poissonScaledTable : Fin 7 → ℕ :=
  ![720, 1440, 1440, 960, 480, 192, 64]

/-- Each entry is `2^k * 6! / k!`. -/
theorem poissonScaledTable_eq_formula :
    ∀ k : Fin 7,
      poissonScaledTable k = 2 ^ k.val * Nat.factorial 6 / Nat.factorial k.val := by
  native_decide

/-! ## 3. Geometric distribution partial sums -/

/-- Powers `2^n` for `n = 0..10`. -/
def geometricPowersTable : Fin 11 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

/-- The table entries are `2^n`. -/
theorem geometricPowersTable_eq_pow :
    ∀ n : Fin 11, geometricPowersTable n = 2 ^ n.val := by
  native_decide

/-- Running sum `1 + 2 + 4 + ... + 2^n` read from the finite table. -/
def geometricRunningSum (n : Fin 11) : ℕ :=
  ∑ i : Fin (n.val + 1), geometricPowersTable ⟨i.val, by omega⟩

/-- For `n = 0..10`, `1 + 2 + 4 + ... + 2^n = 2^(n+1) - 1`. -/
theorem geometricRunningSum_eq :
    ∀ n : Fin 11, geometricRunningSum n = 2 ^ (n.val + 1) - 1 := by
  native_decide

/-! ## 4. Negative binomial coefficients -/

/-- Negative-binomial coefficients `C(n+k-1,k-1)` for `k = 3` and `n = 0..8`. -/
def negativeBinomialK3Table : Fin 9 → ℕ :=
  ![1, 3, 6, 10, 15, 21, 28, 36, 45]

/-- The `k = 3` negative-binomial row is the triangular-number row. -/
theorem negativeBinomialK3Table_eq_choose :
    ∀ n : Fin 9,
      negativeBinomialK3Table n = Nat.choose (n.val + 3 - 1) (3 - 1) := by
  native_decide

/-! ## 5. Hypergeometric distribution numerators -/

/-- Hypergeometric numerators `C(5,k) * C(5,3-k)` for `k = 0..3`. -/
def hypergeometricNumeratorsTable : Fin 4 → ℕ :=
  ![10, 50, 50, 10]

/-- Each numerator is `C(5,k) * C(5,3-k)`. -/
theorem hypergeometricNumeratorsTable_eq_formula :
    ∀ k : Fin 4,
      hypergeometricNumeratorsTable k =
        Nat.choose 5 k.val * Nat.choose 5 (3 - k.val) := by
  native_decide

/-- The numerator sum is `120 = C(10,3)`. -/
theorem hypergeometricNumeratorsTable_sum :
    (∑ k : Fin 4, hypergeometricNumeratorsTable k) = 120 ∧
      (∑ k : Fin 4, hypergeometricNumeratorsTable k) = Nat.choose 10 3 := by
  native_decide

/-! ## 6. Multinomial coefficients -/

/-- Four small multinomial coefficients. -/
def multinomialCoefficientsTable : Fin 4 → ℕ :=
  ![24, 12, 6, 30]

/-- Verify the listed multinomial coefficients. -/
theorem multinomialCoefficientsTable_eq_formulas :
    multinomialCoefficientsTable ⟨0, by omega⟩ =
        Nat.factorial 4 / (Nat.factorial 1 * Nat.factorial 1 *
          Nat.factorial 1 * Nat.factorial 1) ∧
      multinomialCoefficientsTable ⟨1, by omega⟩ =
        Nat.factorial 4 / (Nat.factorial 2 * Nat.factorial 1 * Nat.factorial 1) ∧
      multinomialCoefficientsTable ⟨2, by omega⟩ =
        Nat.factorial 4 / (Nat.factorial 2 * Nat.factorial 2) ∧
      multinomialCoefficientsTable ⟨3, by omega⟩ =
        Nat.factorial 5 / (Nat.factorial 2 * Nat.factorial 2 * Nat.factorial 1) := by
  native_decide



structure ProbabilityDistributionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProbabilityDistributionsBudgetCertificate.controlled
    (c : ProbabilityDistributionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ProbabilityDistributionsBudgetCertificate.budgetControlled
    (c : ProbabilityDistributionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ProbabilityDistributionsBudgetCertificate.Ready
    (c : ProbabilityDistributionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ProbabilityDistributionsBudgetCertificate.size
    (c : ProbabilityDistributionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem probabilityDistributions_budgetCertificate_le_size
    (c : ProbabilityDistributionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleProbabilityDistributionsBudgetCertificate :
    ProbabilityDistributionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleProbabilityDistributionsBudgetCertificate.Ready := by
  constructor
  · norm_num [ProbabilityDistributionsBudgetCertificate.controlled,
      sampleProbabilityDistributionsBudgetCertificate]
  · norm_num [ProbabilityDistributionsBudgetCertificate.budgetControlled,
      sampleProbabilityDistributionsBudgetCertificate]

example :
    sampleProbabilityDistributionsBudgetCertificate.certificateBudgetWindow ≤
      sampleProbabilityDistributionsBudgetCertificate.size := by
  apply probabilityDistributions_budgetCertificate_le_size
  constructor
  · norm_num [ProbabilityDistributionsBudgetCertificate.controlled,
      sampleProbabilityDistributionsBudgetCertificate]
  · norm_num [ProbabilityDistributionsBudgetCertificate.budgetControlled,
      sampleProbabilityDistributionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleProbabilityDistributionsBudgetCertificate.Ready := by
  constructor
  · norm_num [ProbabilityDistributionsBudgetCertificate.controlled,
      sampleProbabilityDistributionsBudgetCertificate]
  · norm_num [ProbabilityDistributionsBudgetCertificate.budgetControlled,
      sampleProbabilityDistributionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleProbabilityDistributionsBudgetCertificate.certificateBudgetWindow ≤
      sampleProbabilityDistributionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ProbabilityDistributionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleProbabilityDistributionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleProbabilityDistributionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.ProbabilityDistributions
