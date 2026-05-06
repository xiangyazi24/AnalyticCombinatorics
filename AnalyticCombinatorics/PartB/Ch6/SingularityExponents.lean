/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Singularity exponents and coefficient growth.

  Singularity types classified by exponent α in (1−z/ρ)^α and their
  effect on coefficient asymptotics via the transfer theorem:
  • Pole of order m (α = −m): [z^n] ~ n^{m−1} ρ^{−n} / Γ(m)
  • Algebraic (α ∈ ℚ \ ℤ): [z^n] ~ n^{−α−1} ρ^{−n} / Γ(−α)
  • Logarithmic: log-factor corrections with harmonic numbers.
  Gamma function: Γ(n) = (n−1)! at positive integers, simple poles
  at 0, −1, −2, … with residue (−1)^n/n!.
  Reference: Flajolet & Sedgewick, §VI.1–VI.3.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.SingularityExponents
open Finset

/-! ## 1. Gamma function at positive integers

Γ(n) = (n−1)! for n ≥ 1. -/

/-- Γ(n) at positive integers: (n−1)!. Returns 0 at n = 0 (pole). -/
def gammaPos (n : ℕ) : ℚ :=
  if n = 0 then 0 else (Nat.factorial (n - 1) : ℚ)

theorem gamma_pos_values :
    gammaPos 1 = 1 ∧ gammaPos 2 = 1 ∧ gammaPos 3 = 2 ∧
    gammaPos 4 = 6 ∧ gammaPos 5 = 24 ∧ gammaPos 6 = 120 := by
  native_decide

/-- Γ(n+1) = n · Γ(n) verified for n = 1, …, 12. -/
theorem gamma_recurrence_1_12 :
    ∀ n ∈ Icc 1 12, gammaPos (n + 1) = (n : ℚ) * gammaPos n := by
  native_decide

/-! ## 2. Gamma poles at non-positive integers

Γ has simple poles at z = −n with residue (−1)^n / n!.
Equivalently, 1/Γ(n) = 0 for n = 0, −1, −2, …. -/

/-- Residue of Γ at z = −n. -/
def gammaResidue (n : ℕ) : ℚ := (-1 : ℚ) ^ n / (Nat.factorial n : ℚ)

theorem gamma_residue_values :
    gammaResidue 0 = 1 ∧ gammaResidue 1 = -1 ∧
    gammaResidue 2 = 1/2 ∧ gammaResidue 3 = -(1/6) ∧
    gammaResidue 4 = 1/24 ∧ gammaResidue 5 = -(1/120) := by
  native_decide

/-- Residues alternate in sign. -/
theorem gamma_residue_alternating :
    ∀ n ∈ range 16, gammaResidue n * gammaResidue (n + 1) < 0 := by
  native_decide

/-! ## 3. Gamma ratio at half-integers

Γ(n+1/2) / Γ(1/2) = (2n)! / (4^n · n!).
Recurrence: Γ(n+3/2) / Γ(n+1/2) = (2n+1)/2. -/

/-- Γ(n+1/2) / Γ(1/2) as a rational number. -/
def gammaHalfRatio (n : ℕ) : ℚ :=
  (Nat.factorial (2 * n) : ℚ) / ((4 : ℚ) ^ n * (Nat.factorial n : ℚ))

theorem gamma_half_ratio_values :
    gammaHalfRatio 0 = 1 ∧ gammaHalfRatio 1 = 1/2 ∧
    gammaHalfRatio 2 = 3/4 ∧ gammaHalfRatio 3 = 15/8 ∧
    gammaHalfRatio 4 = 105/16 := by
  native_decide

/-- Half-integer recurrence: ratio(n+1) = ratio(n) · (2n+1)/2. -/
theorem gamma_half_recurrence_0_8 :
    ∀ n ∈ range 9,
      gammaHalfRatio (n + 1) =
        gammaHalfRatio n * (((2 * n + 1 : ℕ) : ℚ) / 2) := by
  native_decide

/-- Legendre duplication (rationalized):
    Γ(2n) = 2^{2n−1} · Γ(n) · Γ(n+1/2)/Γ(1/2). -/
theorem legendre_duplication_1_6 :
    ∀ n ∈ Icc 1 6,
      gammaPos (2 * n) =
        (2 : ℚ) ^ (2 * n - 1) * gammaPos n * gammaHalfRatio n := by
  native_decide

/-! ## 4. Generalized binomial coefficient

For α ∈ ℚ, C(α, k) = α(α−1)···(α−k+1) / k!.
Then [z^n](1−z)^α = (−1)^n · C(α, n). -/

/-- Generalized binomial coefficient for rational α. -/
def genBinom (alpha : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => genBinom alpha k * (alpha - k) / (k + 1)

/-- C(−1/2, n): inverse square-root singularity (1−z)^{−1/2}. -/
theorem gen_binom_neg_half :
    genBinom (-1/2) 0 = 1 ∧ genBinom (-1/2) 1 = -(1/2) ∧
    genBinom (-1/2) 2 = 3/8 ∧ genBinom (-1/2) 3 = -(5/16) ∧
    genBinom (-1/2) 4 = 35/128 := by
  native_decide

/-- (−1)^n C(−1/2, n) = C(2n,n)/4^n: central binomial connection. -/
theorem gen_binom_central_binom_0_8 :
    ∀ n ∈ range 9,
      (-1 : ℚ) ^ n * genBinom (-1/2) n =
        (Nat.choose (2 * n) n : ℚ) / (4 : ℚ) ^ n := by
  native_decide

/-- C(1/2, n): square-root singularity (1−z)^{1/2}. -/
theorem gen_binom_half :
    genBinom (1/2) 0 = 1 ∧ genBinom (1/2) 1 = 1/2 ∧
    genBinom (1/2) 2 = -(1/8) ∧ genBinom (1/2) 3 = 1/16 ∧
    genBinom (1/2) 4 = -(5/128) := by
  native_decide

/-- C(−3/2, n): Catalan-type singularity. -/
theorem gen_binom_neg_three_half :
    genBinom (-3/2) 0 = 1 ∧ genBinom (-3/2) 1 = -(3/2) ∧
    genBinom (-3/2) 2 = 15/8 ∧ genBinom (-3/2) 3 = -(35/16) ∧
    genBinom (-3/2) 4 = 315/128 := by
  native_decide

/-- C(−1/3, n): cube-root singularity. -/
theorem gen_binom_neg_third :
    genBinom (-1/3) 0 = 1 ∧ genBinom (-1/3) 1 = -(1/3) ∧
    genBinom (-1/3) 2 = 2/9 ∧ genBinom (-1/3) 3 = -(14/81) := by
  native_decide

/-- For integer α = −m: (−1)^n C(−m, n) = C(n+m−1, n). -/
theorem pole_coeff_via_gen_binom :
    ∀ m ∈ (Icc 1 5 : Finset ℕ), ∀ n ∈ range 11,
      (-1 : ℚ) ^ n * genBinom (-↑m) n =
        ↑(Nat.choose (n + m - 1) n) := by
  native_decide

/-! ## 5. Singularity exponent classification -/

/-- Singularity exponent type from F&S Chapter VI. -/
inductive SingExponent where
  | pole (order : ℕ)
  | algebraic (num denom : ℤ)
  | logarithmic (power : ℕ)
  deriving DecidableEq, Repr

/-- Growth exponent −α−1 in the asymptotic factor n^{−α−1}. -/
def growthExponent : SingExponent → Option ℚ
  | SingExponent.pole m => some ((m : ℚ) - 1)
  | SingExponent.algebraic p q =>
      if q = 0 then none else some (-(p : ℚ) / (q : ℚ) - 1)
  | SingExponent.logarithmic _ => some (-1)

example : growthExponent (SingExponent.pole 1) = some 0 := by native_decide
example : growthExponent (SingExponent.pole 3) = some 2 := by native_decide
example : growthExponent (SingExponent.algebraic (-1) 2) = some (-(1/2)) := by native_decide
example : growthExponent (SingExponent.algebraic (-3) 2) = some (1/2) := by native_decide
example : growthExponent (SingExponent.logarithmic 1) = some (-1) := by native_decide

/-! ## 6. Pole asymptotics (α = −m ∈ ℤ)

C(n+m−1, m−1) ~ n^{m−1} / Γ(m). The ratio
C(n+m−1, m−1) · Γ(m) / n^{m−1} → 1 as n → ∞. -/

/-- Asymptotic ratio at n = 100 for poles of order 2, 3, 4. -/
theorem pole_asymptotic_ratio_n100 :
    (Nat.choose 101 1 : ℚ) * gammaPos 2 / 100 = 101/100 ∧
    (Nat.choose 102 2 : ℚ) * gammaPos 3 / 100 ^ 2 = 10302/10000 ∧
    (Nat.choose 103 3 : ℚ) * gammaPos 4 / 100 ^ 3 = 1061106/1000000 := by
  native_decide

/-- All ratios lie in (1, 11/10), confirming convergence to 1. -/
theorem pole_ratio_bounds_n100 :
    1 < (Nat.choose 101 1 : ℚ) * gammaPos 2 / 100 ∧
    (Nat.choose 101 1 : ℚ) * gammaPos 2 / 100 < 11/10 ∧
    1 < (Nat.choose 102 2 : ℚ) * gammaPos 3 / 100 ^ 2 ∧
    (Nat.choose 102 2 : ℚ) * gammaPos 3 / 100 ^ 2 < 11/10 ∧
    1 < (Nat.choose 103 3 : ℚ) * gammaPos 4 / 100 ^ 3 ∧
    (Nat.choose 103 3 : ℚ) * gammaPos 4 / 100 ^ 3 < 11/10 := by
  native_decide

/-- Transfer theorem normalization: 1/Γ(m) = 1/(m−1)!. -/
theorem transfer_normalization :
    1 / gammaPos 1 = 1 ∧ 1 / gammaPos 2 = 1 ∧
    1 / gammaPos 3 = 1/2 ∧ 1 / gammaPos 4 = 1/6 ∧
    1 / gammaPos 5 = 1/24 := by
  native_decide

/-! ## 7. Logarithmic singularity

[z^n] log(1/(1−z)) = 1/n for n ≥ 1.
[z^n] log²(1/(1−z)) = 2H_{n−1}/n where H_n = Σ_{k=1}^n 1/k. -/

/-- Harmonic number H_n. -/
def harmonicNum (n : ℕ) : ℚ := ∑ k ∈ range n, 1 / ((k + 1 : ℕ) : ℚ)

theorem harmonic_values :
    harmonicNum 1 = 1 ∧ harmonicNum 2 = 3/2 ∧
    harmonicNum 3 = 11/6 ∧ harmonicNum 4 = 25/12 ∧
    harmonicNum 5 = 137/60 := by
  native_decide

/-- [z^n] log²(1/(1−z)) = 2·H_{n−1}/n. -/
def logSquaredCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else 2 * harmonicNum (n - 1) / (n : ℚ)

theorem log_squared_values :
    logSquaredCoeff 0 = 0 ∧ logSquaredCoeff 1 = 0 ∧
    logSquaredCoeff 2 = 1 ∧ logSquaredCoeff 3 = 1 ∧
    logSquaredCoeff 4 = 11/12 ∧ logSquaredCoeff 5 = 5/6 := by
  native_decide

/-- Convolution check: 2H_{n−1}/n = Σ_{k=1}^{n−1} 1/(k(n−k)). -/
def logSquaredConv (n : ℕ) : ℚ :=
  ∑ k ∈ Icc 1 (n - 1), 1 / ((k : ℚ) * ((n - k : ℕ) : ℚ))

theorem log_squared_convolution_match :
    ∀ n ∈ Icc 2 10, logSquaredCoeff n = logSquaredConv n := by
  native_decide


structure SingularityExponentsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityExponentsBudgetCertificate.controlled
    (c : SingularityExponentsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SingularityExponentsBudgetCertificate.budgetControlled
    (c : SingularityExponentsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SingularityExponentsBudgetCertificate.Ready
    (c : SingularityExponentsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularityExponentsBudgetCertificate.size
    (c : SingularityExponentsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem singularityExponents_budgetCertificate_le_size
    (c : SingularityExponentsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularityExponentsBudgetCertificate :
    SingularityExponentsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSingularityExponentsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityExponentsBudgetCertificate.controlled,
      sampleSingularityExponentsBudgetCertificate]
  · norm_num [SingularityExponentsBudgetCertificate.budgetControlled,
      sampleSingularityExponentsBudgetCertificate]

example :
    sampleSingularityExponentsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityExponentsBudgetCertificate.size := by
  apply singularityExponents_budgetCertificate_le_size
  constructor
  · norm_num [SingularityExponentsBudgetCertificate.controlled,
      sampleSingularityExponentsBudgetCertificate]
  · norm_num [SingularityExponentsBudgetCertificate.budgetControlled,
      sampleSingularityExponentsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularityExponentsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityExponentsBudgetCertificate.controlled,
      sampleSingularityExponentsBudgetCertificate]
  · norm_num [SingularityExponentsBudgetCertificate.budgetControlled,
      sampleSingularityExponentsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularityExponentsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityExponentsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SingularityExponentsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularityExponentsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSingularityExponentsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.SingularityExponents
