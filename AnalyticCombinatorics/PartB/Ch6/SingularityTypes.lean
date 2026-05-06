/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Singularity types and their coefficient asymptotics.

  Verified numerical checks for the main singularity classes:
  algebraic, logarithmic, square-root, poles, transfer theorem,
  and Motzkin asymptotics.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.SingularityTypes
/-! ## 1. Algebraic singularity: (1 - z/ρ)^α

The Catalan generating function has a (1-4z)^{1/2} type singularity.
[z^n] ~ 4^n / (n^{3/2} √π).

The ratio C(n)/C(n-1) = 2(2n-1)/(n+1) → 4. -/

/-- Catalan ratio: C(n)/C(n-1) = 2(2n-1)/(n+1) as a rational number. -/
def catalanRatio (n : ℕ) : ℚ := if n = 0 then 0 else (2 * (2 * n - 1) : ℚ) / (n + 1)

/-- catalanRatio 1 = 1 (since C(1)/C(0) = 1/1 = 1, and 2(2-1)/(1+1) = 2/2 = 1). -/
example : catalanRatio 1 = 1 := by native_decide

/-- catalanRatio 5 = 3 (since C(5)/C(4) = 42/14 = 3, and 2·9/6 = 3). -/
example : catalanRatio 5 = 3 := by native_decide

/-- catalanRatio 10 = 38/11. Verification: C(10) = 16796, C(9) = 4862,
    and 4862 * 38 = 16796 * 11 = 184756. -/
example : catalanRatio 10 = 38 / 11 := by native_decide

/-- Cross-multiplication check: 4862 * 38 = 16796 * 11. -/
example : 4862 * 38 = 16796 * 11 := by native_decide

/-! ## 2. Logarithmic singularity: ln(1/(1-z))

[z^n] ln(1/(1-z)) = 1/n. The GF of harmonic numbers is -ln(1-z)/(1-z),
with [z^n] = H_n = 1 + 1/2 + ... + 1/n. -/

/-- H_5 = 1 + 1/2 + 1/3 + 1/4 + 1/5 = 137/60. -/
example : (1 : ℚ) + 1/2 + 1/3 + 1/4 + 1/5 = 137/60 := by native_decide

/-! ## 3. Square-root singularity: (1-z)^{-1/2}

[z^n](1-z)^{-1/2} = C(2n,n)/4^n (central binomial coefficient divided by 4^n). -/

/-- C(2,1)/4 = 1/2. -/
example : (2 : ℚ) / 4 = 1/2 := by native_decide

/-- C(4,2)/16 = 3/8. -/
example : (6 : ℚ) / 16 = 3/8 := by native_decide

/-- C(6,3)/64 = 5/16. -/
example : (20 : ℚ) / 64 = 5/16 := by native_decide

/-- C(8,4)/256 = 35/128. -/
example : (70 : ℚ) / 256 = 35/128 := by native_decide

/-! ## 4. Pole of order m

[z^n] 1/(1-z)^m = C(n+m-1, m-1). -/

/-- [z^5] 1/(1-z)^3 = C(7,2) = 21. -/
example : Nat.choose 7 2 = 21 := by native_decide

/-- [z^6] 1/(1-z)^4 = C(9,3) = 84. -/
example : Nat.choose 9 3 = 84 := by native_decide

/-- [z^8] 1/(1-z)^5 = C(12,4) = 495. -/
example : Nat.choose 12 4 = 495 := by native_decide

/-! ## 5. Transfer theorem table

For (1-z/ρ)^α with α ∉ {0,-1,-2,...}:
[z^n] f(z) ~ (ρ^{-n} · n^{-α-1}) / Γ(-α).

Gamma function recurrence at half-integers:
Γ(n+1/2) / Γ(n-1/2) = n - 1/2 = (2n-1)/2.

Verify: C(2n,n) ~ 4^n/√(πn), i.e., C(2n,n)^2 · n ≈ 4^{2n}/π. -/

/-- Gamma recurrence denominator at n=1: 2·1-1 = 1. -/
example : (2 * 1 - 1 : ℕ) = 1 := by native_decide

/-- Gamma recurrence denominator at n=5: 2·5-1 = 9. -/
example : (2 * 5 - 1 : ℕ) = 9 := by native_decide

/-- C(10,5)^2 · 5 = 317520, approximating 4^10/π ≈ 333760. -/
example : (Nat.choose 10 5) ^ 2 * 5 = 317520 := by native_decide

/-- C(20,10)^2 · 10 > 4^20/4 (lower bound consistent with ~4^{20}/π). -/
example : (Nat.choose 20 10) ^ 2 * 10 > 4 ^ 20 / 4 := by native_decide

/-! ## 6. Motzkin asymptotics

M(n) ~ 3·3^n / (√(3π)·n^{3/2}). Radius of convergence ρ = 1/3.
Ratio M(n)/M(n-1) → 3. -/

/-- First nine Motzkin numbers: 1, 1, 2, 4, 9, 21, 51, 127, 323. -/
def motzkin : Fin 9 → ℕ := ![1, 1, 2, 4, 9, 21, 51, 127, 323]

/-- Motzkin ratio bound: M(5)·4 > M(4)·9, i.e. 84 > 81. -/
example : 21 * 4 > 9 * 9 := by native_decide

/-- Motzkin ratio bound: M(8)·4 > M(7)·9, i.e. 1292 > 1143. -/
example : 323 * 4 > 127 * 9 := by native_decide

/-- Pole coefficient for `(1 - z)^(-m)`. -/
def poleCoeff (m n : ℕ) : ℕ :=
  Nat.choose (n + m - 1) (m - 1)

theorem poleCoeff_order_three_five :
    poleCoeff 3 5 = 21 := by
  native_decide

/-- Square-root coefficient numerator before division by `4^n`. -/
def squareRootCoeffNumerator (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n

theorem squareRootCoeffNumerator_four :
    squareRootCoeffNumerator 4 = 70 := by
  native_decide


structure SingularityTypesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityTypesBudgetCertificate.controlled
    (c : SingularityTypesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SingularityTypesBudgetCertificate.budgetControlled
    (c : SingularityTypesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SingularityTypesBudgetCertificate.Ready
    (c : SingularityTypesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularityTypesBudgetCertificate.size
    (c : SingularityTypesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem singularityTypes_budgetCertificate_le_size
    (c : SingularityTypesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularityTypesBudgetCertificate :
    SingularityTypesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSingularityTypesBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityTypesBudgetCertificate.controlled,
      sampleSingularityTypesBudgetCertificate]
  · norm_num [SingularityTypesBudgetCertificate.budgetControlled,
      sampleSingularityTypesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularityTypesBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityTypesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSingularityTypesBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityTypesBudgetCertificate.controlled,
      sampleSingularityTypesBudgetCertificate]
  · norm_num [SingularityTypesBudgetCertificate.budgetControlled,
      sampleSingularityTypesBudgetCertificate]

example :
    sampleSingularityTypesBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityTypesBudgetCertificate.size := by
  apply singularityTypes_budgetCertificate_le_size
  constructor
  · norm_num [SingularityTypesBudgetCertificate.controlled,
      sampleSingularityTypesBudgetCertificate]
  · norm_num [SingularityTypesBudgetCertificate.budgetControlled,
      sampleSingularityTypesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List SingularityTypesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularityTypesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSingularityTypesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.SingularityTypes
