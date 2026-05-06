/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Asymptotic Expansions

  Verified numerical identities related to:
  • Geometric series partial sums
  • Power sum formulas
  • Harmonic numbers (rational arithmetic)
  • Exponential generating function coefficients
  • Coefficient growth rates (dominant singularity)
  • Transfer matrix method / Fibonacci recurrence
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.AsymptoticExpansions
/-! ## 1. Geometric series partial sums

  Σ_{k=0}^{n-1} r^k = (r^n - 1)/(r - 1) for r ≠ 1.
  We verify instances in ℕ. -/

/-- Σ_{k=0}^{9} 2^k = 2^10 - 1 = 1023. -/
example : ∑ k ∈ Finset.range 10, 2 ^ k = 2 ^ 10 - 1 := by native_decide

/-- Σ_{k=0}^{7} 3^k = (3^8 - 1) / 2 = 3280. -/
example : ∑ k ∈ Finset.range 8, 3 ^ k = (3 ^ 8 - 1) / 2 := by native_decide

/-- Geometric series n=1..10 for base 2. -/
example : ∑ k ∈ Finset.range 1, 2 ^ k = 2 ^ 1 - 1 := by native_decide
example : ∑ k ∈ Finset.range 2, 2 ^ k = 2 ^ 2 - 1 := by native_decide
example : ∑ k ∈ Finset.range 3, 2 ^ k = 2 ^ 3 - 1 := by native_decide
example : ∑ k ∈ Finset.range 4, 2 ^ k = 2 ^ 4 - 1 := by native_decide
example : ∑ k ∈ Finset.range 5, 2 ^ k = 2 ^ 5 - 1 := by native_decide
example : ∑ k ∈ Finset.range 6, 2 ^ k = 2 ^ 6 - 1 := by native_decide
example : ∑ k ∈ Finset.range 7, 2 ^ k = 2 ^ 7 - 1 := by native_decide
example : ∑ k ∈ Finset.range 8, 2 ^ k = 2 ^ 8 - 1 := by native_decide
example : ∑ k ∈ Finset.range 9, 2 ^ k = 2 ^ 9 - 1 := by native_decide

/-- Geometric series n=1..8 for base 3. -/
example : ∑ k ∈ Finset.range 1, 3 ^ k = (3 ^ 1 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 2, 3 ^ k = (3 ^ 2 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 3, 3 ^ k = (3 ^ 3 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 4, 3 ^ k = (3 ^ 4 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 5, 3 ^ k = (3 ^ 5 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 6, 3 ^ k = (3 ^ 6 - 1) / 2 := by native_decide
example : ∑ k ∈ Finset.range 7, 3 ^ k = (3 ^ 7 - 1) / 2 := by native_decide

/-! ## 2. Power sum formulas

  Σ_{k=1}^n k = n(n+1)/2,
  Σ_{k=1}^n k^2 = n(n+1)(2n+1)/6,
  Σ_{k=1}^n k^3 = (n(n+1)/2)^2. -/

/-- Σ_{k=1}^{20} k = 20*21/2 = 210. -/
example : ∑ k ∈ Finset.range 20, (k + 1) = 20 * 21 / 2 := by native_decide

/-- Verify Σ k for several n. -/
example : ∑ k ∈ Finset.range 1, (k + 1) = 1 * 2 / 2 := by native_decide
example : ∑ k ∈ Finset.range 5, (k + 1) = 5 * 6 / 2 := by native_decide
example : ∑ k ∈ Finset.range 10, (k + 1) = 10 * 11 / 2 := by native_decide
example : ∑ k ∈ Finset.range 15, (k + 1) = 15 * 16 / 2 := by native_decide

/-- Σ_{k=1}^{12} k^2 = 12*13*25/6 = 650. -/
example : ∑ k ∈ Finset.range 12, (k + 1) ^ 2 = 12 * 13 * 25 / 6 := by native_decide

/-- Verify Σ k^2 for several n. -/
example : ∑ k ∈ Finset.range 1, (k + 1) ^ 2 = 1 * 2 * 3 / 6 := by native_decide
example : ∑ k ∈ Finset.range 5, (k + 1) ^ 2 = 5 * 6 * 11 / 6 := by native_decide
example : ∑ k ∈ Finset.range 10, (k + 1) ^ 2 = 10 * 11 * 21 / 6 := by native_decide

/-- Σ_{k=1}^{10} k^3 = (10*11/2)^2 = 3025. -/
example : ∑ k ∈ Finset.range 10, (k + 1) ^ 3 = (10 * 11 / 2) ^ 2 := by native_decide

/-- Verify Σ k^3 for several n. -/
example : ∑ k ∈ Finset.range 1, (k + 1) ^ 3 = (1 * 2 / 2) ^ 2 := by native_decide
example : ∑ k ∈ Finset.range 5, (k + 1) ^ 3 = (5 * 6 / 2) ^ 2 := by native_decide
example : ∑ k ∈ Finset.range 8, (k + 1) ^ 3 = (8 * 9 / 2) ^ 2 := by native_decide

/-! ## 3. Harmonic number bounds

  H_n = Σ_{k=1}^n 1/k.
  We work in ℚ for exact arithmetic. -/

/-- Rational harmonic number. -/
def harmonicRat (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

/-- H_10 = 7381/2520. -/
example : harmonicRat 10 = 7381 / 2520 := by native_decide

/-- H_10 > 8/3 (i.e., 7381*3 > 2520*8). -/
example : harmonicRat 10 > 8 / 3 := by native_decide

/-- H_5 = 137/60. -/
example : harmonicRat 5 = 137 / 60 := by native_decide

/-- H_1 = 1. -/
example : harmonicRat 1 = 1 := by native_decide

/-- H_n > 0 for n ≥ 1 (spot checks). -/
example : harmonicRat 1 > 0 := by native_decide
example : harmonicRat 5 > 0 := by native_decide
example : harmonicRat 10 > 0 := by native_decide

/-! ## 4. Exponential generating function coefficients

  [z^n/n!] e^{az} = a^n. So [z^n] e^z = 1/n!.
  We verify power-of-2 values (from e^{2z}). -/

example : (2 : ℕ) ^ 0 = 1 := by native_decide
example : (2 : ℕ) ^ 1 = 2 := by native_decide
example : (2 : ℕ) ^ 2 = 4 := by native_decide
example : (2 : ℕ) ^ 3 = 8 := by native_decide
example : (2 : ℕ) ^ 4 = 16 := by native_decide
example : (2 : ℕ) ^ 5 = 32 := by native_decide
example : (2 : ℕ) ^ 6 = 64 := by native_decide
example : (2 : ℕ) ^ 7 = 128 := by native_decide
example : (2 : ℕ) ^ 8 = 256 := by native_decide

/-- Factorial values (denominators of [z^n] e^z = 1/n!). -/
example : Nat.factorial 0 = 1 := by native_decide
example : Nat.factorial 5 = 120 := by native_decide
example : Nat.factorial 8 = 40320 := by native_decide
example : Nat.factorial 10 = 3628800 := by native_decide

/-! ## 5. Coefficient growth rates (dominant singularity)

  For f(z) = 1/((1-z)(1-2z)): [z^n]f = 2^{n+1} - 1.
  Growth ratio → 2 as n → ∞. -/

/-- [z^n] 1/((1-z)(1-2z)) = 2^{n+1} - 1. Spot checks. -/
example : 2 ^ 1 - 1 = (1 : ℕ) := by native_decide
example : 2 ^ 2 - 1 = (3 : ℕ) := by native_decide
example : 2 ^ 3 - 1 = (7 : ℕ) := by native_decide
example : 2 ^ 4 - 1 = (15 : ℕ) := by native_decide
example : 2 ^ 5 - 1 = (31 : ℕ) := by native_decide
example : 2 ^ 10 - 1 = (1023 : ℕ) := by native_decide

/-- 2^{n+1}-1 > 2*(2^n - 1) for n ≥ 1 (coefficient dominance). -/
example : 2 ^ 11 - 1 > 2 * (2 ^ 10 - 1) := by native_decide
example : 2 ^ 6 - 1 > 2 * (2 ^ 5 - 1) := by native_decide
example : 2 ^ 3 - 1 > 2 * (2 ^ 2 - 1) := by native_decide

/-- Growth ratio approaches 2: (2^11-1)/(2^10-1) = 2047/1023 in ℚ. -/
example : (2 ^ 11 - 1 : ℚ) / (2 ^ 10 - 1) = 2047 / 1023 := by native_decide

/-- The ratio exceeds 2 (approaches from above). -/
example : (2047 : ℚ) / 1023 > 2 := by native_decide

/-- The ratio is greater than 1 (exponential growth). -/
example : (2047 : ℚ) / 1023 > 1 := by native_decide

/-! ## 6. Transfer matrix method / Fibonacci recurrence

  Strings over {0,1} avoiding "11" are counted by Fibonacci numbers.
  Transfer matrix [[1,1],[1,0]] has trace 1, det -1, char poly λ²-λ-1. -/

/-- Fibonacci recurrence: fib(n+2) = fib(n+1) + fib(n). -/
example : Nat.fib 2 = Nat.fib 1 + Nat.fib 0 := by native_decide
example : Nat.fib 3 = Nat.fib 2 + Nat.fib 1 := by native_decide
example : Nat.fib 4 = Nat.fib 3 + Nat.fib 2 := by native_decide
example : Nat.fib 5 = Nat.fib 4 + Nat.fib 3 := by native_decide
example : Nat.fib 6 = Nat.fib 5 + Nat.fib 4 := by native_decide
example : Nat.fib 7 = Nat.fib 6 + Nat.fib 5 := by native_decide
example : Nat.fib 8 = Nat.fib 7 + Nat.fib 6 := by native_decide
example : Nat.fib 9 = Nat.fib 8 + Nat.fib 7 := by native_decide
example : Nat.fib 10 = Nat.fib 9 + Nat.fib 8 := by native_decide
example : Nat.fib 15 = Nat.fib 14 + Nat.fib 13 := by native_decide

/-- Fibonacci values (for reference). -/
example : Nat.fib 10 = 55 := by native_decide
example : Nat.fib 15 = 610 := by native_decide
example : Nat.fib 20 = 6765 := by native_decide

/-- Transfer matrix trace = 1 (sum of diagonal: 1+0). -/
example : 1 + 0 = (1 : ℕ) := by native_decide

/-- Transfer matrix det = -1 (in ℤ: 1*0 - 1*1 = -1). -/
example : (1 : ℤ) * 0 - 1 * 1 = -1 := by native_decide

/-- Cassini's identity: fib(n-1)*fib(n+1) - fib(n)^2 = (-1)^n.
    In ℕ, for odd n: fib(n)^2 = fib(n-1)*fib(n+1) + 1.
    For even n: fib(n-1)*fib(n+1) = fib(n)^2 + 1. -/
-- n=5 (odd): fib(5)^2 = fib(4)*fib(6) + 1, i.e. 25 = 24 + 1
example : Nat.fib 5 ^ 2 = Nat.fib 4 * Nat.fib 6 + 1 := by native_decide
-- n=6 (even): fib(5)*fib(7) = fib(6)^2 + 1, i.e. 65 = 64 + 1
example : Nat.fib 5 * Nat.fib 7 = Nat.fib 6 ^ 2 + 1 := by native_decide
-- n=7 (odd): fib(7)^2 = fib(6)*fib(8) + 1, i.e. 169 = 168 + 1
example : Nat.fib 7 ^ 2 = Nat.fib 6 * Nat.fib 8 + 1 := by native_decide
-- n=8 (even): fib(7)*fib(9) = fib(8)^2 + 1, i.e. 442 = 441 + 1
example : Nat.fib 7 * Nat.fib 9 = Nat.fib 8 ^ 2 + 1 := by native_decide
-- n=10 (even): fib(9)*fib(11) = fib(10)^2 + 1, i.e. 3026 = 3025 + 1
example : Nat.fib 9 * Nat.fib 11 = Nat.fib 10 ^ 2 + 1 := by native_decide

/-- Finite geometric prefix used in elementary asymptotic expansions. -/
def geometricPrefix (base n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, base ^ k

theorem geometricPrefix_two_ten :
    geometricPrefix 2 10 = 1023 := by
  native_decide

/-- Dominant coefficient model for `1 / ((1 - z) * (1 - 2z))`. -/
def dominantTwoPoleCoeff (n : ℕ) : ℕ :=
  2 ^ (n + 1) - 1

theorem dominantTwoPoleCoeff_nine :
    dominantTwoPoleCoeff 9 = 1023 := by
  native_decide


structure AsymptoticExpansionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AsymptoticExpansionsBudgetCertificate.controlled
    (c : AsymptoticExpansionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AsymptoticExpansionsBudgetCertificate.budgetControlled
    (c : AsymptoticExpansionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AsymptoticExpansionsBudgetCertificate.Ready
    (c : AsymptoticExpansionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AsymptoticExpansionsBudgetCertificate.size
    (c : AsymptoticExpansionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem asymptoticExpansions_budgetCertificate_le_size
    (c : AsymptoticExpansionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAsymptoticExpansionsBudgetCertificate :
    AsymptoticExpansionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAsymptoticExpansionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticExpansionsBudgetCertificate.controlled,
      sampleAsymptoticExpansionsBudgetCertificate]
  · norm_num [AsymptoticExpansionsBudgetCertificate.budgetControlled,
      sampleAsymptoticExpansionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAsymptoticExpansionsBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticExpansionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAsymptoticExpansionsBudgetCertificate.Ready := by
  constructor
  · norm_num [AsymptoticExpansionsBudgetCertificate.controlled,
      sampleAsymptoticExpansionsBudgetCertificate]
  · norm_num [AsymptoticExpansionsBudgetCertificate.budgetControlled,
      sampleAsymptoticExpansionsBudgetCertificate]

example :
    sampleAsymptoticExpansionsBudgetCertificate.certificateBudgetWindow ≤
      sampleAsymptoticExpansionsBudgetCertificate.size := by
  apply asymptoticExpansions_budgetCertificate_le_size
  constructor
  · norm_num [AsymptoticExpansionsBudgetCertificate.controlled,
      sampleAsymptoticExpansionsBudgetCertificate]
  · norm_num [AsymptoticExpansionsBudgetCertificate.budgetControlled,
      sampleAsymptoticExpansionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AsymptoticExpansionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAsymptoticExpansionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAsymptoticExpansionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.AsymptoticExpansions
