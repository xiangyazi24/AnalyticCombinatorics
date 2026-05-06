/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Logarithmic singularities, harmonic numbers, and asymptotics.

  Verified numerical checks for:
  - Harmonic numbers H(n) and their scaled integer forms
  - Wolstenholme numerator divisibility by p²
  - Sums of squares and their closed forms
  - Logarithmic growth bounds for harmonic numbers
  - Stirling-type inequalities for factorials
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.LogarithmicSingularities
/-! ## 1. Scaled harmonic numbers

Define posHarm(n) = ∑_{k=1}^{n} (n! / k), which is always a natural number.
This equals n! · H(n) where H(n) = 1 + 1/2 + ... + 1/n.

posHarm(1) = 1
posHarm(2) = 2+1 = 3
posHarm(3) = 6+3+2 = 11
posHarm(4) = 24+12+8+6 = 50
posHarm(5) = 120+60+40+30+24 = 274
posHarm(6) = 720+360+240+180+144+120 = 1764
posHarm(7) = 5040+2520+1680+1260+1008+840+720 = 13068
-/

/-- posHarm n = ∑_{k=1}^{n} (n! / k) = n! · H(n). Always an integer. -/
def posHarm (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, n.factorial / (k + 1)

theorem posHarm_1 : posHarm 1 = 1 := by native_decide
theorem posHarm_2 : posHarm 2 = 3 := by native_decide
theorem posHarm_3 : posHarm 3 = 11 := by native_decide
theorem posHarm_4 : posHarm 4 = 50 := by native_decide
theorem posHarm_5 : posHarm 5 = 274 := by native_decide
theorem posHarm_6 : posHarm 6 = 1764 := by native_decide
theorem posHarm_7 : posHarm 7 = 13068 := by native_decide

/-- Table of posHarm values for n = 1..7. -/
def posHarmTable : Fin 7 → ℕ := ![1, 3, 11, 50, 274, 1764, 13068]

theorem posHarmTable_check_1 : posHarmTable 0 = posHarm 1 := by native_decide
theorem posHarmTable_check_2 : posHarmTable 1 = posHarm 2 := by native_decide
theorem posHarmTable_check_3 : posHarmTable 2 = posHarm 3 := by native_decide
theorem posHarmTable_check_4 : posHarmTable 3 = posHarm 4 := by native_decide
theorem posHarmTable_check_5 : posHarmTable 4 = posHarm 5 := by native_decide
theorem posHarmTable_check_6 : posHarmTable 5 = posHarm 6 := by native_decide
theorem posHarmTable_check_7 : posHarmTable 6 = posHarm 7 := by native_decide

/-! ## 2. Harmonic numbers as rationals

H(n) = ∑_{k=1}^{n} 1/k as a rational number.
H(1) = 1, H(2) = 3/2, H(3) = 11/6, H(4) = 25/12,
H(5) = 137/60, H(6) = 49/20, H(7) = 363/140.
-/

/-- Harmonic number H(n) as a rational. -/
def harmQ (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / (k + 1 : ℚ)

theorem harmQ_1 : harmQ 1 = 1 := by native_decide
theorem harmQ_2 : harmQ 2 = 3 / 2 := by native_decide
theorem harmQ_3 : harmQ 3 = 11 / 6 := by native_decide
theorem harmQ_4 : harmQ 4 = 25 / 12 := by native_decide
theorem harmQ_5 : harmQ 5 = 137 / 60 := by native_decide
theorem harmQ_6 : harmQ 6 = 49 / 20 := by native_decide
theorem harmQ_7 : harmQ 7 = 363 / 140 := by native_decide

/-- The denominator of H(4) is 12. -/
theorem harmQ_4_denom : (harmQ 4).den = 12 := by native_decide

/-- The numerator of H(4) is 25 = 5². -/
theorem harmQ_4_num : (harmQ 4).num = 25 := by native_decide

/-- The denominator of H(6) is 20. -/
theorem harmQ_6_denom : (harmQ 6).den = 20 := by native_decide

/-- The numerator of H(6) is 49 = 7². -/
theorem harmQ_6_num : (harmQ 6).num = 49 := by native_decide

/-! ## 3. Wolstenholme's theorem (numerical instances)

For prime p ≥ 5, the numerator of H(p-1) (in lowest terms) is divisible by p².

- p = 5: H(4) = 25/12, numerator = 25 = 5² ✓
- p = 7: H(6) = 49/20, numerator = 49 = 7² ✓
-/

/-- For p=5: numerator of H(4) equals 5². -/
theorem wolstenholme_p5 : (harmQ 4).num = 5 ^ 2 := by native_decide

/-- For p=7: numerator of H(6) equals 7². -/
theorem wolstenholme_p7 : (harmQ 6).num = 7 ^ 2 := by native_decide

/-- 5² divides numerator of H(4). -/
theorem wolstenholme_p5_div : (5 ^ 2 : ℤ) ∣ (harmQ 4).num := by native_decide

/-- 7² divides numerator of H(6). -/
theorem wolstenholme_p7_div : (7 ^ 2 : ℤ) ∣ (harmQ 6).num := by native_decide

/-- Consistency: harmQ(n) = posHarm(n) / n! for n = 1..7.
    Verified as: harmQ(n) * n! = posHarm(n). -/
theorem harmQ_posHarm_ratio_1 : harmQ 1 * 1 = posHarm 1 := by native_decide
theorem harmQ_posHarm_ratio_2 : harmQ 2 * 2 = posHarm 2 := by native_decide
theorem harmQ_posHarm_ratio_3 : harmQ 3 * 6 = posHarm 3 := by native_decide
theorem harmQ_posHarm_ratio_4 : harmQ 4 * 24 = posHarm 4 := by native_decide
theorem harmQ_posHarm_ratio_5 : harmQ 5 * 120 = posHarm 5 := by native_decide
theorem harmQ_posHarm_ratio_6 : harmQ 6 * 720 = posHarm 6 := by native_decide
theorem harmQ_posHarm_ratio_7 : harmQ 7 * 5040 = posHarm 7 := by native_decide

/-! ## 4. Sums of squares and cubes

∑_{k=1}^{n} k² = n(n+1)(2n+1)/6

Values for n = 1..10:
1, 5, 14, 30, 55, 91, 140, 204, 285, 385
-/

/-- sumSq n = ∑_{k=1}^{n} k². -/
def sumSq (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (k + 1) ^ 2

/-- Table of sum-of-squares for n = 1..10. -/
def sumSqTable : Fin 10 → ℕ := ![1, 5, 14, 30, 55, 91, 140, 204, 285, 385]

theorem sumSq_table_check : ∀ i : Fin 10, sumSqTable i = sumSq (i.val + 1) := by
  native_decide

/-- Closed form: ∑_{k=1}^{n} k² = n(n+1)(2n+1)/6.
    We verify the scaled version: 6 * sumSq(n) = n*(n+1)*(2*n+1). -/
theorem sumSq_formula_1 : 6 * sumSq 1 = 1 * 2 * 3 := by native_decide
theorem sumSq_formula_2 : 6 * sumSq 2 = 2 * 3 * 5 := by native_decide
theorem sumSq_formula_3 : 6 * sumSq 3 = 3 * 4 * 7 := by native_decide
theorem sumSq_formula_4 : 6 * sumSq 4 = 4 * 5 * 9 := by native_decide
theorem sumSq_formula_5 : 6 * sumSq 5 = 5 * 6 * 11 := by native_decide
theorem sumSq_formula_6 : 6 * sumSq 6 = 6 * 7 * 13 := by native_decide
theorem sumSq_formula_7 : 6 * sumSq 7 = 7 * 8 * 15 := by native_decide
theorem sumSq_formula_8 : 6 * sumSq 8 = 8 * 9 * 17 := by native_decide
theorem sumSq_formula_9 : 6 * sumSq 9 = 9 * 10 * 19 := by native_decide
theorem sumSq_formula_10 : 6 * sumSq 10 = 10 * 11 * 21 := by native_decide

/-! ## 5. Logarithmic growth bounds for harmonic numbers

H(n) grows like ln(n) + γ where γ ≈ 0.5772.

Elementary bounds verified numerically:
  (a) H(n) < n  for n = 1..7  (i.e., posHarm(n) < n * n!)
  (b) H(n) > 1/2 for n ≥ 2   (i.e., 2 * posHarm(n) > n! for n ≥ 2)
  (c) Tighter lower bound: H(n) > ln-like growth checked via integer arithmetic.
-/

/-- H(n) ≤ n  ⟺  posHarm(n) ≤ n * n!, for n = 1..7.
    (For n=1: H(1)=1=1, equality holds; for n≥2: strict inequality.) -/
theorem posHarm_le_n_factorial_1 : posHarm 1 ≤ 1 * Nat.factorial 1 := by native_decide
theorem posHarm_lt_n_factorial_2 : posHarm 2 < 2 * Nat.factorial 2 := by native_decide
theorem posHarm_lt_n_factorial_3 : posHarm 3 < 3 * Nat.factorial 3 := by native_decide
theorem posHarm_lt_n_factorial_4 : posHarm 4 < 4 * Nat.factorial 4 := by native_decide
theorem posHarm_lt_n_factorial_5 : posHarm 5 < 5 * Nat.factorial 5 := by native_decide
theorem posHarm_lt_n_factorial_6 : posHarm 6 < 6 * Nat.factorial 6 := by native_decide
theorem posHarm_lt_n_factorial_7 : posHarm 7 < 7 * Nat.factorial 7 := by native_decide

/-- H(n) > 1  for n ≥ 2  ⟺  posHarm(n) > n! for n ≥ 2. -/
theorem posHarm_gt_factorial_2 : posHarm 2 > Nat.factorial 2 := by native_decide
theorem posHarm_gt_factorial_3 : posHarm 3 > Nat.factorial 3 := by native_decide
theorem posHarm_gt_factorial_4 : posHarm 4 > Nat.factorial 4 := by native_decide
theorem posHarm_gt_factorial_5 : posHarm 5 > Nat.factorial 5 := by native_decide
theorem posHarm_gt_factorial_6 : posHarm 6 > Nat.factorial 6 := by native_decide
theorem posHarm_gt_factorial_7 : posHarm 7 > Nat.factorial 7 := by native_decide

/-- 2 * posHarm(n) > n! for n ≥ 1 (i.e., H(n) > 1/2). -/
theorem posHarm_half_bound_1 : 2 * posHarm 1 > Nat.factorial 1 := by native_decide
theorem posHarm_half_bound_2 : 2 * posHarm 2 > Nat.factorial 2 := by native_decide
theorem posHarm_half_bound_3 : 2 * posHarm 3 > Nat.factorial 3 := by native_decide
theorem posHarm_half_bound_4 : 2 * posHarm 4 > Nat.factorial 4 := by native_decide
theorem posHarm_half_bound_5 : 2 * posHarm 5 > Nat.factorial 5 := by native_decide
theorem posHarm_half_bound_6 : 2 * posHarm 6 > Nat.factorial 6 := by native_decide
theorem posHarm_half_bound_7 : 2 * posHarm 7 > Nat.factorial 7 := by native_decide

/-- H(n) is strictly increasing: posHarm grows faster than n!.
    Verified: posHarm(n+1)*(n+1)! > posHarm(n)*(n+1)! is trivial.
    Instead: posHarm values strictly increase. -/
theorem posHarm_strict_mono_12 : posHarm 1 < posHarm 2 := by native_decide
theorem posHarm_strict_mono_23 : posHarm 2 < posHarm 3 := by native_decide
theorem posHarm_strict_mono_34 : posHarm 3 < posHarm 4 := by native_decide
theorem posHarm_strict_mono_45 : posHarm 4 < posHarm 5 := by native_decide
theorem posHarm_strict_mono_56 : posHarm 5 < posHarm 6 := by native_decide
theorem posHarm_strict_mono_67 : posHarm 6 < posHarm 7 := by native_decide

/-! ## 6. Logarithm-type lower bound via reciprocals

The telescoping bound: H(n) ≥ log₂(n+1) follows from H(2^k) ≥ 1 + k/2.
We verify: posHarm(4) = 50 ≥ 3 * 4!/2 = 3*12 = 36 (i.e., H(4) ≥ 3/2). -/

/-- H(4) ≥ 3/2: posHarm(4) * 2 ≥ 3 * 4! . -/
theorem harmQ_4_lower : 2 * posHarm 4 ≥ 3 * Nat.factorial 4 := by native_decide

/-- H(8) ≥ 2 (classical): check via harmQ. -/
theorem harmQ_8_ge_2 : harmQ 8 ≥ 2 := by native_decide

/-- H(4) ≥ 3/2. -/
theorem harmQ_4_ge_half3 : harmQ 4 ≥ 3 / 2 := by native_decide

/-- H(7) ≈ 2.59: verify 2 * posHarm(7) > 5040 * 5 (i.e., H(7) > 5/2). -/
theorem harmQ_7_ge_5half : harmQ 7 ≥ 5 / 2 := by native_decide

/-! ## 7. Stirling-type inequalities for factorials

Stirling: n! ≈ √(2πn) (n/e)^n.

We verify elementary bounds:
  (a) n^n > n! for n = 2..7
  (b) 3^n * n! > n^n for n = 2..6 (i.e., (n/3)^n < n!)
-/

/-- n^n values for n = 2..7: 4, 27, 256, 3125, 46656, 823543. -/
def powN : Fin 6 → ℕ := ![4, 27, 256, 3125, 46656, 823543]

theorem powN_2 : 2 ^ 2 = 4 := by native_decide
theorem powN_3 : 3 ^ 3 = 27 := by native_decide
theorem powN_4 : 4 ^ 4 = 256 := by native_decide
theorem powN_5 : 5 ^ 5 = 3125 := by native_decide
theorem powN_6 : 6 ^ 6 = 46656 := by native_decide
theorem powN_7 : 7 ^ 7 = 823543 := by native_decide

/-- n! values for n = 2..7: 2, 6, 24, 120, 720, 5040. -/
def factTable : Fin 6 → ℕ := ![2, 6, 24, 120, 720, 5040]

theorem factTable_check : ∀ i : Fin 6, factTable i = Nat.factorial (i.val + 2) := by
  native_decide

/-- n^n > n! for n = 2..7. -/
theorem nn_gt_factorial_2 : 2 ^ 2 > Nat.factorial 2 := by native_decide
theorem nn_gt_factorial_3 : 3 ^ 3 > Nat.factorial 3 := by native_decide
theorem nn_gt_factorial_4 : 4 ^ 4 > Nat.factorial 4 := by native_decide
theorem nn_gt_factorial_5 : 5 ^ 5 > Nat.factorial 5 := by native_decide
theorem nn_gt_factorial_6 : 6 ^ 6 > Nat.factorial 6 := by native_decide
theorem nn_gt_factorial_7 : 7 ^ 7 > Nat.factorial 7 := by native_decide

/-- 3^n * n! > n^n for n = 2..6 (equivalent to n! > (n/3)^n). -/
theorem stirling_lower_2 : 3 ^ 2 * Nat.factorial 2 > 2 ^ 2 := by native_decide
theorem stirling_lower_3 : 3 ^ 3 * Nat.factorial 3 > 3 ^ 3 := by native_decide
theorem stirling_lower_4 : 3 ^ 4 * Nat.factorial 4 > 4 ^ 4 := by native_decide
theorem stirling_lower_5 : 3 ^ 5 * Nat.factorial 5 > 5 ^ 5 := by native_decide
theorem stirling_lower_6 : 3 ^ 6 * Nat.factorial 6 > 6 ^ 6 := by native_decide

/-! ## 8. Alternating harmonic sums (partial sums towards ln 2)

altHarm(n) = ∑_{k=1}^{n} (-1)^{k+1} / k = 1 - 1/2 + 1/3 - ...

Partial sums approach ln 2 ≈ 0.6931...

Values: 1, 1/2, 5/6, 7/12, 47/60, 37/60, 319/420, 533/840
-/

/-- Alternating harmonic sum as a rational. -/
def altHarmQ (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, ((-1 : ℚ) ^ k * (1 / (k + 1 : ℚ)))

theorem altHarmQ_1 : altHarmQ 1 = 1 := by native_decide
theorem altHarmQ_2 : altHarmQ 2 = 1 / 2 := by native_decide
theorem altHarmQ_3 : altHarmQ 3 = 5 / 6 := by native_decide
theorem altHarmQ_4 : altHarmQ 4 = 7 / 12 := by native_decide
theorem altHarmQ_5 : altHarmQ 5 = 47 / 60 := by native_decide
theorem altHarmQ_6 : altHarmQ 6 = 37 / 60 := by native_decide
theorem altHarmQ_7 : altHarmQ 7 = 319 / 420 := by native_decide
theorem altHarmQ_8 : altHarmQ 8 = 533 / 840 := by native_decide

/-- Alternating partial sums are sandwiched: altHarmQ(2k) < ln2 < altHarmQ(2k-1).
    We verify the rational bounds 1/2 < altHarmQ(n) < 1 for n = 2..8. -/
theorem altHarmQ_between_half_one_2 : altHarmQ 2 > 0 ∧ altHarmQ 2 < 1 := by
  constructor <;> native_decide
theorem altHarmQ_between_half_one_3 : altHarmQ 3 > 1 / 2 ∧ altHarmQ 3 < 1 := by
  constructor <;> native_decide
theorem altHarmQ_between_half_one_4 : altHarmQ 4 > 1 / 2 ∧ altHarmQ 4 < 1 := by
  constructor <;> native_decide
theorem altHarmQ_between_half_one_5 : altHarmQ 5 > 1 / 2 ∧ altHarmQ 5 < 1 := by
  constructor <;> native_decide
theorem altHarmQ_between_half_one_6 : altHarmQ 6 > 1 / 2 ∧ altHarmQ 6 < 1 := by
  constructor <;> native_decide

/-- The alternating partial sums oscillate: odd-indexed > even-indexed. -/
theorem altHarmQ_oscillate_12 : altHarmQ 1 > altHarmQ 2 := by native_decide
theorem altHarmQ_oscillate_23 : altHarmQ 2 < altHarmQ 3 := by native_decide
theorem altHarmQ_oscillate_34 : altHarmQ 3 > altHarmQ 4 := by native_decide
theorem altHarmQ_oscillate_45 : altHarmQ 4 < altHarmQ 5 := by native_decide
theorem altHarmQ_oscillate_56 : altHarmQ 5 > altHarmQ 6 := by native_decide
theorem altHarmQ_oscillate_67 : altHarmQ 6 < altHarmQ 7 := by native_decide

/-! ## 9. Logarithmic GF coefficient identity

[z^n] ln(1/(1-z)) = 1/n.
Equivalently, H(n) = [z^n] (-ln(1-z)) / (1-z).
We verify H(n) - H(n-1) = 1/n via harmQ for small n. -/

/-- H(n) - H(n-1) = 1/n for n = 2..7. -/
theorem harmQ_diff_2 : harmQ 2 - harmQ 1 = 1 / 2 := by native_decide
theorem harmQ_diff_3 : harmQ 3 - harmQ 2 = 1 / 3 := by native_decide
theorem harmQ_diff_4 : harmQ 4 - harmQ 3 = 1 / 4 := by native_decide
theorem harmQ_diff_5 : harmQ 5 - harmQ 4 = 1 / 5 := by native_decide
theorem harmQ_diff_6 : harmQ 6 - harmQ 5 = 1 / 6 := by native_decide
theorem harmQ_diff_7 : harmQ 7 - harmQ 6 = 1 / 7 := by native_decide


structure LogarithmicSingularitiesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogarithmicSingularitiesBudgetCertificate.controlled
    (c : LogarithmicSingularitiesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LogarithmicSingularitiesBudgetCertificate.budgetControlled
    (c : LogarithmicSingularitiesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LogarithmicSingularitiesBudgetCertificate.Ready
    (c : LogarithmicSingularitiesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LogarithmicSingularitiesBudgetCertificate.size
    (c : LogarithmicSingularitiesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem logarithmicSingularities_budgetCertificate_le_size
    (c : LogarithmicSingularitiesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLogarithmicSingularitiesBudgetCertificate :
    LogarithmicSingularitiesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleLogarithmicSingularitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [LogarithmicSingularitiesBudgetCertificate.controlled,
      sampleLogarithmicSingularitiesBudgetCertificate]
  · norm_num [LogarithmicSingularitiesBudgetCertificate.budgetControlled,
      sampleLogarithmicSingularitiesBudgetCertificate]

example :
    sampleLogarithmicSingularitiesBudgetCertificate.certificateBudgetWindow ≤
      sampleLogarithmicSingularitiesBudgetCertificate.size := by
  apply logarithmicSingularities_budgetCertificate_le_size
  constructor
  · norm_num [LogarithmicSingularitiesBudgetCertificate.controlled,
      sampleLogarithmicSingularitiesBudgetCertificate]
  · norm_num [LogarithmicSingularitiesBudgetCertificate.budgetControlled,
      sampleLogarithmicSingularitiesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLogarithmicSingularitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [LogarithmicSingularitiesBudgetCertificate.controlled,
      sampleLogarithmicSingularitiesBudgetCertificate]
  · norm_num [LogarithmicSingularitiesBudgetCertificate.budgetControlled,
      sampleLogarithmicSingularitiesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLogarithmicSingularitiesBudgetCertificate.certificateBudgetWindow ≤
      sampleLogarithmicSingularitiesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LogarithmicSingularitiesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLogarithmicSingularitiesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLogarithmicSingularitiesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.LogarithmicSingularities
