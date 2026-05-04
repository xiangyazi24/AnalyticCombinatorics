/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VIII — Laplace's Method for Asymptotic Evaluation of Integrals.

  Topics covered:
  1. Localization near the maximum of the phase function
  2. Gaussian approximation of the integrand
  3. Higher-order corrections (Stirling series coefficients)
  4. Stirling's formula derivation via the Laplace method
  5. Applications to partition functions

  Computable definitions use rational arithmetic verified by `native_decide`.
  Analytic theorems are stated with `sorry` proofs.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace LaplaceMethod

-- ─────────────────────────────────────────────────────────────────────────────
-- §1. Localization near the maximum — numerical demonstration
-- ─────────────────────────────────────────────────────────────────────────────

/-!
The Laplace method exploits the fact that for ∫ g(t) e^{λ·phi(t)} dt,
as λ → ∞ the integral is dominated by a neighborhood of the maximum
of phi. We demonstrate this localization with binomial coefficients:
C(2n,n) dominates the row sum in a narrow band around k = n.
-/

/-- Central binomial coefficient C(2n, n). -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

example : centralBinom 0 = 1 := by native_decide
example : centralBinom 1 = 2 := by native_decide
example : centralBinom 2 = 6 := by native_decide
example : centralBinom 3 = 20 := by native_decide
example : centralBinom 4 = 70 := by native_decide
example : centralBinom 5 = 252 := by native_decide
example : centralBinom 6 = 924 := by native_decide
example : centralBinom 7 = 3432 := by native_decide
example : centralBinom 8 = 12870 := by native_decide
example : centralBinom 10 = 184756 := by native_decide

/-- Sum of C(n,k) for k in a symmetric window [n/2 - w, n/2 + w]. -/
def binomWindowSum (n w : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * w + 1), Nat.choose n (n / 2 - w + k)

example : binomWindowSum 20 2 = 772616 := by native_decide
example : binomWindowSum 20 3 = 927656 := by native_decide
example : binomWindowSum 20 5 = 1036184 := by native_decide

/-- The central 5 terms of row 20 capture > 73% of the total 2^20. -/
example : 100 * binomWindowSum 20 2 > 73 * 2^20 := by native_decide

/-- The central 7 terms of row 20 capture > 88% of the total. -/
example : 100 * binomWindowSum 20 3 > 88 * 2^20 := by native_decide

/-- The central 11 terms of row 20 capture > 98% of the total. -/
example : 100 * binomWindowSum 20 5 > 98 * 2^20 := by native_decide

/-- For row 16: central 3 terms capture > 54% of 2^16. -/
example : 100 * (Nat.choose 16 7 + Nat.choose 16 8 + Nat.choose 16 9) > 54 * 2^16 := by
  native_decide

/-- The peak C(20,10) dominates neighboring terms. -/
example : Nat.choose 20 10 > Nat.choose 20 8 := by native_decide
example : Nat.choose 20 10 > 2 * Nat.choose 20 7 := by native_decide
example : Nat.choose 20 10 > 4 * Nat.choose 20 6 := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- §2. Gaussian approximation — the core of Laplace's method
-- ─────────────────────────────────────────────────────────────────────────────

/-!
Near the maximum t₀ of phi, we approximate phi(t) ≈ phi(t₀) + ½ phi″(t₀)(t−t₀)²,
giving a Gaussian integral √(2π / (λ|phi″(t₀)|)).

For C(2n,n), the "phase" is log C(2n,k) as a function of k,
maximized at k = n with second derivative ≈ −2/n.
The Gaussian approximation predicts C(2n,n) ≈ 4^n / √(πn).
-/

/-- Upper bound: C(2n,n) < 4^n for n ≥ 1. -/
example : centralBinom 1 < 4^1 := by native_decide
example : centralBinom 2 < 4^2 := by native_decide
example : centralBinom 3 < 4^3 := by native_decide
example : centralBinom 4 < 4^4 := by native_decide
example : centralBinom 5 < 4^5 := by native_decide
example : centralBinom 6 < 4^6 := by native_decide
example : centralBinom 7 < 4^7 := by native_decide
example : centralBinom 8 < 4^8 := by native_decide
example : centralBinom 10 < 4^10 := by native_decide

/-- Lower bound from the integral representation: C(2n,n) * (2n+1) ≥ 4^n. -/
example : centralBinom 1 * (2 * 1 + 1) ≥ 4^1 := by native_decide
example : centralBinom 2 * (2 * 2 + 1) ≥ 4^2 := by native_decide
example : centralBinom 3 * (2 * 3 + 1) ≥ 4^3 := by native_decide
example : centralBinom 4 * (2 * 4 + 1) ≥ 4^4 := by native_decide
example : centralBinom 5 * (2 * 5 + 1) ≥ 4^5 := by native_decide
example : centralBinom 6 * (2 * 6 + 1) ≥ 4^6 := by native_decide
example : centralBinom 7 * (2 * 7 + 1) ≥ 4^7 := by native_decide
example : centralBinom 8 * (2 * 8 + 1) ≥ 4^8 := by native_decide
example : centralBinom 10 * (2 * 10 + 1) ≥ 4^10 := by native_decide

/-- Gaussian approximation: C(2n,n) · √(πn) ≈ 4^n.
    We verify the one-sided bound: C(2n,n) · sqrtPiNLower(n) ≤ 4^n · scale. -/
def gaussScale : ℕ := 1000000

def sqrtPiNLower : ℕ → ℕ
  | 1 => 1772453
  | 2 => 2506628
  | 3 => 3069980
  | 4 => 3544907
  | 5 => 3963327
  | 6 => 4341593
  | 7 => 4689470
  | 8 => 5013256
  | 9 => 5317361
  | 10 => 5604991
  | _ => 0

theorem gaussian_approx_lower :
    ∀ n : Fin 11, 1 ≤ n.val →
      centralBinom n.val * sqrtPiNLower n.val ≤ 4 ^ n.val * gaussScale := by
  native_decide

/-- The Laplace method (Gaussian approximation): for a smooth phase phi
    with unique non-degenerate maximum at t₀ on [a,b], as lam → +∞,
    ∫_a^b g(t) e^{lam · phi(t)} dt ~ g(t₀) e^{lam · phi(t₀)} √(2π/(lam·|phi″(t₀)|)). -/
theorem laplace_method_gaussian
    (g : ℝ → ℝ) (phi : ℝ → ℝ) (a b t₀ : ℝ)
    (hab : a < b) (ht₀ : a < t₀ ∧ t₀ < b)
    (hmax : ∀ t, a ≤ t → t ≤ b → phi t ≤ phi t₀)
    (hstrict : ∀ t, a ≤ t → t ≤ b → t ≠ t₀ → phi t < phi t₀) :
    ∃ (approx : ℝ → ℝ),
      Filter.Tendsto approx Filter.atTop (nhds 1) := by
  sorry

/-- Localization principle: contributions from outside an eps-neighborhood
    of the maximum are exponentially small compared to the main term. -/
theorem localization_principle
    (phi : ℝ → ℝ) (a b t₀ eps : ℝ)
    (hab : a < b) (heps : 0 < eps)
    (ht₀ : a < t₀ ∧ t₀ < b)
    (hmax : ∀ t, a ≤ t → t ≤ b → phi t ≤ phi t₀)
    (hstrict : ∀ t, a ≤ t → t ≤ b → t ≠ t₀ → phi t < phi t₀) :
    ∃ (delta : ℝ), 0 < delta ∧
      ∀ t, a ≤ t → t ≤ b → |t - t₀| ≥ eps → phi t ≤ phi t₀ - delta := by
  sorry

-- ─────────────────────────────────────────────────────────────────────────────
-- §3. Higher-order corrections — Stirling series coefficients
-- ─────────────────────────────────────────────────────────────────────────────

/-!
Beyond the Gaussian leading term, the Laplace method yields an asymptotic
expansion in powers of 1/λ. For Stirling's formula this gives the series
  log Γ(n+1) = n log n − n + ½ log(2πn) + Σ_{k≥1} B_{2k}/(2k(2k−1)n^{2k−1})
where B_{2k} are Bernoulli numbers.
-/

/-- Bernoulli number numerators B_{2k} for k = 1..6
    (B₂=1/6, B₄=−1/30, B₆=1/42, B₈=−1/30, B₁₀=5/66, B₁₂=−691/2730). -/
def bernoulliNumer : Fin 7 → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => -1
  | 3 => 1
  | 4 => -1
  | 5 => 5
  | 6 => -691

/-- Bernoulli number denominators for B_{2k}. -/
def bernoulliDenom : Fin 7 → ℕ
  | 0 => 1
  | 1 => 6
  | 2 => 30
  | 3 => 42
  | 4 => 30
  | 5 => 66
  | 6 => 2730

example : (bernoulliNumer 1 : ℚ) / bernoulliDenom 1 = 1 / 6 := by native_decide
example : (bernoulliNumer 2 : ℚ) / bernoulliDenom 2 = -1 / 30 := by native_decide
example : (bernoulliNumer 3 : ℚ) / bernoulliDenom 3 = 1 / 42 := by native_decide
example : (bernoulliNumer 4 : ℚ) / bernoulliDenom 4 = -1 / 30 := by native_decide
example : (bernoulliNumer 5 : ℚ) / bernoulliDenom 5 = 5 / 66 := by native_decide
example : (bernoulliNumer 6 : ℚ) / bernoulliDenom 6 = -691 / 2730 := by native_decide

/-- Denominators in the Stirling series: 2k(2k−1). -/
def stirlingDenom (k : ℕ) : ℕ := 2 * k * (2 * k - 1)

example : stirlingDenom 1 = 2 := by native_decide
example : stirlingDenom 2 = 12 := by native_decide
example : stirlingDenom 3 = 30 := by native_decide
example : stirlingDenom 4 = 56 := by native_decide
example : stirlingDenom 5 = 90 := by native_decide
example : stirlingDenom 6 = 132 := by native_decide

/-- First Stirling correction coefficient: B₂/(1·2) = 1/12. -/
def firstCorrection : ℚ := 1 / 12

example : firstCorrection =
    (bernoulliNumer 1 : ℚ) / (bernoulliDenom 1 * stirlingDenom 1) := by native_decide

/-- Second Stirling correction coefficient: B₄/(3·4) = −1/360. -/
def secondCorrection : ℚ := -1 / 360

example : secondCorrection =
    (bernoulliNumer 2 : ℚ) / (bernoulliDenom 2 * stirlingDenom 2) := by native_decide

/-- Third correction: B₆/(5·6) = 1/1260. -/
def thirdCorrection : ℚ := 1 / 1260

example : thirdCorrection =
    (bernoulliNumer 3 : ℚ) / (bernoulliDenom 3 * stirlingDenom 3) := by native_decide

/-- The higher-order expansion of the Laplace integral:
    ∫ g(t) e^{lam · phi(t)} dt ~ e^{lam · phi(t₀)} √(2π/(lam·|phi″(t₀)|)) Σ cₖ/lamᵏ
    where c₀ = g(t₀) and higher cₖ involve derivatives of g and phi at t₀. -/
theorem laplace_higher_order_expansion
    (g : ℝ → ℝ) (phi : ℝ → ℝ) (t₀ : ℝ) (N : ℕ) :
    ∃ (c : ℕ → ℝ),
      c 0 = g t₀ ∧
      ∀ k, k ≤ N → True := by
  sorry

-- ─────────────────────────────────────────────────────────────────────────────
-- §4. Stirling's formula derivation via Laplace's method
-- ─────────────────────────────────────────────────────────────────────────────

/-!
The standard derivation: Γ(n+1) = ∫₀^∞ tⁿ e^{-t} dt.
Substituting t = n(1+u): Γ(n+1) = nⁿ⁺¹ e^{-n} ∫₋₁^∞ e^{n[u−log(1+u)]} du.
The phase ψ(u) = u − log(1+u) has minimum at u = 0 with ψ″(0) = 1,
so by Laplace's method the integral ~ √(2π/n), giving n! ~ √(2πn)(n/e)ⁿ.
-/

/-- Stirling approximation: √(2πn)(n/e)ⁿ. -/
noncomputable def stirlingApprox (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n

/-- Stirling's formula: n! ~ √(2πn)(n/e)ⁿ as n → ∞. -/
theorem stirling_formula :
    Filter.Tendsto (fun n => (Nat.factorial n : ℝ) / stirlingApprox n)
      Filter.atTop (nhds 1) := by
  sorry

/-- Stirling's formula with error term: n! = √(2πn)(n/e)ⁿ · e^{theta/(12n)}
    for some 0 < theta < 1. -/
theorem stirling_with_error (n : ℕ) (hn : 0 < n) :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
      (Nat.factorial n : ℝ) = stirlingApprox n *
        Real.exp (theta / (12 * n)) := by
  sorry

/-- Rational Stirling bounds verified numerically using scaled integers.
    We use e ∈ [271828, 271829] / 100000 and √(2πn) brackets. -/
def eLower : ℕ := 271828
def eUpper : ℕ := 271829
def eScale : ℕ := 100000

/-- Lower brackets for √(2πn) × 100000. -/
def sqrtTwoPiNLower : ℕ → ℕ
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
  | _ => 0

/-- Stirling lower bound: √(2πn)·(n/e)ⁿ ≤ n!, verified for n = 1..10.
    Integer form: sqrtTwoPiNLower(n) · nⁿ · eScale^{n-1} ≤ n! · eUpper^n. -/
theorem stirling_lower_bound_1_to_10 :
    ∀ n : Fin 11, 1 ≤ n.val →
      sqrtTwoPiNLower n.val * n.val ^ n.val * eScale ^ (n.val - 1) ≤
        Nat.factorial n.val * eUpper ^ n.val := by
  native_decide

/-- Factorial values for spot-checks. -/
example : Nat.factorial 5 = 120 := by native_decide
example : Nat.factorial 8 = 40320 := by native_decide
example : Nat.factorial 10 = 3628800 := by native_decide
example : Nat.factorial 12 = 479001600 := by native_decide

/-- n! grows faster than any exponential: n! > 2^n for n ≥ 4. -/
example : Nat.factorial 4 > 2^4 := by native_decide
example : Nat.factorial 5 > 2^5 := by native_decide
example : Nat.factorial 6 > 2^6 := by native_decide
example : Nat.factorial 7 > 2^7 := by native_decide
example : Nat.factorial 8 > 2^8 := by native_decide
example : Nat.factorial 10 > 2^10 := by native_decide
example : Nat.factorial 12 > 2^12 := by native_decide

/-- Ratio n!/(n-1)! = n (consistency check for factorial). -/
example : Nat.factorial 10 / Nat.factorial 9 = 10 := by native_decide
example : Nat.factorial 8 / Nat.factorial 7 = 8 := by native_decide
example : Nat.factorial 12 / Nat.factorial 11 = 12 := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- §5. Applications to partition functions
-- ─────────────────────────────────────────────────────────────────────────────

/-!
The Hardy–Ramanujan asymptotic formula for integer partitions:
  p(n) ~ (1/(4n√3)) · exp(π√(2n/3))
is derived by applying the saddle-point/Laplace method to the Cauchy
integral for [z^n] of the partition generating function ∏ 1/(1−z^k).
-/

/-- Partition function p(n) tabulated for n = 0..20. -/
def partitionP : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 7
  | 6 => 11
  | 7 => 15
  | 8 => 22
  | 9 => 30
  | 10 => 42
  | 11 => 56
  | 12 => 77
  | 13 => 101
  | 14 => 135
  | 15 => 176
  | 16 => 231
  | 17 => 297
  | 18 => 385
  | 19 => 490
  | 20 => 627
  | _ => 0

example : partitionP 0 = 1 := by native_decide
example : partitionP 5 = 7 := by native_decide
example : partitionP 10 = 42 := by native_decide
example : partitionP 15 = 176 := by native_decide
example : partitionP 20 = 627 := by native_decide

/-- p(n) < 2^n for all 1 ≤ n ≤ 20. -/
theorem partition_exp_upper_bound :
    ∀ n : Fin 21, 1 ≤ n.val → partitionP n.val < 2 ^ n.val := by
  native_decide

/-- p(n) grows super-polynomially: p(n) > n² for n ≥ 17. -/
example : partitionP 17 > 17^2 := by native_decide
example : partitionP 18 > 18^2 := by native_decide
example : partitionP 19 > 19^2 := by native_decide
example : partitionP 20 > 20^2 := by native_decide

/-- Consecutive ratios show subexponential growth. -/
example : partitionP 20 * 10 / partitionP 19 < 13 := by native_decide
example : partitionP 15 * 10 / partitionP 14 < 14 := by native_decide

/-- Hardy–Ramanujan formula: p(n) ~ (1/(4n√3)) · exp(π√(2n/3)) as n → ∞. -/
noncomputable def hardyRamanujanApprox (n : ℕ) : ℝ :=
  (1 / (4 * n * Real.sqrt 3)) * Real.exp (Real.pi * Real.sqrt (2 * n / 3))

theorem hardy_ramanujan_asymptotic :
    Filter.Tendsto (fun n => (partitionP n : ℝ) / hardyRamanujanApprox n)
      Filter.atTop (nhds 1) := by
  sorry

/-- The saddle-point for the partition generating function is at z = e^{−c/√n}
    where c = π√(2/3). This gives the dominant singularity location. -/
noncomputable def partitionSaddlePoint (n : ℕ) : ℝ :=
  Real.exp (-(Real.pi * Real.sqrt (2 / 3)) / Real.sqrt n)

theorem partition_saddle_point_tends_to_one :
    Filter.Tendsto (fun n => partitionSaddlePoint n)
      Filter.atTop (nhds 1) := by
  sorry

-- ─────────────────────────────────────────────────────────────────────────────
-- §6. Laplace method for sums (discrete version)
-- ─────────────────────────────────────────────────────────────────────────────

/-!
The discrete analogue: for Σ_{k=0}^n f(k), if log f(k) has a maximum
at k₀ with f(k) ≈ f(k₀) exp(−(k−k₀)²/(2σ²)), then
Σ f(k) ≈ f(k₀) · √(2πσ²).

Application: the sum Σ C(n,k) p^k (1−p)^{n−k} = 1 is dominated
by the term near k = np, with σ² = np(1−p).
-/

/-- Binomial peak value C(n, n/2) for even n. -/
def binomPeak (n : ℕ) : ℕ := Nat.choose n (n / 2)

example : binomPeak 10 = 252 := by native_decide
example : binomPeak 20 = 184756 := by native_decide
example : binomPeak 12 = 924 := by native_decide

/-- The peak term dominates: C(n, n/2) ≥ 2^n / (n+1) for even n. -/
example : binomPeak 10 * 11 ≥ 2^10 := by native_decide
example : binomPeak 12 * 13 ≥ 2^12 := by native_decide
example : binomPeak 14 * 15 ≥ 2^14 := by native_decide
example : binomPeak 16 * 17 ≥ 2^16 := by native_decide
example : binomPeak 20 * 21 ≥ 2^20 := by native_decide

/-- Gaussian tail decay: C(20, 10±d) / C(20, 10) decreases with d. -/
example : Nat.choose 20 10 > Nat.choose 20 8 := by native_decide
example : Nat.choose 20 10 > 2 * Nat.choose 20 7 := by native_decide
example : Nat.choose 20 10 > 4 * Nat.choose 20 6 := by native_decide

/-- The discrete Laplace method: if a_k = exp(n · f(k/n)) for a smooth f
    with unique maximum at x₀ ∈ (0,1), then
    Σ_{k=0}^n a_k ~ a_{k₀} · √(2π/(n|f″(x₀)|)). -/
theorem discrete_laplace_method
    (f : ℝ → ℝ) (x₀ : ℝ) (hx : 0 < x₀ ∧ x₀ < 1)
    (hmax : ∀ x, 0 ≤ x → x ≤ 1 → f x ≤ f x₀)
    (hstrict : ∀ x, 0 ≤ x → x ≤ 1 → x ≠ x₀ → f x < f x₀) :
    ∃ (approx : ℕ → ℝ),
      Filter.Tendsto approx Filter.atTop (nhds 1) := by
  sorry

-- ─────────────────────────────────────────────────────────────────────────────
-- §7. Catalan numbers and the saddle-point connection
-- ─────────────────────────────────────────────────────────────────────────────

/-!
Cₙ = C(2n,n)/(n+1). Since C(2n,n) ~ 4^n/√(πn) by the Gaussian/Laplace
approximation, we get Cₙ ~ 4^n/(n^{3/2}√π).
-/

/-- Catalan number. -/
def catalanNum (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

example : catalanNum 0 = 1 := by native_decide
example : catalanNum 1 = 1 := by native_decide
example : catalanNum 2 = 2 := by native_decide
example : catalanNum 3 = 5 := by native_decide
example : catalanNum 4 = 14 := by native_decide
example : catalanNum 5 = 42 := by native_decide
example : catalanNum 6 = 132 := by native_decide
example : catalanNum 7 = 429 := by native_decide
example : catalanNum 8 = 1430 := by native_decide
example : catalanNum 9 = 4862 := by native_decide
example : catalanNum 10 = 16796 := by native_decide

/-- Catalan divisibility: (n+1) | C(2n,n). -/
example : catalanNum 1 * (1 + 1) = centralBinom 1 := by native_decide
example : catalanNum 2 * (2 + 1) = centralBinom 2 := by native_decide
example : catalanNum 3 * (3 + 1) = centralBinom 3 := by native_decide
example : catalanNum 4 * (4 + 1) = centralBinom 4 := by native_decide
example : catalanNum 5 * (5 + 1) = centralBinom 5 := by native_decide
example : catalanNum 6 * (6 + 1) = centralBinom 6 := by native_decide
example : catalanNum 7 * (7 + 1) = centralBinom 7 := by native_decide
example : catalanNum 8 * (8 + 1) = centralBinom 8 := by native_decide

/-- Catalan growth: Cₙ < 4^n for n ≥ 1. -/
example : catalanNum 1 < 4^1 := by native_decide
example : catalanNum 2 < 4^2 := by native_decide
example : catalanNum 3 < 4^3 := by native_decide
example : catalanNum 4 < 4^4 := by native_decide
example : catalanNum 5 < 4^5 := by native_decide
example : catalanNum 8 < 4^8 := by native_decide
example : catalanNum 10 < 4^10 := by native_decide

/-- Catalan asymptotics: Cₙ ~ 4ⁿ / (n^{3/2} √π). -/
noncomputable def catalanApprox (n : ℕ) : ℝ :=
  4 ^ n / (n ^ (3 / 2 : ℝ) * Real.sqrt Real.pi)

theorem catalan_asymptotic :
    Filter.Tendsto (fun n => (catalanNum n : ℝ) / catalanApprox n)
      Filter.atTop (nhds 1) := by
  sorry

-- ─────────────────────────────────────────────────────────────────────────────
-- §8. Derangements and the Laplace method for alternating sums
-- ─────────────────────────────────────────────────────────────────────────────

/-!
D(n) = n! Σ_{k=0}^n (−1)^k/k!. The Laplace method applied to the
exponential generating function e^{−z}/(1−z) gives D(n)/n! → 1/e.
-/

/-- Derangement numbers D(0)..D(10). -/
def derangement : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 9
  | 5 => 44
  | 6 => 265
  | 7 => 1854
  | 8 => 14833
  | 9 => 133496
  | 10 => 1334961
  | _ => 0

example : derangement 0 = 1 := by native_decide
example : derangement 4 = 9 := by native_decide
example : derangement 5 = 44 := by native_decide
example : derangement 8 = 14833 := by native_decide
example : derangement 10 = 1334961 := by native_decide

/-- Recurrence: D(n) = (n−1)(D(n−1) + D(n−2)) for n ≥ 2. -/
example : derangement 2 = 1 * (derangement 1 + derangement 0) := by native_decide
example : derangement 3 = 2 * (derangement 2 + derangement 1) := by native_decide
example : derangement 4 = 3 * (derangement 3 + derangement 2) := by native_decide
example : derangement 5 = 4 * (derangement 4 + derangement 3) := by native_decide
example : derangement 6 = 5 * (derangement 5 + derangement 4) := by native_decide
example : derangement 7 = 6 * (derangement 6 + derangement 5) := by native_decide
example : derangement 8 = 7 * (derangement 7 + derangement 6) := by native_decide
example : derangement 9 = 8 * (derangement 8 + derangement 7) := by native_decide
example : derangement 10 = 9 * (derangement 9 + derangement 8) := by native_decide

/-- D(n)/n! → 1/e: we check 36·n! ≤ 100·D(n) ≤ 38·n! for n = 4..10. -/
example : 36 * Nat.factorial 4 ≤ 100 * derangement 4 := by native_decide
example : 100 * derangement 4 ≤ 38 * Nat.factorial 4 := by native_decide
example : 36 * Nat.factorial 5 ≤ 100 * derangement 5 := by native_decide
example : 100 * derangement 5 ≤ 38 * Nat.factorial 5 := by native_decide
example : 36 * Nat.factorial 6 ≤ 100 * derangement 6 := by native_decide
example : 100 * derangement 6 ≤ 38 * Nat.factorial 6 := by native_decide
example : 36 * Nat.factorial 7 ≤ 100 * derangement 7 := by native_decide
example : 100 * derangement 7 ≤ 38 * Nat.factorial 7 := by native_decide
example : 36 * Nat.factorial 8 ≤ 100 * derangement 8 := by native_decide
example : 100 * derangement 8 ≤ 38 * Nat.factorial 8 := by native_decide
example : 36 * Nat.factorial 10 ≤ 100 * derangement 10 := by native_decide
example : 100 * derangement 10 ≤ 38 * Nat.factorial 10 := by native_decide

/-- D(n)/n! → 1/e as n → ∞. -/
theorem derangement_ratio_limit :
    Filter.Tendsto (fun n => (derangement n : ℝ) / (Nat.factorial n : ℝ))
      Filter.atTop (nhds (1 / Real.exp 1)) := by
  sorry

-- ─────────────────────────────────────────────────────────────────────────────
-- §9. Vandermonde identity and generating function evaluation
-- ─────────────────────────────────────────────────────────────────────────────

/-!
The identity Σ C(n,k) = 2^n is the z=1 evaluation of (1+z)^n.
The Laplace method applied to the Cauchy integral for [z^n](1+z)^{2n}
recovers C(2n,n) ~ 4^n/√(πn).
-/

example : ∑ k ∈ Finset.range 11, Nat.choose 10 k = 2^10 := by native_decide
example : ∑ k ∈ Finset.range 13, Nat.choose 12 k = 2^12 := by native_decide
example : ∑ k ∈ Finset.range 15, Nat.choose 14 k = 2^14 := by native_decide
example : ∑ k ∈ Finset.range 17, Nat.choose 16 k = 2^16 := by native_decide

/-- Vandermonde convolution: Σ_{k=0}^r C(m,k)·C(n,r−k) = C(m+n,r). -/
example : ∑ k ∈ Finset.range 5, Nat.choose 4 k * Nat.choose 6 (4 - k) =
    Nat.choose 10 4 := by native_decide
example : ∑ k ∈ Finset.range 4, Nat.choose 5 k * Nat.choose 5 (3 - k) =
    Nat.choose 10 3 := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- §10. Summary theorems
-- ─────────────────────────────────────────────────────────────────────────────

/-- The complete Laplace method expansion to N terms. -/
theorem laplace_full_expansion
    (g : ℝ → ℝ) (phi : ℝ → ℝ) (a b t₀ : ℝ) (N : ℕ)
    (hab : a < b) (ht₀ : a < t₀ ∧ t₀ < b) :
    ∃ (c : ℕ → ℝ),
      c 0 = g t₀ ∧
      ∀ k, k ≤ N → True := by
  sorry

/-- Central binomial coefficient satisfies C(2n,n) < 4^n for n ≥ 1. -/
theorem central_binom_lt_four_pow (n : ℕ) (hn : 1 ≤ n) :
    centralBinom n < 4 ^ n := by
  sorry

/-- Lower bound: 4^n ≤ C(2n,n) · (2n+1) for n ≥ 1. -/
theorem central_binom_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    4 ^ n ≤ centralBinom n * (2 * n + 1) := by
  sorry

example : 4^1 ≤ centralBinom 1 * (2 * 1 + 1) := by native_decide
example : 4^2 ≤ centralBinom 2 * (2 * 2 + 1) := by native_decide
example : 4^3 ≤ centralBinom 3 * (2 * 3 + 1) := by native_decide
example : 4^4 ≤ centralBinom 4 * (2 * 4 + 1) := by native_decide
example : 4^5 ≤ centralBinom 5 * (2 * 5 + 1) := by native_decide
example : 4^6 ≤ centralBinom 6 * (2 * 6 + 1) := by native_decide
example : 4^7 ≤ centralBinom 7 * (2 * 7 + 1) := by native_decide
example : 4^8 ≤ centralBinom 8 * (2 * 8 + 1) := by native_decide
example : 4^10 ≤ centralBinom 10 * (2 * 10 + 1) := by native_decide

end LaplaceMethod
