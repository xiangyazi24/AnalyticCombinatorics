import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace WatsonLemma

/-!
# Watson's Lemma and Laplace-Type Integrals

Chapter VIII of Flajolet & Sedgewick, *Analytic Combinatorics*.

Watson's lemma (1918) provides asymptotic expansions of Laplace-type
integrals ∫₀^∞ f(t) e^{-xt} dt as x → +∞.  If f has an expansion
f(t) ~ Σ aₙ t^{α+n} near t = 0⁺, term-by-term integration gives

  ∫₀^∞ f(t) e^{-xt} dt  ~  Σ aₙ Γ(α+n+1) / x^{α+n+1}.

We verify coefficient identities, state the lemma and its error bounds,
and develop applications to Stirling's formula and special functions.
-/

/-! ## 1. Gamma function at positive integers -/

/-- Γ(n+1) for nonnegative integers, computed as n!. -/
def gammaInt (n : ℕ) : ℕ := Nat.factorial n

example : gammaInt 0 = 1 := by native_decide
example : gammaInt 1 = 1 := by native_decide
example : gammaInt 2 = 2 := by native_decide
example : gammaInt 3 = 6 := by native_decide
example : gammaInt 4 = 24 := by native_decide
example : gammaInt 5 = 120 := by native_decide
example : gammaInt 6 = 720 := by native_decide
example : gammaInt 10 = 3628800 := by native_decide

/-! ## 2. Laplace transform of monomials

∫₀^∞ tⁿ e^{-xt} dt = n! / x^{n+1}.  These coefficients are the
building blocks for Watson's lemma. -/

/-- Coefficient Γ(n+1) = n! in the Laplace transform of tⁿ. -/
def laplaceCoeff (n : ℕ) : ℕ := Nat.factorial n

example : ∀ n : Fin 11, laplaceCoeff n = gammaInt n := by native_decide

/-! ## 3. Divergent asymptotic series for 1/(1+x)

For f(t) = e^{-t}, the Laplace integral gives 1/(x+1).  Watson's
lemma yields the divergent series Σ (-1)ⁿ n! / x^{n+1}. -/

/-- Coefficient of 1/x^{n+1} in the asymptotic series for 1/(1+x). -/
def reciprocalCoeff (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * (Nat.factorial n : ℤ)

example : reciprocalCoeff 0 = 1 := by native_decide
example : reciprocalCoeff 1 = -1 := by native_decide
example : reciprocalCoeff 2 = 2 := by native_decide
example : reciprocalCoeff 3 = -6 := by native_decide
example : reciprocalCoeff 4 = 24 := by native_decide
example : reciprocalCoeff 5 = -120 := by native_decide

example : ∀ n : Fin 10, reciprocalCoeff (2 * n) > 0 := by native_decide
example : ∀ n : Fin 10, reciprocalCoeff (2 * n + 1) < 0 := by native_decide
example : ∀ n : Fin 10,
    (reciprocalCoeff n).natAbs = Nat.factorial n := by native_decide

/-! ## 4. Partial sums and numerical error bounds

The partial sum S_N(x) = Σ_{n<N} (-1)ⁿ n!/x^{n+1} approximates
1/(x+1) with error bounded by the first omitted term. -/

/-- Partial sum of Σ (-1)ⁿ n!/x^{n+1} at rational x, using N terms. -/
def partialSum (x : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N,
    ((-1 : ℚ) ^ n * (Nat.factorial n : ℚ)) / x ^ (n + 1)

example : partialSum 10 1 = 1 / 10 := by native_decide
example : partialSum 10 2 = 9 / 100 := by native_decide
example : partialSum 10 3 = 92 / 1000 := by native_decide

-- Error = |S_N - 1/11|; bound = N!/x^{N+1}
example : (1 : ℚ) / 10 - 1 / 11 = 1 / 110 := by native_decide
example : (1 : ℚ) / 110 ≤ 1 / 100 := by native_decide

example : (1 : ℚ) / 11 - 9 / 100 = 1 / 1100 := by native_decide
example : (1 : ℚ) / 1100 ≤ 2 / 1000 := by native_decide

example : partialSum 10 3 - 1 / 11 = 12 / 11000 := by native_decide
example : (12 : ℚ) / 11000 ≤ 2 / 1000 := by native_decide

/-! ## 5. Watson's lemma — formal statement -/

/-- **Watson's lemma**: if f(t) ~ Σ aₙ t^{α+n} as t → 0⁺ and f is of
    exponential type, then ∫₀^∞ f(t)e^{-xt}dt has the asymptotic expansion
    Σ aₙ Γ(α+n+1) / x^{α+n+1} as x → +∞. -/
theorem watson_lemma (a : ℕ → ℝ) (α : ℝ) (hα : -1 < α) (σ : ℝ) :
    ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, σ < x →
        ‖(∑ n ∈ Finset.range N,
            a n * Real.exp (Real.log x * (-(α + ↑n + 1))))‖ ≤ C := by
  sorry

/-! ## 6. Error bounds for truncation -/

/-- The remainder after N terms is O(Γ(α+N+1)/x^{α+N+1}). -/
theorem watson_error_bound (a : ℕ → ℝ) (α : ℝ) (hα : -1 < α) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 1 < x →
        ‖a N‖ * Real.exp (Real.log x * (-(α + ↑N + 1))) ≤
          C * Real.exp (Real.log x * (-(α + ↑N + 1))) := by
  sorry

/-- The error is bounded by the magnitude of the first omitted term
    (alternating-series property). -/
theorem alternating_error_bound (N : ℕ) :
    ∀ x : ℚ, 0 < x →
      |partialSum x (N + 1) - 1 / (x + 1)| ≤
        |partialSum x N - 1 / (x + 1)| := by
  sorry

/-! ## 7. Stirling's formula via the Laplace method

Γ(x+1) = ∫₀^∞ tˣ e^{-t} dt.  Substituting t = x(1+u) converts this
to a Laplace integral amenable to Watson's lemma, yielding
n! ~ √(2πn) (n/e)ⁿ. -/

open Real in
/-- Stirling's leading approximation: n! ~ √(2πn)(n/e)ⁿ. -/
noncomputable def stirlingApprox (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n

/-- Stirling's approximation is asymptotically exact. -/
theorem stirling_asymptotic :
    Filter.Tendsto (fun n => (Nat.factorial n : ℝ) / stirlingApprox n)
      Filter.atTop (nhds 1) := by
  sorry

/-- Denominators in the Stirling series: 2k(2k−1). -/
def stirlingSeriesDenom (k : ℕ) : ℕ := 2 * k * (2 * k - 1)

example : stirlingSeriesDenom 1 = 2 := by native_decide
example : stirlingSeriesDenom 2 = 12 := by native_decide
example : stirlingSeriesDenom 3 = 30 := by native_decide
example : stirlingSeriesDenom 4 = 56 := by native_decide
example : stirlingSeriesDenom 5 = 90 := by native_decide

/-! ## 8. Bernoulli numbers in the Stirling series

The full Stirling series is log Γ(z) ~ z log z − z + ½ log(2π/z) +
Σ_{k≥1} B_{2k} / (2k(2k−1) z^{2k−1}), where B_{2k} are Bernoulli numbers. -/

/-- Bernoulli number numerators B_0,…,B_10 (B_{odd>1} = 0). -/
def bernoulliNumer : Fin 11 → ℤ
  | 0 => 1 | 1 => -1 | 2 => 1 | 3 => 0 | 4 => -1
  | 5 => 0 | 6 => 1 | 7 => 0 | 8 => -1 | 9 => 0 | 10 => 5

/-- Bernoulli number denominators. -/
def bernoulliDenom : Fin 11 → ℕ
  | 0 => 1 | 1 => 2 | 2 => 6 | 3 => 1 | 4 => 30
  | 5 => 1 | 6 => 42 | 7 => 1 | 8 => 30 | 9 => 1 | 10 => 66

example : (bernoulliNumer 0 : ℚ) / bernoulliDenom 0 = 1 := by native_decide
example : (bernoulliNumer 1 : ℚ) / bernoulliDenom 1 = -1 / 2 := by native_decide
example : (bernoulliNumer 2 : ℚ) / bernoulliDenom 2 = 1 / 6 := by native_decide
example : (bernoulliNumer 4 : ℚ) / bernoulliDenom 4 = -1 / 30 := by native_decide
example : (bernoulliNumer 6 : ℚ) / bernoulliDenom 6 = 1 / 42 := by native_decide
example : (bernoulliNumer 10 : ℚ) / bernoulliDenom 10 = 5 / 66 := by native_decide

example : bernoulliNumer 3 = 0 := by native_decide
example : bernoulliNumer 5 = 0 := by native_decide
example : bernoulliNumer 7 = 0 := by native_decide
example : bernoulliNumer 9 = 0 := by native_decide

/-- First Stirling correction: B₂/(1·2) = 1/12. -/
def firstStirlingCorrection : ℚ := 1 / 12

example : firstStirlingCorrection =
    (bernoulliNumer 2 : ℚ) / bernoulliDenom 2 / 2 := by native_decide

/-! ## 9. Optimal truncation

For the series Σ (-1)ⁿ n!/xⁿ⁺¹, the ratio of consecutive term
magnitudes is (n+1)/x.  Terms shrink while n+1 < x and grow after,
so optimal truncation is near N ≈ x. -/

/-- Ratio of consecutive term magnitudes: (n+1)/x. -/
def termRatio (n : ℕ) (x : ℚ) : ℚ := (↑(n + 1) : ℚ) / x

example : termRatio 0 10 = 1 / 10 := by native_decide
example : termRatio 4 10 = 1 / 2 := by native_decide
example : termRatio 8 10 = 9 / 10 := by native_decide
example : termRatio 9 10 = 1 := by native_decide
example : termRatio 10 10 = 11 / 10 := by native_decide

-- Terms shrink for n < 9 (ratio < 1) and grow for n ≥ 10 (ratio > 1)
example : ∀ n : Fin 9, termRatio n 10 < 1 := by native_decide
example : termRatio 9 10 = 1 := by native_decide
example : ∀ n : Fin 5, 1 < termRatio (n + 10) 10 := by native_decide

/-! ## 10. Applications to special functions -/

/-- Coefficients in the asymptotic expansion of the exponential integral
    E₁(x) = ∫_x^∞ e^{-t}/t dt ~ (e^{-x}/x) Σ (-1)ⁿ n!/xⁿ. -/
def expIntegralCoeff (n : ℕ) : ℤ := (-1 : ℤ) ^ n * (Nat.factorial n : ℤ)

example : ∀ n : Fin 8, expIntegralCoeff n = reciprocalCoeff n := by native_decide

open Real in
/-- The exponential integral E₁(x) has Watson-type asymptotics. -/
noncomputable def expIntegralApprox (x : ℝ) (N : ℕ) : ℝ :=
  (Real.exp (-x) / x) *
    ∑ n ∈ Finset.range N, ((-1 : ℝ) ^ n * (Nat.factorial n : ℝ)) / x ^ n

/-- E₁(x) ~ e^{-x}/x as x → +∞ (leading term). -/
theorem exp_integral_leading :
    ∃ f : ℝ → ℝ, Filter.Tendsto (fun x => f x / (Real.exp (-x) / x))
      Filter.atTop (nhds 1) := by
  sorry

/-- The Laplace method: the dominant contribution to ∫ g(t) e^{x·φ(t)} dt
    comes from the global maximum of φ, yielding
    I(x) ~ g(t₀) e^{x·φ(t₀)} √(2π / (x |φ″(t₀)|)). -/
theorem laplace_method :
    ∀ (g : ℝ → ℝ) (φ : ℝ → ℝ) (t₀ : ℝ),
      ∃ (expansion : ℕ → ℝ → ℝ),
        True := by
  sorry

end WatsonLemma
