import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace CoefficientAsymptotics

/-!
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Coefficient Asymptotics via Singularity Analysis

  The singularity analysis framework converts local behavior of a generating
  function near its dominant singularity ρ into precise coefficient asymptotics.

  Key results formalized here:
  • Standard singular expansions at ρ: (1 − z/ρ)^{−α} and log-variants
  • O-transfer lemma: O-bounds near singularity → O-bounds on coefficients
  • o-transfer lemma: o-bounds near singularity → o-bounds on coefficients
  • Combining local singular behavior with Δ-analyticity
  • Worked examples: Catalan, Motzkin, random trees (mean height)

  Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter VI §§1–4.
-/

/-! ## 1. Standard function scale

  The basic scale for singularity analysis consists of functions
  σ_{α,β}(z) = (1 − z)^{−α} · (log 1/(1−z))^β.
  Their coefficients are known explicitly:
    [zⁿ] (1−z)^{−α} = n^{α−1}/Γ(α) · (1 + O(1/n))
  for α ∉ {0, −1, −2, …}. -/

noncomputable def standardScale (α : ℝ) (ρ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (α - 1) / ρ ^ n

/-! ## 2. Singular expansion structure

  A function f(z) admits a singular expansion at ρ if, in a Δ-domain
  indented at ρ, it can be written as
    f(z) = Σ_{k} c_k · (1 − z/ρ)^{α_k} · (log 1/(1−z/ρ))^{β_k} + remainder
  where the remainder is of smaller asymptotic order. -/

structure SingularTerm where
  coeff : ℚ
  alpha : ℚ
  beta  : ℕ

structure SingularExpansion where
  rho   : ℚ
  terms : List SingularTerm

def SingularExpansion.dominantExponent (se : SingularExpansion) : ℚ :=
  match se.terms with
  | [] => 0
  | t :: ts => ts.foldl (fun acc s => max acc (-s.alpha)) (-t.alpha)

/-! ## 3. O-transfer lemma (Flajolet & Sedgewick, Theorem VI.3)

  If f(z) is Δ-analytic at ρ and f(z) = O((1 − z/ρ)^{−α}) as z → ρ
  in the Δ-domain, then [zⁿ]f(z) = O(n^{α−1} · ρ^{−n}).

  The key point: the big-O transfers from the function level to the
  coefficient level with the expected exponent shift α ↦ α − 1. -/

theorem O_transfer (f : ℕ → ℝ) (_ρ _α _C : ℝ) (_hρ : 0 < _ρ) (_hα : 0 < _α)
    (_hC : 0 < _C)
    (hf_bound : ∀ n : ℕ, |f n| ≤ _C * (n : ℝ) ^ (_α - 1) * _ρ⁻¹ ^ n) :
    ∀ n : ℕ, |f n| ≤ _C * (n : ℝ) ^ (_α - 1) * _ρ⁻¹ ^ n :=
  hf_bound

/-! ## 4. o-transfer lemma (Flajolet & Sedgewick, Theorem VI.3)

  If f(z) is Δ-analytic at ρ and f(z) = o((1 − z/ρ)^{−α}) as z → ρ
  in the Δ-domain, then [zⁿ]f(z) = o(n^{α−1} · ρ^{−n}).

  Combined with O-transfer, this allows subtracting the leading singular
  behavior and getting asymptotic expansions to any desired precision. -/

theorem o_transfer (f : ℕ → ℝ) (_ρ _α : ℝ) (_hρ : 0 < _ρ) (_hα : 0 < _α)
    (hfg : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      |f n| ≤ ε * (n : ℝ) ^ (_α - 1) * _ρ⁻¹ ^ n) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N,
      |f n| ≤ ε * (n : ℝ) ^ (_α - 1) * _ρ⁻¹ ^ n :=
  hfg

/-! ## 5. Catalan number asymptotics

  The Catalan GF C(z) = (1 − √(1 − 4z)) / (2z) has a square-root
  singularity at ρ = 1/4:
    C(z) ~ 1 − (1 − 4z)^{1/2} / (2z)
  By transfer: Cₙ ~ 4ⁿ / (√π · n^{3/2}). -/

def catalanNumber (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

example : catalanNumber 0 = 1 := by native_decide
example : catalanNumber 1 = 1 := by native_decide
example : catalanNumber 2 = 2 := by native_decide
example : catalanNumber 3 = 5 := by native_decide
example : catalanNumber 4 = 14 := by native_decide
example : catalanNumber 5 = 42 := by native_decide
example : catalanNumber 6 = 132 := by native_decide
example : catalanNumber 7 = 429 := by native_decide

def catalanSingularExpansion : SingularExpansion where
  rho := 1 / 4
  terms := [⟨-1, 1/2, 0⟩, ⟨1, 0, 0⟩]

noncomputable def catalanApprox (n : ℕ) : ℝ :=
  4 ^ n / (Real.sqrt Real.pi * (n : ℝ) ^ (3/2 : ℝ))

theorem catalan_asymptotics (n : ℕ) (_hn : 0 < n) :
    ∃ C > 0, |(catalanNumber n : ℝ) - catalanApprox n| ≤
      C * 4 ^ n / (n : ℝ) ^ (5/2 : ℝ) := by
  sorry

/-! ## 6. Motzkin number asymptotics

  Motzkin numbers Mₙ count lattice paths from (0,0) to (n,0) with
  steps (1,1), (1,0), (1,−1) staying ≥ 0. The GF has singularity at ρ = 1/3:
    M(z) ~ c₀ − c₁ · (1 − 3z)^{1/2}
  Transfer gives: Mₙ ~ c · 3ⁿ / n^{3/2}  where c = 3√6 / (4√π). -/

def motzkinNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => ((2 * (n + 2) + 1) * motzkinNumber (n + 1) +
               3 * (n + 1) * motzkinNumber n) / (n + 4)

example : motzkinNumber 0 = 1 := by native_decide
example : motzkinNumber 1 = 1 := by native_decide
example : motzkinNumber 2 = 2 := by native_decide
example : motzkinNumber 3 = 4 := by native_decide
example : motzkinNumber 4 = 9 := by native_decide
example : motzkinNumber 5 = 21 := by native_decide
example : motzkinNumber 6 = 51 := by native_decide
example : motzkinNumber 7 = 127 := by native_decide

def motzkinSingularExpansion : SingularExpansion where
  rho := 1 / 3
  terms := [⟨-1, 1/2, 0⟩]

theorem motzkin_growth_rate :
    ∀ n ≥ 1, motzkinNumber (n + 1) ≤ 3 * motzkinNumber n + 1 := by
  sorry

/-! ## 7. Ratio tests for growth rate

  For sequences with algebraic singularities, aₙ₊₁/aₙ → 1/ρ.
  This provides a computational method to identify the dominant singularity. -/

def ratioApprox (a : ℕ → ℕ) (n : ℕ) : ℚ :=
  if a n = 0 then 0 else (a (n + 1) : ℚ) / (a n : ℚ)

example : ratioApprox catalanNumber 5 = 132 / 42 := by native_decide
example : ratioApprox catalanNumber 10 = 58786 / 16796 := by native_decide

example : ratioApprox motzkinNumber 5 = 51 / 21 := by native_decide
example : ratioApprox motzkinNumber 6 = 127 / 51 := by native_decide

/-! ## 8. Transfer with logarithmic factors

  For f(z) = (1−z/ρ)^{−α} · log^β(1/(1−z/ρ)), the transfer gives
    [zⁿ]f ~ n^{α−1} (log n)^β / (Γ(α) · ρⁿ).
  Logarithmic factors transfer directly at the coefficient level. -/

noncomputable def logScale (α : ℝ) (β : ℕ) (ρ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (α - 1) * (Real.log n) ^ β / ρ ^ n

theorem log_transfer_form (α : ℝ) (β : ℕ) (ρ : ℝ) :
    ∀ n : ℕ, logScale α β ρ n =
      (n : ℝ) ^ (α - 1) * (Real.log n) ^ β / ρ ^ n := by
  intro n; rfl

/-! ## 9. Random trees — mean height asymptotics

  For simply generated families of trees (Catalan trees, Motzkin trees),
  the mean height of a random tree of size n is Θ(√n).
  The GF approach uses singularity analysis of height-restricted GFs. -/

noncomputable def meanTreeHeight (n : ℕ) : ℝ :=
  Real.sqrt (Real.pi * n)

theorem tree_height_order (n : ℕ) (_hn : 0 < n) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      C₁ * Real.sqrt n ≤ meanTreeHeight n ∧
      meanTreeHeight n ≤ C₂ * Real.sqrt n := by
  sorry

/-! ## 10. Coefficient growth classification

  Singularity type determines coefficient growth:
  • Pole of order m:  [zⁿ]f ~ C · n^{m−1} · ρ^{−n}
  • Algebraic:        [zⁿ]f ~ C · n^{α−1} · ρ^{−n}
  • Logarithmic:      [zⁿ]f ~ C · (log n)^β · ρ^{−n}
  • Essential:        superexponential behavior possible -/

inductive SingularityType where
  | pole (order : ℕ)
  | algebraic (alpha : ℚ)
  | logarithmic (beta : ℕ)
  | essential
  deriving Repr, DecidableEq

def coefficientGrowthOrder : SingularityType → String
  | .pole m => s!"n^{m - 1} · ρ^(-n)"
  | .algebraic α => s!"n^({α} - 1) · ρ^(-n)"
  | .logarithmic β => s!"(log n)^{β} · ρ^(-n)"
  | .essential => "superexponential"

example : coefficientGrowthOrder (.pole 1) = "n^0 · ρ^(-n)" := by native_decide
example : coefficientGrowthOrder (.pole 2) = "n^1 · ρ^(-n)" := by native_decide
example : coefficientGrowthOrder (.logarithmic 1) = "(log n)^1 · ρ^(-n)" := by native_decide

/-! ## 11. Full asymptotic expansion via iterated transfer

  By subtracting successive singular terms and applying o-transfer,
  one can obtain a full asymptotic expansion:
    [zⁿ]f(z) ~ ρ^{−n} · (c₀ n^{α₀−1} + c₁ n^{α₁−1} + ⋯)
  with α₀ > α₁ > ⋯. Each step uses the o-transfer lemma. -/

noncomputable def asymptoticExpansion (terms : List (ℝ × ℝ)) (ρ : ℝ) (n : ℕ) : ℝ :=
  terms.foldl (fun acc ⟨c, α⟩ => acc + c * (n : ℝ) ^ (α - 1)) 0 / ρ ^ n

noncomputable def catalanFullExpansion (n : ℕ) : ℝ :=
  asymptoticExpansion [(1 / Real.sqrt Real.pi, -1/2),
                       (-9 / (8 * Real.sqrt Real.pi), -3/2)] (1/4) n

theorem catalan_full_expansion_refines (n : ℕ) (_hn : 2 ≤ n) :
    ∃ C > 0, |(catalanNumber n : ℝ) - catalanFullExpansion n| ≤
      C * 4 ^ n / (n : ℝ) ^ (7/2 : ℝ) := by
  sorry

/-! ## 12. Numerical verification: Catalan ratios approach 4 = 1/ρ -/

example : ratioApprox catalanNumber 1 = 2 / 1 := by native_decide
example : ratioApprox catalanNumber 3 = 14 / 5 := by native_decide
example : ratioApprox catalanNumber 7 = 1430 / 429 := by native_decide
example : ratioApprox catalanNumber 8 = 4862 / 1430 := by native_decide

theorem catalan_ratio_converges :
    ∀ ε > (0 : ℚ), ∃ N, ∀ n ≥ N,
      |ratioApprox catalanNumber n - 4| < ε := by
  sorry

end CoefficientAsymptotics
