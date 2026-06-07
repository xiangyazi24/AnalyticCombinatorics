import Mathlib

/-!
# R7 cover: reusable summability of the per-scale defect bound

The Erdős record-cover assembly accumulates one-step pullback losses
`Δ_N = (|boundaryTerm N| + M·|kernelMass N − 1| + M·R_N)/μ` along a chain of running-max
predecessors whose `√N` strictly decreases by a fixed amount per step.  Summing the losses over
that `√`-spaced chain converges because, as a function of the scale `t = √N`, each piece of `Δ`
is summable in `t`:

* `|boundaryTerm N| ≤ σ(N)·e^{−C√N} ≤ N²·e^{−Ct} = t⁴·e^{−Ct}` — polynomial × exponential decay,
* `M·R_N = M·N³·e^{−(C/10)√N} = M·t⁶·e^{−(C/10)t}` — polynomial × exponential decay,
* `M·|kernelMass N − 1| ≤ M·K/N = M·K/t²` — inverse-square.

This file proves the two chain-independent summability building blocks (`Σ tᵏ e^{−ct}` and
`Σ 1/(t+1)²`) and their sum.  The chain-dependent bookkeeping (how the `Δ`'s are indexed by the
`√`-spaced chain) lives in the cover-assembly file.  Opus-authored.
-/

noncomputable section

open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `Σ_t tᵏ · e^{−c t}` converges for `c > 0`: polynomial times geometric. -/
lemma summable_pow_mul_exp_neg {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Summable (fun t : ℕ => (t : ℝ) ^ k * Real.exp (-c * (t : ℝ))) := by
  have hr : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc Real.exp (-c) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hsum := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hr
  refine hsum.congr (fun t => ?_)
  rw [← Real.exp_nat_mul, mul_comm (t : ℝ) (-c)]

/-- `Σ_t B/(t+1)²` converges (the `1/n` kernel-mass rate, summed over the `√`-spaced chain). -/
lemma summable_const_div_succ_sq (B : ℝ) :
    Summable (fun t : ℕ => B / ((t : ℝ) + 1) ^ 2) := by
  have h2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (le_refl 2)
  have hshift : Summable (fun t : ℕ => 1 / (((t : ℝ) + 1)) ^ 2) := by
    have h := (h2.comp_injective (add_left_injective 1))
    refine h.congr (fun t => ?_)
    simp only [Function.comp]
    push_cast
    ring
  simpa [div_eq_mul_inv, mul_comm] using hshift.mul_left B

/-- The full per-scale defect majorant `B/(t+1)² + tᵏ e^{−c₁t} + t^l e^{−c₂t}` is summable.
This is exactly the shape of `Δ` as a function of the scale `t = √N`
(`B = M·K`, the two poly-exp terms = boundary + far-tail remainder). -/
lemma summable_defect_scale {c₁ c₂ B : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (k l : ℕ) :
    Summable (fun t : ℕ =>
      B / ((t : ℝ) + 1) ^ 2
        + (t : ℝ) ^ k * Real.exp (-c₁ * (t : ℝ))
        + (t : ℝ) ^ l * Real.exp (-c₂ * (t : ℝ))) := by
  exact ((summable_const_div_succ_sq B).add (summable_pow_mul_exp_neg hc₁ k)).add
    (summable_pow_mul_exp_neg hc₂ l)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
