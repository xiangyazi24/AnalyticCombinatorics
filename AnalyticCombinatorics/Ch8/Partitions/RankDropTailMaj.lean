import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Ceiling-escape brick 1: the rank-drop tail majorant as a clean summable sequence

This file packages the banked rank-drop tail majorant `C₀·(t+1)·e^{−γt}` (the upper bound of
`Pker_rankDrop_tail_majorant`) as a reusable nonnegative, summable sequence with a vanishing shifted
tail.  It is pure exponential-polynomial summability — no analytic number theory, no `Pker`.

* `rankDropTailMaj γ C₀ t = C₀·(t+1)·e^{−γt}`  (nonneg for `C₀ ≥ 0`);
* `rankDropTailMaj_summable` (for `γ > 0`): the sequence is summable;
* `rankDropTailMaj_tail_tendsto_zero` (for `γ > 0`): `A ↦ ∑'_i U(A+i) → 0` as `A → ∞`.

NEW file; depends only on Mathlib.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The rank-drop tail majorant sequence `C₀·(t+1)·e^{−γt}`. -/
noncomputable def rankDropTailMaj (γ C₀ : ℝ) (t : ℕ) : ℝ :=
  C₀ * ((t : ℝ) + 1) * Real.exp (-γ * (t : ℝ))

/-- Nonnegativity of the tail majorant (given `0 ≤ C₀`). -/
lemma rankDropTailMaj_nonneg {γ C₀ : ℝ} (hC₀ : 0 ≤ C₀) (t : ℕ) :
    0 ≤ rankDropTailMaj γ C₀ t := by
  unfold rankDropTailMaj
  have h1 : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) ≤ Real.exp (-γ * (t : ℝ)) := (Real.exp_pos _).le
  positivity

/-- `e^{−γt} = (e^{−γ})^t`, the geometric form used for summability. -/
lemma rankDropTailMaj_exp_pow (γ : ℝ) (t : ℕ) :
    Real.exp (-γ * (t : ℝ)) = (Real.exp (-γ)) ^ t := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- For `γ > 0`, the tail majorant is summable: `(t+1)·r^t` with `r = e^{−γ} ∈ (0,1)`. -/
lemma rankDropTailMaj_summable {γ C₀ : ℝ} (hγ : 0 < γ) :
    Summable (fun t : ℕ => rankDropTailMaj γ C₀ t) := by
  set r : ℝ := Real.exp (-γ) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr]
    calc Real.exp (-γ) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
  -- ∑ (t+1)·r^t = ∑ t·r^t + ∑ r^t, both summable
  have hpow1 : Summable (fun t : ℕ => (t : ℝ) ^ 1 * r ^ t) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hpow0 : Summable (fun t : ℕ => (t : ℝ) ^ 0 * r ^ t) :=
    summable_pow_mul_geometric_of_norm_lt_one 0 hnorm
  have hsum : Summable (fun t : ℕ => ((t : ℝ) + 1) * r ^ t) := by
    have := hpow1.add hpow0
    apply this.congr
    intro t
    simp only [pow_one, pow_zero, one_mul]
    ring
  have hC : Summable (fun t : ℕ => C₀ * (((t : ℝ) + 1) * r ^ t)) := hsum.mul_left C₀
  apply hC.congr
  intro t
  unfold rankDropTailMaj
  rw [rankDropTailMaj_exp_pow, ← hr]
  ring

/-- The shifted tail `A ↦ ∑'_i U(A+i)` of a summable nonnegative sequence vanishes as `A → ∞`. -/
lemma rankDropTailMaj_tail_tendsto_zero {γ C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hγ : 0 < γ) :
    Tendsto (fun A : ℕ => ∑' i : ℕ, rankDropTailMaj γ C₀ (A + i)) atTop (𝓝 0) := by
  set U : ℕ → ℝ := fun t => rankDropTailMaj γ C₀ t with hU
  have hsum : Summable U := rankDropTailMaj_summable hγ
  have hUnn : ∀ t, 0 ≤ U t := fun t => rankDropTailMaj_nonneg hC₀ t
  -- ∑'_i U(A+i) = ∑' U − ∑_{range A} U, the partial-sum tail, which → 0.
  have htot : Tendsto (fun A : ℕ => ∑ n ∈ Finset.range A, U n) atTop (𝓝 (∑' n, U n)) :=
    hsum.tendsto_sum_tsum_nat
  have heq : ∀ A : ℕ, (∑' i : ℕ, U (A + i)) = (∑' n, U n) - ∑ n ∈ Finset.range A, U n := by
    intro A
    have hadd := Summable.sum_add_tsum_nat_add A hsum
    -- hadd : (∑ i ∈ range A, U i) + ∑' i, U (i + A) = ∑' i, U i
    have hcomm : (∑' i : ℕ, U (A + i)) = ∑' i : ℕ, U (i + A) := by
      apply tsum_congr; intro i; rw [add_comm]
    rw [hcomm]; linarith [hadd]
  rw [show (0 : ℝ) = (∑' n, U n) - (∑' n, U n) by ring]
  apply (Tendsto.sub tendsto_const_nhds htot).congr
  intro A; rw [heq A]

#print axioms rankDropTailMaj_summable
#print axioms rankDropTailMaj_tail_tendsto_zero

end AnalyticCombinatorics.Ch8.Partitions.Erdos
