import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateBose

/-!
# Mass-rate campaign: the Bose antiderivative (R10 bricks 8–12)

`F(x) = 1/x − 1/(eˣ−1)` has `F′ = boseReg0` on `(0,∞)`, `F → 0` at `∞`, `F → 1/2` at `0⁺`
(squeeze via the order-3 bound), with the finite FTC `∫_a^b boseReg0 = F(b) − F(a)`.
Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The antiderivative `1/x − 1/(eˣ−1)`. -/
noncomputable def boseAntideriv (x : ℝ) : ℝ :=
  1 / x - 1 / (Real.exp x - 1)

/-- `F′ = boseReg0` on `(0,∞)`. -/
lemma boseAntideriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt boseAntideriv (boseReg0 x) x := by
  have hy : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hypos : 0 < Real.exp x - 1 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => 1 / x) (-(1 / x ^ 2)) x := by
    have := hasDerivAt_inv hx.ne'
    simpa [one_div] using this
  have hexp : HasDerivAt (fun x : ℝ => Real.exp x - 1) (Real.exp x) x := by
    simpa using (Real.hasDerivAt_exp x).sub_const 1
  have h2 : HasDerivAt (fun x : ℝ => 1 / (Real.exp x - 1))
      (-(Real.exp x / (Real.exp x - 1) ^ 2)) x := by
    have := hexp.inv hypos.ne'
    simpa [one_div, div_eq_mul_inv] using this
  have hsub := h1.sub h2
  have heq : -(1 / x ^ 2) - -(Real.exp x / (Real.exp x - 1) ^ 2) = boseReg0 x := by
    rw [boseReg0, boseKernel_eq_exp_form hx]
    ring
  rw [← heq]
  exact hsub

/-- `boseReg0` is continuous at every `x > 0`. -/
lemma boseReg0_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt boseReg0 x := by
  have hlt : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hden : (1 - Real.exp (-x)) ^ 2 ≠ 0 := by
    have : 0 < 1 - Real.exp (-x) := by linarith
    positivity
  have hK : ContinuousAt boseKernel x := by
    apply ContinuousAt.div
    · exact (Real.continuous_exp.comp continuous_neg).continuousAt
    · exact ((continuous_const.sub (Real.continuous_exp.comp continuous_neg)).pow 2).continuousAt
    · exact hden
  have hI : ContinuousAt (fun y : ℝ => 1 / y ^ 2) x := by
    apply ContinuousAt.div continuousAt_const ((continuous_pow 2).continuousAt)
    exact pow_ne_zero 2 hx.ne'
  exact hK.sub hI

/-- Finite FTC for `boseReg0`. -/
lemma intervalIntegral_boseReg0_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, boseReg0 x = boseAntideriv b - boseAntideriv a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact boseAntideriv_hasDerivAt (lt_of_lt_of_le ha hx.1)
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (boseReg0_continuousAt (lt_of_lt_of_le ha hx.1)).continuousWithinAt

/-- `F → 0` at `∞`. -/
lemma boseAntideriv_tendsto_atTop : Tendsto boseAntideriv atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero
  have h2 : Tendsto (fun x : ℝ => 1 / (Real.exp x - 1)) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun x : ℝ => Real.exp x - 1) atTop atTop :=
      tendsto_atTop_add_const_right _ (-1) Real.tendsto_exp_atTop
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hcomp
    simpa [one_div, Function.comp] using this
  have hfin := h1.sub h2
  rw [sub_zero] at hfin
  refine hfin.congr fun x => ?_
  rw [boseAntideriv]

/-- `F → 1/2` at `0⁺`. -/
lemma boseAntideriv_tendsto_zero_right :
    Tendsto boseAntideriv (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
  have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio 1, isOpen_Iio, by norm_num,
      fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  -- numerator limit: (eˣ−1−x)/x² → 1/2
  have hnum : Tendsto (fun x : ℝ => (Real.exp x - 1 - x) / x ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2)) := by
    have hbound : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
        ‖(Real.exp x - 1 - x) / x ^ 2 - 1 / 2‖ ≤ x := by
      filter_upwards [hmem] with x hx
      have hδ := exp_sub_one_sub_self_sq_bound hx.1.le hx.2
      rw [Real.norm_eq_abs]
      have hxne : x ≠ 0 := hx.1.ne'
      have heq : (Real.exp x - 1 - x) / x ^ 2 - 1 / 2
          = (Real.exp x - 1 - x - x ^ 2 / 2) / x ^ 2 := by
        field_simp
      rw [heq, abs_div, abs_of_pos (pow_pos hx.1 2),
        div_le_iff₀ (pow_pos hx.1 2)]
      calc |Real.exp x - 1 - x - x ^ 2 / 2| ≤ x ^ 3 := hδ
        _ = x * x ^ 2 := by ring
    have hz := squeeze_zero_norm' hbound hx0
    have hfin := hz.add (tendsto_const_nhds (x := (1 / 2 : ℝ)))
    rw [zero_add] at hfin
    refine hfin.congr fun x => ?_
    ring
  -- denominator limit: (eˣ−1)/x → 1
  have hden : Tendsto (fun x : ℝ => (Real.exp x - 1) / x)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hbound : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
        ‖(Real.exp x - 1) / x - 1‖ ≤ 2 * x := by
      filter_upwards [hmem] with x hx
      have hδ := exp_sub_one_sub_self_sq_bound hx.1.le hx.2
      have hδhi := (abs_le.mp hδ).2
      have hδlo := (abs_le.mp hδ).1
      rw [Real.norm_eq_abs]
      have hxne : x ≠ 0 := hx.1.ne'
      have heq : (Real.exp x - 1) / x - 1 = (Real.exp x - 1 - x) / x := by
        field_simp
      rw [heq, abs_div, abs_of_pos hx.1, div_le_iff₀ hx.1]
      rw [abs_le]
      constructor
      · nlinarith [hx.1.le, hx.2]
      · nlinarith [hx.1.le, hx.2]
    have h2x : Tendsto (fun x : ℝ => 2 * x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc := hx0.const_mul (2 : ℝ)
      rwa [mul_zero] at hc
    have hz := squeeze_zero_norm' hbound h2x
    have hfin := hz.add (tendsto_const_nhds (x := (1 : ℝ)))
    rw [zero_add] at hfin
    refine hfin.congr fun x => ?_
    ring
  -- quotient
  have hquot := hnum.div hden (by norm_num)
  rw [div_one] at hquot
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : (0 : ℝ) < x := hx
  have hy : 0 < Real.exp x - 1 := by
    have := Real.add_one_lt_exp (x := x) hxpos.ne'
    linarith
  have hxne : x ≠ 0 := hxpos.ne'
  have hyne : Real.exp x - 1 ≠ 0 := hy.ne'
  rw [Pi.div_apply, boseAntideriv]
  field_simp

end AnalyticCombinatorics.Ch8.Partitions.Erdos
