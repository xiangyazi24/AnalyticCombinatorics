import AnalyticCombinatorics.Ch8.Partitions.GaussianTail

/-!
# Gaussian tail asymptotic (HR brick 4): `∫_{Ioi 1} e^{-s(v-v₀)²}/v ~ (2√π/C)√s`

Splits at the saddle cutoff `cut = C/(4s)`: the right part gives the main
`(2√s/C)·√π` (via `modelGaussCut_eq` + DCT); the left strip is exponentially negligible.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
open scoped Topology Interval

noncomputable section

/-- The full Gaussian tail integral after completing the square. -/
noncomputable def gaussianTailFull (s : ℝ) : ℝ :=
  ∫ v in Set.Ioi (1 : ℝ), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v

/-- Right (central) part: ratio → 1. -/
lemma gaussianTail_cut_ratio_tendsto :
    Tendsto
      (fun s : ℝ =>
        (∫ v in Set.Ioi (gaussianTailCut s), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hK : Tendsto (fun s : ℝ => (∫ u : ℝ, gaussianTailKernel s u) / Real.sqrt Real.pi)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by positivity
    have h := gaussianTailKernel_integral_tendsto.div_const (Real.sqrt Real.pi)
    simpa [hsqrtpi] using h
  refine hK.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hCpos : 0 < C := C_pos
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hsqrtpi : (0 : ℝ) < Real.sqrt Real.pi := by positivity
  rw [modelGaussCut_eq hspos]
  field_simp

/-- `(s⁻¹)^{3/2} = (s·√s)⁻¹`. -/
lemma inv_rpow_three_halves {s : ℝ} (hs : 0 < s) :
    (s⁻¹) ^ ((3 : ℝ) / 2) = (s * Real.sqrt s)⁻¹ := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
    ← Real.sqrt_eq_rpow, Real.sqrt_inv, ← mul_inv]

/-- The exponential-decay bound function `(C/4s)·e^{-(C²/16)/s}/((2√π/C)√s) → 0`. -/
lemma gaussianTail_strip_bound_tendsto_zero :
    Tendsto
      (fun s : ℝ =>
        (C / (4 * s)) * Real.exp (-(C ^ 2 / 16) * s⁻¹) / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hCpos : 0 < C := C_pos
  have hc : 0 < C ^ 2 / 16 := by positivity
  have hcomp : Tendsto
      (fun σ : ℝ => σ ^ ((3 : ℝ) / 2) * Real.exp (-(C ^ 2 / 16) * σ)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 / 2) (C ^ 2 / 16) hc
  have hmul := (hcomp.comp tendsto_inv_nhdsGT_zero).const_mul (C ^ 2 / (8 * Real.sqrt Real.pi))
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hsqrtpi : (0 : ℝ) < Real.sqrt Real.pi := by positivity
  simp only [Function.comp_apply]
  rw [inv_rpow_three_halves hspos]
  field_simp
  ring

end

end AnalyticCombinatorics.Ch8.Partitions
