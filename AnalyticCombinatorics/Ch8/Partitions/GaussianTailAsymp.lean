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

/-- `cut s = C/(4s) → ∞`, so eventually `1 ≤ cut s`. -/
lemma eventually_one_le_cut : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 1 ≤ gaussianTailCut s := by
  have hto : Tendsto gaussianTailCut (𝓝[>] (0 : ℝ)) atTop := by
    unfold gaussianTailCut
    have hinv : Tendsto (fun s : ℝ => s⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
    have h2 : Tendsto (fun s : ℝ => C / 4 * s⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      Tendsto.const_mul_atTop (div_pos C_pos (by norm_num)) hinv
    refine h2.congr (fun s => ?_); rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  exact hto.eventually_ge_atTop 1

/-- `e^{-s(v-v₀)²}/v` integrable on `(1,∞)` (dominated by the shifted Gaussian). -/
lemma integrableOn_gaussShift_div_Ioi1 {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v) (Set.Ioi (1 : ℝ)) := by
  have hmeas : AEStronglyMeasurable
      (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    apply Measurable.aestronglyMeasurable; fun_prop
  refine (integrable_gaussShift hs).integrableOn.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with v hv
  have hv1 : (1 : ℝ) < v := hv
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
  nlinarith [Real.exp_pos (-s * (v - C / (2 * s)) ^ 2), hv1]

/-- Left strip ratio → 0. -/
lemma gaussianTail_left_ratio_tendsto_zero :
    Tendsto
      (fun s : ℝ =>
        (∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
          / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hCpos : 0 < C := C_pos
  refine squeeze_zero' ?_ ?_ gaussianTail_strip_bound_tendsto_zero
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := hs
    have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
    have hsqrtpi : (0 : ℝ) < Real.sqrt Real.pi := by positivity
    have hi : 0 ≤ ∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s),
        Real.exp (-s * (v - C / (2 * s)) ^ 2) / v :=
      setIntegral_nonneg measurableSet_Ioc (fun v hv => by
        have : (0 : ℝ) < v := lt_trans one_pos hv.1; positivity)
    have hdenpos : (0 : ℝ) < (2 * Real.sqrt Real.pi / C) * Real.sqrt s := by positivity
    exact div_nonneg hi hdenpos.le
  · filter_upwards [self_mem_nhdsWithin, eventually_one_le_cut] with s hs hcutge
    have hspos : 0 < s := hs
    have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
    have hsqrtpi : (0 : ℝ) < Real.sqrt Real.pi := by positivity
    have hdenpos : (0 : ℝ) < (2 * Real.sqrt Real.pi / C) * Real.sqrt s := by positivity
    have hpt : ∀ v ∈ Set.Ioc (1 : ℝ) (gaussianTailCut s),
        ‖Real.exp (-s * (v - C / (2 * s)) ^ 2) / v‖ ≤ Real.exp (-(C ^ 2 / 16) * s⁻¹) := by
      intro v hv
      have hv1 : (1 : ℝ) < v := hv.1
      have hvpos : 0 < v := lt_trans one_pos hv1
      have hvle : v ≤ C / (4 * s) := by rw [gaussianTailCut] at *; exact hv.2
      have hkey : (C / (4 * s)) ^ 2 ≤ (v - C / (2 * s)) ^ 2 := by
        have h1 : v - C / (2 * s) ≤ -(C / (4 * s)) := by
          have hcc : C / (4 * s) = C / (2 * s) - C / (4 * s) := by field_simp; ring
          nlinarith [hvle, hcc]
        nlinarith [h1, sq_nonneg (v - C / (2 * s))]
      have hcl : C ^ 2 ≤ 16 * s ^ 2 * (v - C / (2 * s)) ^ 2 := by
        have he : (C / (4 * s)) ^ 2 = C ^ 2 / (16 * s ^ 2) := by ring
        rw [he, div_le_iff₀ (by positivity : (0 : ℝ) < 16 * s ^ 2)] at hkey
        linarith [hkey]
      have hexpbound : Real.exp (-s * (v - C / (2 * s)) ^ 2) ≤ Real.exp (-(C ^ 2 / 16) * s⁻¹) := by
        apply Real.exp_le_exp.mpr
        rw [neg_mul, neg_mul, neg_le_neg_iff]
        have hsc : s * s⁻¹ = 1 := mul_inv_cancel₀ hspos.ne'
        nlinarith [hcl, hsc, hspos]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc Real.exp (-s * (v - C / (2 * s)) ^ 2) / v
          ≤ Real.exp (-s * (v - C / (2 * s)) ^ 2) / 1 := by gcongr
        _ = Real.exp (-s * (v - C / (2 * s)) ^ 2) := by rw [div_one]
        _ ≤ Real.exp (-(C ^ 2 / 16) * s⁻¹) := hexpbound
    have hbound := norm_setIntegral_le_of_norm_le_const
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) hpt
    rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc (fun v hv => by
      have : (0 : ℝ) < v := lt_trans one_pos hv.1; positivity))] at hbound
    have hμ : volume.real (Set.Ioc (1 : ℝ) (gaussianTailCut s)) ≤ C / (4 * s) := by
      rw [volume_real_Ioc, max_eq_left (by linarith [hcutge] : (0 : ℝ) ≤ gaussianTailCut s - 1),
        gaussianTailCut]
      linarith
    rw [div_le_iff₀ hdenpos]
    calc ∫ v in Set.Ioc (1 : ℝ) (gaussianTailCut s), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v
        ≤ Real.exp (-(C ^ 2 / 16) * s⁻¹) * volume.real (Set.Ioc (1 : ℝ) (gaussianTailCut s)) := hbound
      _ ≤ Real.exp (-(C ^ 2 / 16) * s⁻¹) * (C / (4 * s)) :=
          mul_le_mul_of_nonneg_left hμ (Real.exp_pos _).le
      _ = (C / (4 * s)) * Real.exp (-(C ^ 2 / 16) * s⁻¹)
            / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s)
            * ((2 * Real.sqrt Real.pi / C) * Real.sqrt s) := by field_simp

/-- **Gaussian tail asymptotic.** `∫_{Ioi 1} e^{-s(v-v₀)²}/v ~ (2√π/C)√s`. -/
lemma gaussianTail_asymp :
    Tendsto (fun s : ℝ => gaussianTailFull s / ((2 * Real.sqrt Real.pi / C) * Real.sqrt s))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hsum := gaussianTail_left_ratio_tendsto_zero.add gaussianTail_cut_ratio_tendsto
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_one_le_cut] with s hs hcutge
  have hspos : 0 < s := hs
  have hint1 := integrableOn_gaussShift_div_Ioi1 hspos
  have hIoc : IntegrableOn (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      (Set.Ioc (1 : ℝ) (gaussianTailCut s)) := hint1.mono_set (fun v hv => hv.1)
  have hIoi : IntegrableOn (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      (Set.Ioi (gaussianTailCut s)) := hint1.mono_set (fun v hv => lt_of_le_of_lt hcutge hv)
  have hdisj : Disjoint (Set.Ioc (1 : ℝ) (gaussianTailCut s)) (Set.Ioi (gaussianTailCut s)) := by
    refine Set.disjoint_left.mpr (fun v hv1 hv2 => ?_)
    exact absurd (Set.mem_Ioi.mp hv2) (not_lt.mpr hv1.2)
  have hunion := setIntegral_union hdisj measurableSet_Ioi hIoc hIoi
  rw [Set.Ioc_union_Ioi_eq_Ioi hcutge] at hunion
  rw [← add_div]
  unfold gaussianTailFull
  rw [hunion]

end

end AnalyticCombinatorics.Ch8.Partitions
