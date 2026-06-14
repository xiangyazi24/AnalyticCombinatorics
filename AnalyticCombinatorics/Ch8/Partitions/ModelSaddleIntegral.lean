import AnalyticCombinatorics.Ch8.Partitions.ErdosConstant

/-!
# Model-saddle integrand: density + derivative (HR brick 4, integral comparison)

`saddleDensity t x = e^{C√x − tx}/x` is the continuous density whose `∫_{Ioi 1}` the
discrete `modelSaddle` sum is compared against (via `riemann_sum_Ioi_sub_integral_bound`,
applied to the shift `x ↦ saddleDensity t (x+1)` to avoid the `1/x` singularity at `0`).

This file establishes the density and its derivative
`saddleDensity'(t,x) = saddleDensity t x · (C/(2√x) − t − 1/x)`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology Real MeasureTheory
open AnalyticCombinatorics.Ch8.Partitions.Erdos

noncomputable section

/-- Continuous density `e^{C√x − tx}/x`. -/
noncomputable def saddleDensity (t x : ℝ) : ℝ :=
  Real.exp (C * Real.sqrt x - t * x) / x

/-- Derivative of the model-saddle density on `x > 0`. -/
lemma saddleDensity_hasDerivAt {t x : ℝ} (hx : 0 < x) :
    HasDerivAt (saddleDensity t)
      (saddleDensity t x * (C / (2 * Real.sqrt x) - t - 1 / x)) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsne : Real.sqrt x ≠ 0 := ne_of_gt hsqrtpos
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hxne
  have h2 : HasDerivAt (fun y : ℝ => t * y) t x := by simpa using (hasDerivAt_id x).const_mul t
  have hg : HasDerivAt (fun y : ℝ => C * Real.sqrt y - t * y)
      (C * (1 / (2 * Real.sqrt x)) - t) x := (hsqrt.const_mul C).sub h2
  have hnum := hg.exp
  have hdiv := hnum.div (hasDerivAt_id x) hxne
  simp only [id_eq] at hdiv
  convert hdiv using 1
  simp only [saddleDensity]
  field_simp

/-- Real-`y` AM–GM exponent bound: `C√y − sy ≤ C²/(2s) − (s/2)y` for `y ≥ 0`, `s > 0`. -/
lemma saddle_exponent_bound_real {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 0 ≤ y) :
    C * Real.sqrt y - s * y ≤ C ^ 2 / (2 * s) - (s / 2) * y := by
  have hsy : s ^ 2 * Real.sqrt y ^ 2 = s ^ 2 * y := by rw [Real.sq_sqrt hy]
  rw [le_sub_iff_add_le, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * s)]
  nlinarith [sq_nonneg (C - s * Real.sqrt y), hsy]

/-- The shifted density `x ↦ saddleDensity s (x+1)` is integrable on `(0,∞)` (`s > 0`).
The shift removes the `1/x` singularity, and the integrand decays by the exponent bound. -/
lemma integrableOn_saddleDensity_shift {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => saddleDensity s (x + 1)) (Set.Ioi (0 : ℝ)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => saddleDensity s (x + 1))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    unfold saddleDensity
    fun_prop
  have hdom : IntegrableOn
      (fun x : ℝ => Real.exp (C ^ 2 / (2 * s)) * Real.exp (-(s / 2) * (x + 1))) (Set.Ioi 0) := by
    have hbase : IntegrableOn (fun x : ℝ => Real.exp (-(s / 2) * x)) (Set.Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 (half_pos hs)
    have h2 : IntegrableOn
        (fun x : ℝ => (Real.exp (C ^ 2 / (2 * s)) * Real.exp (-(s / 2))) * Real.exp (-(s / 2) * x))
        (Set.Ioi 0) :=
      hbase.const_mul (Real.exp (C ^ 2 / (2 * s)) * Real.exp (-(s / 2)))
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x _
    simp only [← Real.exp_add]
    congr 1
    ring
  refine Integrable.mono' hdom hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  have hx0 : 0 < x := hx
  have hx1 : (1 : ℝ) ≤ x + 1 := by linarith
  have hden : (0 : ℝ) < x + 1 := by linarith
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by unfold saddleDensity; exact div_nonneg (Real.exp_pos _).le hden.le)]
  unfold saddleDensity
  calc Real.exp (C * Real.sqrt (x + 1) - s * (x + 1)) / (x + 1)
      ≤ Real.exp (C * Real.sqrt (x + 1) - s * (x + 1)) := by
        rw [div_le_iff₀ hden]
        nlinarith [Real.exp_pos (C * Real.sqrt (x + 1) - s * (x + 1)), hx1]
    _ ≤ Real.exp (C ^ 2 / (2 * s)) * Real.exp (-(s / 2) * (x + 1)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have := saddle_exponent_bound_real hs (y := x + 1) (by linarith)
        linarith

/-- Derivative of the shifted density (chain rule with `y ↦ y+1`). -/
lemma saddleDensity_shift_hasDerivAt {s x : ℝ} (hx : -1 < x) :
    HasDerivAt (fun y : ℝ => saddleDensity s (y + 1))
      (saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - 1 / (x + 1))) x := by
  have hxp1 : 0 < x + 1 := by linarith
  have h := (saddleDensity_hasDerivAt (t := s) hxp1).comp x ((hasDerivAt_id x).add_const 1)
  simpa using h

/-- The shifted-density derivative is integrable on `(0,∞)`: the bracket factor is bounded
by `C/2 + s + 1`, so `|f'| ≤ (C/2+s+1)·saddleDensity`, which is integrable. -/
lemma integrableOn_saddleDensity_shift_deriv {s : ℝ} (hs : 0 < s) :
    IntegrableOn
      (fun x : ℝ => saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - 1 / (x + 1)))
      (Set.Ioi (0 : ℝ)) := by
  have hCpos : 0 < C := C_pos
  have hg : IntegrableOn (fun x : ℝ => (C / 2 + s + 1) * saddleDensity s (x + 1)) (Set.Ioi 0) :=
    (integrableOn_saddleDensity_shift hs).const_mul _
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => saddleDensity s (x + 1) * (C / (2 * Real.sqrt (x + 1)) - s - 1 / (x + 1)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    unfold saddleDensity
    fun_prop
  refine Integrable.mono' hg hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  have hx0 : 0 < x := hx
  have hden : (0 : ℝ) < x + 1 := by linarith
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (x + 1) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ x + 1 by linarith)
    rwa [Real.sqrt_one] at h
  have hsd_nonneg : 0 ≤ saddleDensity s (x + 1) := by
    unfold saddleDensity; exact div_nonneg (Real.exp_pos _).le hden.le
  have hfac : |C / (2 * Real.sqrt (x + 1)) - s - 1 / (x + 1)| ≤ C / 2 + s + 1 := by
    have hsp : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.mpr hden
    have h1 : C / (2 * Real.sqrt (x + 1)) ≤ C / 2 := by
      rw [div_mul_eq_div_div]
      exact div_le_self (div_nonneg hCpos.le (by norm_num)) hsq1
    have h1' : 0 ≤ C / (2 * Real.sqrt (x + 1)) := by positivity
    have h2 : 1 / (x + 1) ≤ 1 := by rw [div_le_one hden]; linarith
    have h2' : 0 ≤ 1 / (x + 1) := by positivity
    rw [abs_le]
    constructor <;> nlinarith [hCpos.le, hs.le]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsd_nonneg]
  calc saddleDensity s (x + 1) * |C / (2 * Real.sqrt (x + 1)) - s - 1 / (x + 1)|
      ≤ saddleDensity s (x + 1) * (C / 2 + s + 1) :=
        mul_le_mul_of_nonneg_left hfac hsd_nonneg
    _ = (C / 2 + s + 1) * saddleDensity s (x + 1) := by ring

/-- Finite-interval `u = v²` substitution: `∫₁^{B²} e^{C√u−su}/u du = ∫₁^B 2e^{Cv−sv²}/v dv`.
The image `[1,B²] ⊂ (0,∞)` dodges the `1/u` singularity, so `integral_comp_mul_deriv'` applies. -/
lemma modelSaddleInterval_substitution {s B : ℝ} (hB : 1 ≤ B) :
    (∫ u in (1 : ℝ)..(B ^ 2), saddleDensity s u)
      = ∫ v in (1 : ℝ)..B, 2 * Real.exp (C * v - s * v ^ 2) / v := by
  have hderiv : ∀ v ∈ Set.uIcc (1 : ℝ) B, HasDerivAt (fun y : ℝ => y ^ 2) (2 * v) v := by
    intro v _; simpa using hasDerivAt_pow 2 v
  have hcont' : ContinuousOn (fun v : ℝ => 2 * v) (Set.uIcc 1 B) :=
    (continuous_const.mul continuous_id).continuousOn
  have hcontg : ContinuousOn (saddleDensity s) ((fun y : ℝ => y ^ 2) '' Set.uIcc 1 B) := by
    refine ContinuousOn.mono (s := Set.Ioi (0 : ℝ)) ?_ ?_
    · unfold saddleDensity
      refine ContinuousOn.div ?_ continuousOn_id ?_
      · exact (by fun_prop : Continuous fun u : ℝ => Real.exp (C * Real.sqrt u - s * u)).continuousOn
      · intro u hu; exact ne_of_gt hu
    · rintro u ⟨v, hv, rfl⟩
      rw [Set.uIcc_of_le hB] at hv
      have hv1 : (1 : ℝ) ≤ v := hv.1
      show (0 : ℝ) < v ^ 2
      nlinarith [hv1]
  have hsub := intervalIntegral.integral_comp_mul_deriv' hderiv hcont' hcontg
  simp only [one_pow] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [Set.uIcc_of_le hB] at hv
  have hv1 : (1 : ℝ) ≤ v := hv.1
  simp only [Function.comp, saddleDensity]
  rw [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ v)]
  field_simp

end

end AnalyticCombinatorics.Ch8.Partitions
