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

end

end AnalyticCombinatorics.Ch8.Partitions
