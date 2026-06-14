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

open Filter Topology Real
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

end

end AnalyticCombinatorics.Ch8.Partitions
