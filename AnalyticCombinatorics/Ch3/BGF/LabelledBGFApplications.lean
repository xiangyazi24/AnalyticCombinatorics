import AnalyticCombinatorics.Ch3.BGF.LabelledSetMarked
import AnalyticCombinatorics.Ch2.EGF.Applications

/-!
# Ch3 -- Bivariate EGF applications for marked labelled sets

Cheap specializations of `ParamClass.begf_setMarked_exp` for the standard
labelled examples from Chapter 2.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

/-- Set partitions marked by the number of blocks:
`exp(u (exp z - 1))`. -/
theorem ParamClass.begf_setPartitionsByBlocks :
    (ParamClass.setMarked CombClass.posInt).begf =
      (PowerSeries.exp ℚ[X]).subst
        (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (PowerSeries.exp ℚ - 1)) := by
  have h := ParamClass.begf_setMarked_exp CombClass.posInt
    (by simp [CombClass.counts_posInt])
  rwa [CombClass.egf_posInt] at h

/-- Involutions marked by the number of SET components:
`exp(u (z + z^2 / 2))`. -/
theorem ParamClass.begf_involutionsByComponents :
    (ParamClass.setMarked CombClass.parts12).begf =
      (PowerSeries.exp ℚ[X]).subst
        (PowerSeries.C (Polynomial.X : ℚ[X]) *
          liftU (PowerSeries.X + (2⁻¹ : ℚ) • PowerSeries.X ^ 2)) := by
  have h := ParamClass.begf_setMarked_exp CombClass.parts12
    (by simp [CombClass.counts_parts12])
  rwa [CombClass.egf_parts12_egf] at h

end AnalyticCombinatorics.Ch1
