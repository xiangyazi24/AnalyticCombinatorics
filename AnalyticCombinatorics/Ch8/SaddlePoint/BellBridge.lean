import AnalyticCombinatorics.Ch8.SaddlePoint.Bell
import AnalyticCombinatorics.Ch4.Analytic.SubstComp

open scoped PowerSeries

noncomputable section

theorem bellCarrier_toFMLS_eq_analyticBellSeries :
    PowerSeries.toFMLS bellCarrier = analyticBellSeries := by
  rw [bellCarrier_eq_complex_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp]
  · change (PowerSeries.toFMLS expCarrier).comp
        (PowerSeries.toFMLS (PowerSeries.exp ℂ - 1)) =
      analyticBellSeries
    rw [expCarrier_toFMLS_eq_expSeries]
    have hinner : PowerSeries.toFMLS (PowerSeries.exp ℂ - 1) =
        expSeriesC - constFormalMultilinearSeries ℂ ℂ (1 : ℂ) := by
      ext n
      cases n <;>
        simp [PowerSeries.toFMLS, expSeriesC, NormedSpace.expSeries_eq_ofScalars,
          constFormalMultilinearSeries]
    rw [hinner]
  · simp

theorem bell_egf_coeff_le
    {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (AnalyticCombinatorics.Ch1.CombClass.posInt.set.counts n : ℝ) / n.factorial ≤
      Real.exp (Real.exp r - 1) / r ^ n :=
  bell_egf_coeff_le_of_composition_bridge hr bellCarrier_toFMLS_eq_analyticBellSeries

