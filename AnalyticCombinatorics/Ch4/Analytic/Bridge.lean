import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

open Filter ENNReal
open scoped PowerSeries Topology NNReal ENNReal

noncomputable section

namespace PowerSeries

def toFMLS (f : PowerSeries ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => PowerSeries.coeff (R := ℂ) n f)

def analyticSum (f : PowerSeries ℂ) (z : ℂ) : ℂ :=
  (toFMLS f).sum z

def mapℂ : PowerSeries ℚ →+* PowerSeries ℂ :=
  PowerSeries.map (algebraMap ℚ ℂ)

@[simp] lemma coeff_toFMLS (f : PowerSeries ℂ) (n : ℕ) :
    (toFMLS f).coeff n = PowerSeries.coeff (R := ℂ) n f := by
  simp [toFMLS]

@[simp] lemma coeff_mapℂ (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (mapℂ f) =
      algebraMap ℚ ℂ (PowerSeries.coeff (R := ℚ) n f) := by
  simp [mapℂ]

lemma analyticSum_eq_tsum (f : PowerSeries ℂ) (z : ℂ) :
    analyticSum f z =
      ∑' n : ℕ, PowerSeries.coeff (R := ℂ) n f * z ^ n := by
  simpa [analyticSum, toFMLS, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul]
    using
      (FormalMultilinearSeries.ofScalars_sum_eq
        (fun n => PowerSeries.coeff (R := ℂ) n f) z)

lemma hasSum_analyticSum_of_mem (f : PowerSeries ℂ) {z : ℂ}
    (hz : z ∈ Metric.eball 0 (toFMLS f).radius) :
    HasSum
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f * z ^ n)
      (analyticSum f z) := by
  simpa [analyticSum, toFMLS, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul, mul_comm] using (toFMLS f).hasSum hz

lemma hasFPowerSeriesOnBall_analyticSum (f : PowerSeries ℂ)
    (h : 0 < (toFMLS f).radius) :
    HasFPowerSeriesOnBall (analyticSum f) (toFMLS f) 0 (toFMLS f).radius := by
  simpa [analyticSum] using (toFMLS f).hasFPowerSeriesOnBall h

lemma analyticAt_analyticSum (f : PowerSeries ℂ)
    (h : 0 < (toFMLS f).radius) :
    AnalyticAt ℂ (analyticSum f) 0 := by
  exact (hasFPowerSeriesOnBall_analyticSum f h).analyticAt

@[simp] lemma nnnorm_toFMLS_apply (f : PowerSeries ℂ) (n : ℕ) :
    ‖toFMLS f n‖₊ = ‖PowerSeries.coeff (R := ℂ) n f‖₊ := by
  apply NNReal.eq
  simp [toFMLS]

theorem radius_toFMLS_inv_eq_limsup (f : PowerSeries ℂ) :
    (toFMLS f).radius⁻¹ =
      limsup
        (fun n : ℕ =>
          ((‖PowerSeries.coeff (R := ℂ) n f‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) :
            ℝ≥0∞))
        atTop := by
  rw [FormalMultilinearSeries.radius_inv_eq_limsup]
  refine Filter.limsup_congr (Eventually.of_forall ?_)
  intro n
  rw [nnnorm_toFMLS_apply]

end PowerSeries
