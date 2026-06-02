import Mathlib
import AnalyticCombinatorics.Ch4.Analytic.Bridge

open Complex
open scoped NNReal ENNReal

noncomputable section

theorem coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hR : 0 < R)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 R)) (n : ℕ) :
    p.coeff n =
      (2 * Real.pi * I : ℂ)⁻¹ •
        circleIntegral
          (fun z => ((1 : ℂ) / (z - 0)) ^ n • (z - 0)⁻¹ • f z)
          0 R := by
  have hq : HasFPowerSeriesAt f (cauchyPowerSeries f 0 R) 0 := by
    have hnn : 0 < ((⟨R, hR.le⟩ : ℝ≥0)) := by
      exact_mod_cast hR
    exact (hd.hasFPowerSeriesOnBall hnn).hasFPowerSeriesAt
  have hpq : p = cauchyPowerSeries f 0 R := hp.eq_formalMultilinearSeries hq
  calc
    p.coeff n = (cauchyPowerSeries f 0 R).coeff n := by rw [hpq]
    _ = (cauchyPowerSeries f 0 R n fun _ => (1 : ℂ)) := by rfl
    _ = _ := by exact cauchyPowerSeries_apply f 0 R n 1

theorem powerSeries_coeff_eq_cauchy_circleIntegral
    (F : PowerSeries ℂ) {R : ℝ}
    (hR : 0 < R)
    (hd : DifferentiableOn ℂ (PowerSeries.toFMLS F).sum (Metric.closedBall 0 R))
    (hball : 0 < (PowerSeries.toFMLS F).radius) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n F =
      (2 * Real.pi * I : ℂ)⁻¹ •
        circleIntegral
          (fun z =>
            ((1 : ℂ) / (z - 0)) ^ n • (z - 0)⁻¹ • (PowerSeries.toFMLS F).sum z)
          0 R := by
  have hp : HasFPowerSeriesAt (PowerSeries.toFMLS F).sum (PowerSeries.toFMLS F) 0 :=
    (PowerSeries.hasFPowerSeriesOnBall_analyticSum F hball).hasFPowerSeriesAt
  rw [← PowerSeries.coeff_toFMLS F n]
  exact coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt hR hp hd n

theorem norm_coeff_le_of_circleIntegral
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R M : ℝ}
    (hR : 0 < R)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 R))
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖p.coeff n‖ ≤ M * R⁻¹ ^ n := by
  let g : ℂ → ℂ := fun z => ((1 : ℂ) / (z - 0)) ^ n • (z - 0)⁻¹ • f z
  have hcoeff :
      p.coeff n = (2 * Real.pi * I : ℂ)⁻¹ • circleIntegral g 0 R := by
    simpa [g] using coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt hR hp hd n
  rw [hcoeff]
  calc
    ‖(2 * Real.pi * I : ℂ)⁻¹ • circleIntegral g 0 R‖
        ≤ R * (M * R⁻¹ ^ (n + 1)) := by
      refine circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
        hR.le ?_
      intro z hz
      have hz_norm : ‖z‖ = R := by
        simpa using (Metric.mem_sphere.1 hz)
      calc
        ‖g z‖ = R⁻¹ ^ n * R⁻¹ * ‖f z‖ := by
          simp [g, norm_pow, div_eq_mul_inv, hz_norm, inv_pow, mul_assoc]
        _ ≤ R⁻¹ ^ n * R⁻¹ * M := by
          exact mul_le_mul_of_nonneg_left (hM z hz)
            (mul_nonneg (pow_nonneg (inv_nonneg.mpr hR.le) n)
              (inv_nonneg.mpr hR.le))
        _ = M * R⁻¹ ^ (n + 1) := by
          rw [pow_succ]
          ring
    _ = M * R⁻¹ ^ n := by
      rw [pow_succ]
      field_simp [hR.ne']
