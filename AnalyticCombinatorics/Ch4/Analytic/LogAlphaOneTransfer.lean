import AnalyticCombinatorics.Ch4.Analytic.LogKTransferNatural
import AnalyticCombinatorics.Ch4.Analytic.LittleOTransfer
import AnalyticCombinatorics.Ch4.Analytic.OneSubCpowMul

/-!
# Boundary logarithmic transfer at α = 1

This file records the first α≤1 transfer: the strong-remainder logarithmic transfer at
`α = 1`, whose model coefficient scale is `log n`.
-/

noncomputable section

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

namespace AnalyticCombinatorics

private lemma shiftedHarmonicℂ_one_cast (n : ℕ) :
    ((shiftedHarmonic (1 : ℝ) n : ℝ) : ℂ) =
      shiftedHarmonicℂ ((1 : ℝ) : ℂ) n := by
  rw [shiftedHarmonic, shiftedHarmonicℂ, Complex.ofReal_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast]

private lemma logSingularityCoeff_one_eq_shiftedHarmonic (n : ℕ) :
    logSingularityCoeff (1 : ℝ) n = shiftedHarmonic (1 : ℝ) n := by
  apply Complex.ofReal_injective
  calc
    ((logSingularityCoeff (1 : ℝ) n : ℝ) : ℂ)
        = logSingularityCoeffℂ (((1 : ℝ) : ℂ)) n := logSingularityCoeff_cast (1 : ℝ) n
    _ = ((shiftedHarmonic (1 : ℝ) n : ℝ) : ℂ) := by
        have hbin : binCoeffℂ (((1 : ℝ) : ℂ)) n = 1 := by
          simpa using binCoeffℂ_one n
        rw [logSingularityCoeffℂ, hbin, ← shiftedHarmonicℂ_one_cast n, one_mul]

/-- At `α = 1`, the first-log singularity coefficient scale is equivalent to `log n`. -/
theorem logSingularityScale_one_isEquivalent :
    (fun n : ℕ => logSingularityCoeff (1 : ℝ) n) ~[atTop]
      (fun n : ℕ => Real.log n) := by
  have hshift := shiftedHarmonic_isEquivalent_log (α := (1 : ℝ)) (by norm_num)
  refine hshift.congr_left ?_
  exact Eventually.of_forall fun n => (logSingularityCoeff_one_eq_shiftedHarmonic n).symm

/-- **Boundary strong-remainder logarithmic transfer at `α = 1`.**

If `f - C·(1-z)⁻¹·(-log(1-z)) = o(|1-z|⁻¹)` in a Δ-domain, then
`[zⁿ]f ~ C·log n`. -/
theorem log_transfer_alpha_eq_one_strong_remainder
    {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logSingularityFun (1 : ℂ) z‖ * ‖(1 : ℂ) - z‖)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((Real.log n : ℝ) : ℂ))) := by
  classical
  set q : FormalMultilinearSeries ℂ ℂ ℂ :=
    PowerSeries.toFMLS (logSingularityGF (1 : ℂ)) with hq
  have hαneg : ∀ m : ℕ, ((1 : ℝ) : ℂ) ≠ -m := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hqcoeff : ∀ n, q.coeff n = (logSingularityCoeff (1 : ℝ) n : ℂ) := by
    intro n
    rw [hq, PowerSeries.coeff_toFMLS, logSingularityCoeff_eq_coeff_logSingularityGF hαneg,
      Complex.ofReal_one]
  have hmain : (fun n : ℕ => C * q.coeff n)
      ~[atTop] (fun n : ℕ => C * (((Real.log n : ℝ) : ℂ))) := by
    have hcomplex : (fun n : ℕ => (logSingularityCoeff (1 : ℝ) n : ℂ))
        ~[atTop] (fun n : ℕ => ((Real.log n : ℝ) : ℂ)) := by
      rw [ofReal_isEquivalent_iff]
      exact logSingularityScale_one_isEquivalent
    have hmul := (Asymptotics.IsEquivalent.refl (u := fun _ : ℕ => C)).mul hcomplex
    simp only [hqcoeff]
    exact hmul
  have hpg : HasFPowerSeriesAt
      (fun z : ℂ => f z - C • logSingularityFun (1 : ℂ) z) (p - C • q) 0 :=
    hp.sub ((logSingularityFun_hasFPowerSeriesAt (1 : ℂ)).const_smul (c := C))
  have hφπ : φ < Real.pi := by linarith [hφ2, Real.pi_pos]
  have hΔg : AnalyticOnNhd ℂ
      (fun z : ℂ => f z - C • logSingularityFun (1 : ℂ) z)
      (DeltaDomainArg R φ) :=
    hΔ.sub ((analyticOnNhd_logSingularityFun_deltaDomain
      (α := (1 : ℂ)) (R := R) (φ := φ) hφ0 hφπ).const_smul (c := C))
  have herr_norm : (fun n : ℕ => ‖(p - C • q).coeff n‖)
      =o[atTop] (fun n : ℕ => Real.log n) := by
    refine coeff_norm_isLittleO_atTop_of_delta_littleO_beta_eq_one
      (R := R) (φ := φ)
      (f := fun z : ℂ => f z - C • logSingularityFun (1 : ℂ) z)
      (p := p - C • q) hR hφ0 hφ2 hpg hΔg ?_
    simpa [smul_eq_mul] using hsing
  have hCnorm : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have hscale_bigO : (fun n : ℕ => Real.log n)
      =O[atTop] (fun n : ℕ => C * (((Real.log n : ℝ) : ℂ))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨‖C‖⁻¹, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1R
    calc
      ‖Real.log n‖ = Real.log n := Real.norm_of_nonneg hlogn
      _ = ‖C‖⁻¹ * ‖C * (((Real.log n : ℝ) : ℂ))‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlogn]
          field_simp [hCnorm.ne']
      _ ≤ ‖C‖⁻¹ * ‖C * (((Real.log n : ℝ) : ℂ))‖ := le_rfl
  have herr_target : (fun n : ℕ => (p - C • q).coeff n)
      =o[atTop] (fun n : ℕ => C * (((Real.log n : ℝ) : ℂ))) :=
    (Asymptotics.IsLittleO.of_norm_left herr_norm).trans_isBigO hscale_bigO
  have hsum : (fun n : ℕ => C * q.coeff n + (p - C • q).coeff n)
      ~[atTop] (fun n : ℕ => C * (((Real.log n : ℝ) : ℂ))) :=
    hmain.add_isLittleO herr_target
  have hdecomp : (fun n : ℕ => p.coeff n)
      =ᶠ[atTop] (fun n : ℕ => C * q.coeff n + (p - C • q).coeff n) := by
    refine Eventually.of_forall fun n => ?_
    show p.coeff n = C * q.coeff n + (p - C • q).coeff n
    have hcs : (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
      change (p n - (C • q) n) 1 = p n 1 - C * q.coeff n
      rw [FormalMultilinearSeries.smul_apply, ContinuousMultilinearMap.sub_apply,
        ContinuousMultilinearMap.smul_apply]
      change p.coeff n - C • q.coeff n = p.coeff n - C * q.coeff n
      simp [smul_eq_mul]
    rw [hcs]
    ring
  exact hdecomp.trans_isEquivalent hsum

end AnalyticCombinatorics
