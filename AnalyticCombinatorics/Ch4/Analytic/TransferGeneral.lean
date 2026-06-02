import AnalyticCombinatorics.Ch4.Analytic.LittleODescent
import AnalyticCombinatorics.Ch4.Analytic.SingularityGeneral
import AnalyticCombinatorics.Ch4.Analytic.DeltaDomain
import Mathlib.Analysis.Analytic.Binomial

/-!
# General singularity-analysis transfer theorem

This file assembles the general Darboux little-o transfer estimate with the
standard coefficient scale for `(1 - z)^{-α}`. Unlike the restricted theorem,
there is no lower bound on `α.re`; the only exclusion is that `α` is not a
nonpositive integer, exactly the hypothesis needed for the standard scale.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

private lemma coeff_sub_const_smul (C : ℂ)
    (p q : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
  change (p n - (C • q) n) 1 = p n 1 - C * q.coeff n
  rw [FormalMultilinearSeries.smul_apply]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
  change p.coeff n - C • q.coeff n = p.coeff n - C * q.coeff n
  simp [smul_eq_mul]

private lemma main_term_norm_eventually {α C : ℂ} :
    ∀ᶠ n : ℕ in atTop,
      ‖C * (n : ℂ) ^ (α - 1) / Complex.Gamma α‖ =
        (‖C‖ / ‖Complex.Gamma α‖) * (n : ℝ) ^ (α.re - 1) := by
  refine (eventually_ne_atTop 0).mono ?_
  intro n hn
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hpow : ‖(n : ℂ) ^ (α - 1)‖ = (n : ℝ) ^ ((α - 1).re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (n : ℝ)) hnpos (α - 1)
  have hre : (α - 1).re = α.re - 1 := by simp
  calc
    ‖C * (n : ℂ) ^ (α - 1) / Complex.Gamma α‖
        = ‖C‖ * ‖(n : ℂ) ^ (α - 1)‖ / ‖Complex.Gamma α‖ := by
          rw [norm_div, norm_mul]
    _ = ‖C‖ * ((n : ℝ) ^ ((α - 1).re)) / ‖Complex.Gamma α‖ := by rw [hpow]
    _ = (‖C‖ / ‖Complex.Gamma α‖) * (n : ℝ) ^ (α.re - 1) := by
          rw [hre]
          ring

private lemma rpow_scale_isBigO_main_term {α C : ℂ}
    (hC : C ≠ 0) (hα : ∀ m : ℕ, α ≠ -m) :
    (fun n : ℕ => (n : ℝ) ^ (α.re - 1)) =O[atTop]
      (fun n : ℕ => C * (n : ℂ) ^ (α - 1) / Complex.Gamma α) := by
  let K : ℝ := ‖C‖ / ‖Complex.Gamma α‖
  have hΓ : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero hα
  have hKpos : 0 < K := by
    exact div_pos (norm_pos_iff.mpr hC) (norm_pos_iff.mpr hΓ)
  have hKne : K ≠ 0 := ne_of_gt hKpos
  refine Asymptotics.isBigO_iff.mpr ⟨K⁻¹, ?_⟩
  filter_upwards [main_term_norm_eventually (α := α) (C := C)] with n hn_norm
  have hscale_nonneg : 0 ≤ (n : ℝ) ^ (α.re - 1) :=
    Real.rpow_nonneg (by exact_mod_cast Nat.zero_le n) _
  calc
    ‖(n : ℝ) ^ (α.re - 1)‖ = (n : ℝ) ^ (α.re - 1) :=
      Real.norm_of_nonneg hscale_nonneg
    _ = K⁻¹ * (K * (n : ℝ) ^ (α.re - 1)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hKne, one_mul]
    _ = K⁻¹ * ‖C * (n : ℂ) ^ (α - 1) / Complex.Gamma α‖ := by
      rw [hn_norm]
    _ ≤ K⁻¹ * ‖C * (n : ℂ) ^ (α - 1) / Complex.Gamma α‖ := le_rfl

theorem transfer_theorem {α C : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : ∀ m : ℕ, α ≠ -m) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ)
    (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * (1 - z) ^ (-α)‖ * ‖(1 : ℂ) - z‖ ^ (α.re))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (n : ℂ) ^ (α - 1) / Complex.Gamma α) := by
  let h : ℂ → ℂ := fun z => (1 - z) ^ (-α)
  let q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ => Ring.choose (α + n - 1) n)
  have hφπ : φ < Real.pi := by
    nlinarith [Real.pi_pos]
  have hh : HasFPowerSeriesAt h q 0 := by
    have hraw := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero α).hasFPowerSeriesAt
    convert hraw using 1
    ext z
    dsimp [h]
    rw [Complex.cpow_neg, inv_eq_one_div]
  have hΔh : AnalyticOnNhd ℂ h (DeltaDomainArg R φ) := by
    simpa [h] using
      (analyticOnNhd_one_sub_cpow_deltaDomain (α := α) (R := R) (φ := φ) hφ0 hφπ)
  have hpg : HasFPowerSeriesAt (fun z : ℂ => f z - C • h z) (p - C • q) 0 :=
    hp.sub (hh.const_smul (c := C))
  have hΔg : AnalyticOnNhd ℂ (fun z : ℂ => f z - C • h z) (DeltaDomainArg R φ) :=
    hΔ.sub (hΔh.const_smul (c := C))
  have herr_norm : (fun n : ℕ => ‖(p - C • q).coeff n‖) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (α.re - 1)) := by
    refine coeff_norm_isLittleO_atTop_of_delta_littleO
      (R := R) (φ := φ) (β := α.re) (f := fun z : ℂ => f z - C • h z)
      (p := p - C • q) hR hφ0 hφ2 hpg hΔg ?_
    simpa [h, smul_eq_mul] using hsing
  let main : ℕ → ℂ := fun n => C * q.coeff n
  let err : ℕ → ℂ := fun n => (p - C • q).coeff n
  let target : ℕ → ℂ := fun n => C * (n : ℂ) ^ (α - 1) / Complex.Gamma α
  have hmain : main ~[atTop] target := by
    have hchoose := coeff_oneDivOneSubCpow_isEquivalent (α := α) hα
    have hconst : (fun _ : ℕ => C) ~[atTop] (fun _ : ℕ => C) :=
      Asymptotics.IsEquivalent.refl
    have hmul := hconst.mul hchoose
    simpa [main, target, q, Pi.mul_apply, mul_div_assoc] using hmul
  have herr_scale : err =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α.re - 1)) := by
    exact Asymptotics.IsLittleO.of_norm_left (by simpa [err] using herr_norm)
  have herr_target : err =o[atTop] target := by
    exact herr_scale.trans_isBigO
      (rpow_scale_isBigO_main_term (α := α) (C := C) hC hα)
  have hsum : (main + err) ~[atTop] target := hmain.add_isLittleO herr_target
  have hdecomp : (fun n : ℕ => p.coeff n) =ᶠ[atTop] main + err :=
    Eventually.of_forall fun n => by
      dsimp [main, err]
      rw [coeff_sub_const_smul]
      ring
  exact hdecomp.trans_isEquivalent hsum
