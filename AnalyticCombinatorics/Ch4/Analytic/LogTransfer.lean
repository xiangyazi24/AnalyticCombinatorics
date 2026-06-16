import AnalyticCombinatorics.Ch4.Analytic.LogSingularity
import AnalyticCombinatorics.Ch4.Analytic.TransferTheorem
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics
import AnalyticCombinatorics.Ch4.Analytic.Bridge

/-!
# Flajolet–Odlyzko transfer with a logarithmic factor (strong-remainder form)

The algebraic transfer theorem (`transfer_theorem_re_alpha_gt_one`) handles `f(z) ~ C(1−z)^{−α}`.
This file adds the *logarithmic* singularity transfer

  `f(z) ~ C (1−z)^{−α} log(1/(1−z))   ⟹   [zⁿ]f ~ C · n^{α−1}/Γ(α) · log n`,

in the **strong-remainder** form: the residual is assumed `o(|1−z|^{−α})` (one log factor stronger
than the natural `o(|1−z|^{−α} log)`).  This lets the *existing* algebraic Darboux descent
(`coeff_norm_isLittleO_atTop_of_delta_littleO_beta_gt_one`) supply the coefficient error
`o(n^{α−1}) = o(n^{α−1} log n)`, with no new contour estimate.  The model coefficient asymptotic is the
banked `logSingularityCoeff_isEquivalent`.

The analytic faithfulness of the model `logSingularityFun α = (1−z)^{−α}·(−log(1−z))` (its
`HasFPowerSeriesAt` = `logSingularityGF α`, and delta-domain analyticity) is carried here as explicit
hypotheses; it is discharged separately (`LogTransferBranch`).
-/

noncomputable section

open Complex Filter Asymptotics
open scoped Topology BigOperators

/-- The logarithmic-singularity model function `(1−z)^{−α} · (−log(1−z))`. -/
noncomputable def logSingularityFun (α : ℂ) : ℂ → ℂ :=
  fun z => (1 - z) ^ (-α) * (-Complex.log (1 - z))

/-- `n^{α−1}` is negligible against the log-weighted scale `n^{α−1} log n`. -/
lemma algebraic_scale_isLittleO_log_scale {α : ℝ} :
    (fun n : ℕ => (n : ℝ) ^ (α - 1))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1) * Real.log n) := by
  have hlog : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n : ℕ => Real.log n) :=
    (isLittleO_one_left_iff ℝ).mpr
      (tendsto_norm_atTop_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have h := (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ) ^ (α - 1)) atTop).mul_isLittleO hlog
  simpa using h

/-- **Strong-remainder logarithmic transfer theorem.**  For real `α > 1`, if `f` is analytic on a
delta-domain with `f − C·(1−z)^{−α}·(−log(1−z))` of order `o(|1−z|^{−α})` near `1`, then
`[zⁿ]f ~ C · n^{α−1}/Γ(α) · log n`.  (Model faithfulness `hp_log`, `hΔ_log` is supplied externally.) -/
theorem log_transfer_theorem_strong_remainder
    {α : ℝ} {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hp_log : HasFPowerSeriesAt (logSingularityFun (α : ℂ))
      (PowerSeries.toFMLS (logSingularityGF (α : ℂ))) 0)
    (hΔ_log : AnalyticOnNhd ℂ (logSingularityFun (α : ℂ)) (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logSingularityFun (α : ℂ) z‖ * ‖(1 : ℂ) - z‖ ^ α)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by
  classical
  set q : FormalMultilinearSeries ℂ ℂ ℂ := PowerSeries.toFMLS (logSingularityGF (α : ℂ)) with hq
  -- α (real, >1) is never a nonpositive integer
  have hαneg : ∀ m : ℕ, (α : ℂ) ≠ -m := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  -- coefficient bridge: q.coeff n = (logSingularityCoeff α n : ℂ)
  have hqcoeff : ∀ n, q.coeff n = (logSingularityCoeff α n : ℂ) := by
    intro n
    rw [hq, logSingularityCoeff_eq_coeff_logSingularityGF hαneg, PowerSeries.coeff_toFMLS]
  -- main term ~ target
  have hmain : (fun n : ℕ => C * q.coeff n)
      ~[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by
    have hcomplex : (fun n : ℕ => (logSingularityCoeff α n : ℂ))
        ~[atTop] (fun n : ℕ => (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by
      rw [ofReal_isEquivalent_iff]
      simpa [mul_assoc] using logSingularityCoeff_isEquivalent hα
    have hconst : (fun _ : ℕ => C) ~[atTop] (fun _ : ℕ => C) := Asymptotics.IsEquivalent.refl
    have hmul := hconst.mul hcomplex
    simp only [hqcoeff]
    exact hmul
  -- subtract the model and apply the banked algebraic descent (β = α)
  have hpg : HasFPowerSeriesAt (fun z : ℂ => f z - C • logSingularityFun (α : ℂ) z) (p - C • q) 0 :=
    hp.sub (hp_log.const_smul (c := C))
  have hΔg : AnalyticOnNhd ℂ (fun z : ℂ => f z - C • logSingularityFun (α : ℂ) z)
      (DeltaDomainArg R φ) :=
    hΔ.sub (hΔ_log.const_smul (c := C))
  have herr_norm : (fun n : ℕ => ‖(p - C • q).coeff n‖)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1)) := by
    refine coeff_norm_isLittleO_atTop_of_delta_littleO_beta_gt_one
      (R := R) (φ := φ) (β := α) (f := fun z : ℂ => f z - C • logSingularityFun (α : ℂ) z)
      (p := p - C • q) hR hφ0 hφ2 hpg hΔg ?_ hα
    simpa [smul_eq_mul] using hsing
  -- n^{α-1} =O target (target grows like n^{α-1} log n)
  have hscale_bigO : (fun n : ℕ => (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨Real.Gamma α / ‖C‖, ?_⟩
    have hΓpos : 0 < Real.Gamma α := Real.Gamma_pos_of_pos (by linarith)
    have he1 : Real.exp 1 < 3 := by have h := Real.exp_one_lt_d9; linarith
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hnpos : 0 < (n : ℝ) := by positivity
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog1 : 1 ≤ Real.log n := by rw [Real.le_log_iff_exp_le hnpos]; linarith
    have hpow_pos : 0 < (n : ℝ) ^ (α - 1) := Real.rpow_pos_of_pos hnpos _
    have hCpos : 0 < ‖C‖ := norm_pos_iff.mpr hC
    have hnorm_target :
        ‖C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)‖
          = ‖C‖ * ((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [Real.norm_of_nonneg hpow_pos.le, hnorm_target]
    have hrhs :
        Real.Gamma α / ‖C‖ * (‖C‖ * ((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n))
          = (n : ℝ) ^ (α - 1) * Real.log n := by
      field_simp
    rw [hrhs]
    simpa using mul_le_mul_of_nonneg_left hlog1 hpow_pos.le
  have herr_target : (fun n : ℕ => (p - C • q).coeff n)
      =o[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) :=
    (Asymptotics.IsLittleO.of_norm_left herr_norm).trans_isBigO hscale_bigO
  -- assemble
  have hsum : (fun n : ℕ => C * q.coeff n + (p - C • q).coeff n)
      ~[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * Real.log n : ℝ) : ℂ)) :=
    hmain.add_isLittleO herr_target
  have hdecomp : (fun n : ℕ => p.coeff n)
      =ᶠ[atTop] (fun n : ℕ => C * q.coeff n + (p - C • q).coeff n) := by
    refine Eventually.of_forall fun n => ?_
    show p.coeff n = C * q.coeff n + (p - C • q).coeff n
    have hcs : (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
      change (p n - (C • q) n) 1 = p n 1 - C * q.coeff n
      rw [FormalMultilinearSeries.smul_apply,
        ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
      change p.coeff n - C • q.coeff n = p.coeff n - C * q.coeff n
      simp [smul_eq_mul]
    rw [hcs]; ring
  exact hdecomp.trans_isEquivalent hsum
