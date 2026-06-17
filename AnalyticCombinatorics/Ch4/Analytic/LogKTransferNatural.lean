import AnalyticCombinatorics.Ch4.Analytic.LogKAsymp
import AnalyticCombinatorics.Ch4.Analytic.LogKFaithful
import AnalyticCombinatorics.Ch4.Analytic.LittleOTransfer

/-!
# General logᵏ transfer — natural-remainder form

Capstone of the general logᵏ singularity hierarchy.  For `k ≥ 1`, the natural residual
`o(|1-z|^{-α}·log^k(1/|1-z|))`:

  f - C·(1-z)^{-α}·(-log(1-z))^k = o(|1-z|^{-α}·log^k(1/|1-z|))
    ⟹  [zⁿ]f ~ C·n^{α-1}/Γ(α)·(log n)^k.

Generalizes `logSq_transfer_theorem_natural_remainder` (k = 2) to arbitrary `k ≥ 1`,
built on LogKCoeff (coefficient identity), LogKFaithful (faithfulness), LogKAsymp
(asymptotic scale), and the logᵏ-weighted little-o circle transfer in LittleOTransfer.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

namespace AnalyticCombinatorics

/-- **Natural-remainder general logᵏ transfer** (`k ≥ 1`). -/
theorem logK_transfer_theorem_natural_remainder
    {α : ℝ} {C : ℂ} {R φ : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : 1 < α) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (k : ℕ) (hk : 1 ≤ k)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * logKSingularityFun (α : ℂ) k z‖ * ‖(1 : ℂ) - z‖ ^ α
        * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ k : ℝ) : ℂ)) := by
  classical
  set q : FormalMultilinearSeries ℂ ℂ ℂ := PowerSeries.toFMLS (logKGF (α : ℂ) k) with hq
  have hαneg : ∀ m : ℕ, (α : ℂ) ≠ -m := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hqcoeff : ∀ n, q.coeff n = (logKSingularityScale α k n : ℂ) := by
    intro n
    rw [hq, PowerSeries.coeff_toFMLS, coeff_logKGF_eq_logKCoeffℂ (α : ℂ) hαneg k n,
      ← logKSingularityScale_cast]
  have hmain : (fun n : ℕ => C * q.coeff n)
      ~[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ k : ℝ) : ℂ)) := by
    have hcomplex : (fun n : ℕ => (logKSingularityScale α k n : ℂ))
        ~[atTop] (fun n : ℕ => (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ k : ℝ) : ℂ)) := by
      rw [ofReal_isEquivalent_iff]
      simpa [mul_assoc] using logKSingularityScale_isEquivalent hα k
    have hmul := (Asymptotics.IsEquivalent.refl (u := fun _ : ℕ => C)).mul hcomplex
    simp only [hqcoeff]; exact hmul
  have hpg : HasFPowerSeriesAt (fun z : ℂ => f z - C • logKSingularityFun (α : ℂ) k z) (p - C • q) 0 :=
    hp.sub ((logKSingularityFun_hasFPowerSeriesAt (α : ℂ) k).const_smul (c := C))
  have hΔg : AnalyticOnNhd ℂ (fun z : ℂ => f z - C • logKSingularityFun (α : ℂ) k z)
      (DeltaDomainArg R φ) :=
    hΔ.sub ((analyticOnNhd_logKSingularityFun_deltaDomain k hφ0
      (by linarith [Real.pi_pos] : φ < Real.pi)).const_smul (c := C))
  have herr_norm : (fun n : ℕ => ‖(p - C • q).coeff n‖)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1) * (Real.log n) ^ k) := by
    refine coeff_norm_isLittleO_atTop_of_delta_littleO_logK_beta_gt_one
      (R := R) (φ := φ) (β := α) (k := k)
      (f := fun z : ℂ => f z - C • logKSingularityFun (α : ℂ) k z) (p := p - C • q)
      hR hφ0 hφ2 hpg hΔg ?_ hα hk
    simpa [smul_eq_mul] using hsing
  have hΓ : 0 < Real.Gamma α := Real.Gamma_pos_of_pos (by linarith)
  have hCnorm : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have hscale_bigO : (fun n : ℕ => (n : ℝ) ^ (α - 1) * (Real.log n) ^ k)
      =O[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ k : ℝ) : ℂ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨Real.Gamma α / ‖C‖, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1R
    have hpow : 0 ≤ (n : ℝ) ^ (α - 1) := (Real.rpow_pos_of_pos (by linarith) _).le
    rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    rw [show Real.Gamma α / ‖C‖ * (‖C‖ * ((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ k))
      = (n : ℝ) ^ (α - 1) * (Real.log n) ^ k by field_simp]
  have herr_target : (fun n : ℕ => (p - C • q).coeff n)
      =o[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ k : ℝ) : ℂ)) :=
    (Asymptotics.IsLittleO.of_norm_left herr_norm).trans_isBigO hscale_bigO
  have hsum : (fun n : ℕ => C * q.coeff n + (p - C • q).coeff n)
      ~[atTop] (fun n : ℕ => C * (((n : ℝ) ^ (α - 1) / Real.Gamma α * (Real.log n) ^ k : ℝ) : ℂ)) :=
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
    rw [hcs]; ring
  exact hdecomp.trans_isEquivalent hsum

end AnalyticCombinatorics
