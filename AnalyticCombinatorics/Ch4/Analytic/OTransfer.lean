import AnalyticCombinatorics.Ch4.Analytic.CauchyCoeff
import AnalyticCombinatorics.Ch4.Analytic.DeltaGeometry
import AnalyticCombinatorics.Ch4.Analytic.KernelEstimate
import Mathlib

/-!
# O-transfer for Δ-analytic functions, β > 1

This file records the circle-only O-transfer theorem for singular bounds with
exponent `β > 1`.  The proof combines Cauchy coefficient extraction, elementary
Δ-domain geometry, and the reusable circle-kernel integral estimate.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal

noncomputable section

private lemma circle_norm_integral_zero_to_neg_pi (f : ℂ → ℂ) (r : ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap (0 : ℂ) r θ)‖) =
      ∫ θ in (-Real.pi)..Real.pi, ‖f (circleMap (0 : ℂ) r θ)‖ := by
  have hper : Function.Periodic
      (fun θ : ℝ => ‖f (circleMap (0 : ℂ) r θ)‖) (2 * Real.pi) :=
    (periodic_circleMap (0 : ℂ) r).comp (fun z : ℂ => ‖f z‖)
  have h := hper.intervalIntegral_add_eq (-Real.pi) 0
  simpa [two_mul, add_comm, add_left_comm, add_assoc] using h.symm

theorem norm_coeff_le_integral_circle
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (hd : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) (n : ℕ) :
    ‖p.coeff n‖ ≤
      (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
        ∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
  have hq : HasFPowerSeriesAt f (cauchyPowerSeries f (0 : ℂ) r) (0 : ℂ) := by
    have hnn : 0 < ((⟨r, hr.le⟩ : ℝ≥0)) := by
      exact_mod_cast hr
    exact (hd.hasFPowerSeriesOnBall hnn).hasFPowerSeriesAt
  have hpq : p = cauchyPowerSeries f (0 : ℂ) r := hp.eq_formalMultilinearSeries hq
  have hshift := circle_norm_integral_zero_to_neg_pi f r
  have hnorm := norm_cauchyPowerSeries_le f (0 : ℂ) r n
  rw [hpq]
  calc
    ‖(cauchyPowerSeries f (0 : ℂ) r).coeff n‖ =
        ‖cauchyPowerSeries f (0 : ℂ) r n‖ := by
      rw [FormalMultilinearSeries.norm_apply_eq_norm_coef]
    _ ≤ ((2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap (0 : ℂ) r θ)‖) *
        |r|⁻¹ ^ n := hnorm
    _ = (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
        ∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
      rw [abs_of_pos hr, hshift]
      simp [circleMap_zero]
      ring

private lemma one_add_one_div_pow_le_exp {k : ℕ} (hk : 0 < k) :
    (1 + (1 : ℝ) / k) ^ k ≤ Real.exp 1 := by
  have hle : (-(1 : ℝ)) ≤ (k : ℝ) := by
    have hk_nonneg : (0 : ℝ) ≤ k := by positivity
    linarith
  have h := Real.one_sub_div_pow_le_exp_neg (n := k) (t := (-1 : ℝ)) hle
  simpa [sub_eq_add_neg, neg_div, Real.exp_neg] using h

lemma one_sub_inv_pow_nat_le_four {n : ℕ} (hn : 2 ≤ n) :
    (((1 : ℝ) - 1 / n)⁻¹) ^ n ≤ 4 := by
  by_cases hn2 : n = 2
  · subst n
    norm_num
  by_cases hn3 : n = 3
  · subst n
    norm_num
  have hn4 : 4 ≤ n := by omega
  let k : ℕ := n - 1
  have hkpos : 0 < k := by
    dsimp [k]
    omega
  have hk3 : 3 ≤ k := by
    dsimp [k]
    omega
  have hn_eq : n = k + 1 := by
    dsimp [k]
    omega
  rw [hn_eq]
  have hbase : (((1 : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))⁻¹) =
      1 + (1 : ℝ) / k := by
    have hkreal : (k : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hkpos)
    have hk1real : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hkreal, hk1real]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [hbase, pow_succ]
  have hpow : (1 + (1 : ℝ) / k) ^ k ≤ Real.exp 1 :=
    one_add_one_div_pow_le_exp hkpos
  have hfactor : 1 + (1 : ℝ) / k ≤ 4 / 3 := by
    have hkreal : (3 : ℝ) ≤ k := by
      exact_mod_cast hk3
    have hkpos_real : (0 : ℝ) < k := by
      exact_mod_cast hkpos
    have hdiv : (1 : ℝ) / k ≤ 1 / 3 := by
      rw [one_div_le_one_div hkpos_real (by norm_num : (0 : ℝ) < 3)]
      exact hkreal
    linarith
  calc
    (1 + (1 : ℝ) / k) ^ k * (1 + (1 : ℝ) / k)
        ≤ Real.exp 1 * (4 / 3) := by
          exact mul_le_mul hpow hfactor (by positivity) (by positivity)
    _ ≤ 3 * (4 / 3) := by
          exact mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (by norm_num)
    _ = 4 := by norm_num

lemma one_sub_inv_pow_le_four {n : ℕ} (hn : 2 ≤ n) :
    ((1 : ℝ) - 1 / n) ^ (-(n : ℤ)) ≤ 4 := by
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact one_sub_inv_pow_nat_le_four hn

private lemma circlePoint_mem_delta {R φ r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrR : r < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2) (θ : ℝ) :
    ((r : ℂ) * Complex.exp (θ * Complex.I)) ∈ DeltaDomainArg R φ := by
  refine closedBall_subset_deltaDomain hr1 hrR hφ0 hφ2 ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    ‖((r : ℂ) * Complex.exp (θ * Complex.I)) - 0‖
        = r := by
          simp [Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hr0]
    _ ≤ r := le_rfl

private lemma circleKernel_intervalIntegrable {β r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IntervalIntegrable
      (fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β))
      volume (-Real.pi) Real.pi := by
  refine ((by fun_prop :
      Continuous fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖)
    |>.continuousOn.rpow_const ?_).intervalIntegrable
  intro θ _hθ
  left
  have hnorm_exp : ‖Complex.exp (θ * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I θ
  have hne : (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
    intro hzero
    have hmul_eq : (r : ℂ) * Complex.exp (θ * Complex.I) = 1 :=
      (sub_eq_zero.mp hzero).symm
    have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = 1 := by
      rw [hmul_eq, norm_one]
    have habs : |r| = 1 := by
      simpa [norm_mul, hnorm_exp] using hnorm
    have hr_eq_one : r = 1 := by
      simpa [abs_of_nonneg hr0] using habs
    linarith
  exact (norm_pos_iff.mpr hne).ne'

private lemma circleFunction_intervalIntegrable
    {R φ r : ℝ} {f : ℂ → ℂ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hrR : r < R)
    (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ)) :
    IntervalIntegrable
      (fun θ : ℝ => ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
      volume (-Real.pi) Real.pi := by
  have hcont_delta : ContinuousOn f (DeltaDomainArg R φ) :=
    han.differentiableOn.continuousOn
  have hcont_circle : ContinuousOn
      (fun θ : ℝ => f ((r : ℂ) * Complex.exp (θ * Complex.I)))
      (Set.uIcc (-Real.pi) Real.pi) := by
    refine hcont_delta.comp ?_ ?_
    · exact (by fun_prop : Continuous fun θ : ℝ =>
        ((r : ℂ) * Complex.exp (θ * Complex.I))).continuousOn
    · intro θ _hθ
      exact circlePoint_mem_delta hr0 hr1 hrR hφ0 hφ2 θ
  exact hcont_circle.norm.intervalIntegrable

theorem coeff_norm_isBigO_atTop_of_delta_bound_beta_gt_one
    {R φ β M : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hM0 : 0 ≤ M)
    (hbound : ∀ z ∈ DeltaDomainArg R φ,
      ‖f z‖ ≤ M * ‖(1 : ℂ) - z‖ ^ (-β))
    (hβ : 1 < β) :
    (fun n : ℕ => ‖p.coeff n‖) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (β - 1)) := by
  obtain ⟨C, hC0, hC⟩ := circleKernel_integral_bound_nat hβ
  let K : ℝ := (2 * Real.pi)⁻¹ * 4 * M * C
  refine IsBigO.of_bound K ?_
  refine eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℕ) ≤ 2) hn
  have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  let r : ℝ := 1 - (1 : ℝ) / n
  have hr0 : 0 ≤ r := by
    dsimp [r]
    have hdiv : (1 : ℝ) / n ≤ 1 := by
      rw [div_le_one hnpos]
      exact_mod_cast hn1
    linarith
  have hrpos : 0 < r := by
    dsimp [r]
    have htwo_le : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hdiv_lt : (1 : ℝ) / n < 1 := by
      rw [div_lt_one hnpos]
      linarith
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    have hdiv_pos : 0 < (1 : ℝ) / n := div_pos zero_lt_one hnpos
    linarith
  have hrR : r < R := lt_trans hr1 hR
  have hsubset : Metric.closedBall (0 : ℂ) r ⊆ DeltaDomainArg R φ :=
    closedBall_subset_deltaDomain hr1 hrR hφ0 hφ2
  have hd : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r) :=
    han.differentiableOn.mono hsubset
  have hcauchy := norm_coeff_le_integral_circle (p := p) hrpos hp hd n
  have hleft_int := circleFunction_intervalIntegrable (f := f) hr0 hr1 hrR hφ0 hφ2 han
  have hkernel_int := circleKernel_intervalIntegrable (β := β) hr0 hr1
  have hright_int :
      IntervalIntegrable
        (fun θ : ℝ =>
          M * ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β))
        volume (-Real.pi) Real.pi :=
    hkernel_int.const_mul M
  have hInt_le :
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ≤
        ∫ θ in (-Real.pi)..Real.pi,
          M * ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) := by
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      hleft_int hright_int ?_
    intro θ _hθ
    exact hbound _ (circlePoint_mem_delta hr0 hr1 hrR hφ0 hφ2 θ)
  have hkernel_nonneg :
      0 ≤ ∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) := by
    refine intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) ?_
    intro θ _hθ
    positivity
  have hMkernel_nonneg :
      0 ≤ M * (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) :=
    mul_nonneg hM0 hkernel_nonneg
  have hInt_bound :
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ≤
        M * (∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) := by
    calc
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
          ≤ ∫ θ in (-Real.pi)..Real.pi,
              M * ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) := hInt_le
      _ = M * (∫ θ in (-Real.pi)..Real.pi,
              ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) := by
            rw [intervalIntegral.integral_const_mul]
  have hpow4 : r⁻¹ ^ n ≤ 4 := by
    dsimp [r]
    exact one_sub_inv_pow_nat_le_four hn
  have hkernel_bound :
      (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) ≤
        C * (n : ℝ) ^ (β - 1) := by
    dsimp [r]
    have h := hC n hn1
    simpa [Complex.real_smul] using h
  have htarget_nonneg : 0 ≤ (n : ℝ) ^ (β - 1) := by positivity
  have hcoeff_bound :
      ‖p.coeff n‖ ≤ K * ((n : ℝ) ^ (β - 1)) := by
    calc
      ‖p.coeff n‖
          ≤ (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
              ∫ θ in (-Real.pi)..Real.pi,
                ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := hcauchy
      _ ≤ (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
              (M * (∫ θ in (-Real.pi)..Real.pi,
                ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β))) := by
            exact mul_le_mul_of_nonneg_left hInt_bound
              (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.mpr hr0) n))
      _ ≤ (2 * Real.pi)⁻¹ * 4 *
              (M * (∫ θ in (-Real.pi)..Real.pi,
                ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β))) := by
            calc
              (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
                    (M * (∫ θ in (-Real.pi)..Real.pi,
                      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)))
                  = (2 * Real.pi)⁻¹ *
                    (r⁻¹ ^ n * (M * (∫ θ in (-Real.pi)..Real.pi,
                      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)))) := by
                    ring
              _ ≤ (2 * Real.pi)⁻¹ *
                    (4 * (M * (∫ θ in (-Real.pi)..Real.pi,
                      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)))) := by
                    exact mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right hpow4 hMkernel_nonneg)
                      (by positivity)
              _ = (2 * Real.pi)⁻¹ * 4 *
                    (M * (∫ θ in (-Real.pi)..Real.pi,
                      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β))) := by
                    ring
      _ ≤ (2 * Real.pi)⁻¹ * 4 * (M * (C * (n : ℝ) ^ (β - 1))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hkernel_bound hM0)
              (mul_nonneg (by positivity) (by norm_num))
      _ = K * ((n : ℝ) ^ (β - 1)) := by
            dsimp [K]
            ring
  simpa [Real.norm_of_nonneg htarget_nonneg] using hcoeff_bound
