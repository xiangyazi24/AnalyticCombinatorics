import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrderAlphaLt1
import AnalyticCombinatorics.Ch7.SingularityApp.TwoRegularClass

/-!
# Second-order asymptotics for 2-regular labelled graphs

This file applies the `0 < α < 1` second-order transfer theorem to

`exp (-z/2 - z^2/4) * (1 - z)^(-1/2)`.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

/-- The second-order constant for 2-regular labelled graph counts. -/
def twoRegularSecondConstant : ℝ :=
  -(5 / 8 : ℝ) * twoRegularAsymptoticConstant

lemma hasDerivAt_twoRegularPrefactor_one :
    HasDerivAt twoRegularPrefactor (-twoRegularSingularCoeff) (1 : ℂ) := by
  have hid : HasDerivAt (fun z : ℂ => z) 1 (1 : ℂ) := by
    simpa using hasDerivAt_id (1 : ℂ)
  have hquad : HasDerivAt (fun z : ℂ => z ^ 2) (2 : ℂ) (1 : ℂ) := by
    simpa using hid.pow 2
  have harg : HasDerivAt (fun z : ℂ => -(z / 2) - z ^ 2 / 4) (-1 : ℂ)
      (1 : ℂ) := by
    have h1 := (hid.div_const (2 : ℂ)).neg
    have h2 := hquad.div_const (4 : ℂ)
    convert h1.sub h2 using 1
    ring
  convert harg.cexp using 1
  norm_num [twoRegularPrefactor, twoRegularSingularCoeff]

lemma tendsto_twoRegularPrefactor_twoTerm :
    Tendsto
      (fun z : ℂ => ‖twoRegularPrefactor z - twoRegularSingularCoeff -
          twoRegularSingularCoeff * (1 - z)‖ *
        ‖(1 : ℂ) - z‖ ^ (-(1 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  have ho := hasDerivAt_twoRegularPrefactor_one.isLittleO
  have hnorm : (fun z : ℂ => ‖twoRegularPrefactor z - twoRegularSingularCoeff -
          twoRegularSingularCoeff * (1 - z)‖) =o[𝓝 (1 : ℂ)]
      (fun z : ℂ => ‖(1 : ℂ) - z‖) := by
    have hnorm0 := ho.norm_left.norm_right
    refine hnorm0.congr' ?_ ?_
    · exact Eventually.of_forall fun z => by
        simp [twoRegularPrefactor, twoRegularSingularCoeff, smul_eq_mul]
        ring_nf
    · exact Eventually.of_forall fun z => by
        simp [norm_sub_rev]
  have hquot_nhds : Tendsto
      (fun z : ℂ => ‖twoRegularPrefactor z - twoRegularSingularCoeff -
          twoRegularSingularCoeff * (1 - z)‖ / ‖(1 : ℂ) - z‖)
      (𝓝 (1 : ℂ)) (𝓝 0) := by
    refine (isLittleO_iff_tendsto' ?_).mp hnorm
    filter_upwards with z hzero
    have hz1 : z = 1 := by
      rw [norm_eq_zero, sub_eq_zero] at hzero
      exact hzero.symm
    subst z
    norm_num [twoRegularPrefactor, twoRegularSingularCoeff]
  have hquot_within : Tendsto
      (fun z : ℂ => ‖twoRegularPrefactor z - twoRegularSingularCoeff -
          twoRegularSingularCoeff * (1 - z)‖ / ‖(1 : ℂ) - z‖)
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) :=
    hquot_nhds.mono_left nhdsWithin_le_nhds
  refine hquot_within.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have hnorm_ne : ‖(1 : ℂ) - z‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    simpa [sub_eq_zero] using (Ne.symm hz_ne)
  rw [Real.rpow_neg (norm_nonneg ((1 : ℂ) - z)), Real.rpow_one]
  field_simp [hnorm_ne]

lemma twoRegular_singularity_twoTerm_norm_eq {z : ℂ} (hz : z ≠ 1) :
    ‖twoRegularEGFFun z - twoRegularSingularCoeff * (1 - z) ^ (-(1 / 2 : ℂ)) -
        twoRegularSingularCoeff * (1 - z) ^ (1 / 2 : ℂ)‖ *
        ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)) =
      ‖twoRegularPrefactor z - twoRegularSingularCoeff -
          twoRegularSingularCoeff * (1 - z)‖ *
        ‖(1 : ℂ) - z‖ ^ (-(1 : ℝ)) := by
  let u : ℂ := 1 - z
  have hu_ne : u ≠ 0 := by
    dsimp [u]
    simpa [sub_eq_zero] using (Ne.symm hz)
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hpow_half : u * u ^ (-(1 / 2 : ℂ)) = u ^ (1 / 2 : ℂ) := by
    calc
      u * u ^ (-(1 / 2 : ℂ)) =
          u ^ (1 : ℂ) * u ^ (-(1 / 2 : ℂ)) := by rw [Complex.cpow_one]
      _ = u ^ ((1 : ℂ) + (-(1 / 2 : ℂ))) := by
          rw [← Complex.cpow_add _ _ hu_ne]
      _ = u ^ (1 / 2 : ℂ) := by norm_num
  have hpow_norm : ‖u ^ (-(1 / 2 : ℂ))‖ = ‖u‖ ^ (-(1 / 2 : ℝ)) := by
    convert Complex.norm_cpow_real u (-(1 / 2 : ℝ)) using 1
    norm_num
  unfold twoRegularEGFFun
  change ‖twoRegularPrefactor z * u ^ (-(1 / 2 : ℂ)) -
        twoRegularSingularCoeff * u ^ (-(1 / 2 : ℂ)) -
        twoRegularSingularCoeff * u ^ (1 / 2 : ℂ)‖ *
        ‖u‖ ^ (-(1 / 2 : ℝ)) =
      ‖twoRegularPrefactor z - twoRegularSingularCoeff - twoRegularSingularCoeff * u‖ *
        ‖u‖ ^ (-(1 : ℝ))
  rw [← hpow_half]
  rw [show twoRegularPrefactor z * u ^ (-(1 / 2 : ℂ)) -
        twoRegularSingularCoeff * u ^ (-(1 / 2 : ℂ)) -
        twoRegularSingularCoeff * (u * u ^ (-(1 / 2 : ℂ))) =
      (twoRegularPrefactor z - twoRegularSingularCoeff - twoRegularSingularCoeff * u) *
        u ^ (-(1 / 2 : ℂ)) by ring]
  rw [norm_mul, hpow_norm]
  have hmul : ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) =
      ‖u‖ ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hu_norm_pos]
    norm_num
  rw [mul_assoc, hmul]

lemma tendsto_twoRegular_singularity_twoTerm :
    Tendsto
      (fun z : ℂ =>
        ‖twoRegularEGFFun z -
            twoRegularSingularCoeff * (1 - z) ^ (-(1 / 2 : ℂ)) -
            twoRegularSingularCoeff * (1 - z) ^ (1 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  refine tendsto_twoRegularPrefactor_twoTerm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (twoRegular_singularity_twoTerm_norm_eq hz.2.1).symm

lemma twoRegular_transfer_complex_secondOrder :
    (fun n : ℕ =>
      twoRegularEGFSeriesℂ.coeff n -
        (twoRegularSingularCoeff *
            ((((n : ℝ) ^ ((1 / 2 : ℝ) - 1) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) +
              ((((1 / 2 : ℝ) * ((1 / 2 : ℝ) - 1) / 2 /
                    Real.Gamma (1 / 2 : ℝ)) *
                  (n : ℝ) ^ ((1 / 2 : ℝ) - 2) : ℝ) : ℂ)) +
          twoRegularSingularCoeff *
            (((n : ℝ) ^ ((1 / 2 : ℝ) - 2) /
              Real.Gamma ((1 / 2 : ℝ) - 1) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - 2)) := by
  refine transfer_twoTerm_secondOrder_alpha_lt_one
    (α := (1 / 2 : ℝ)) (C0 := twoRegularSingularCoeff)
    (C1 := twoRegularSingularCoeff) (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (f := twoRegularEGFFun) (p := twoRegularEGFSeriesℂ)
    (by norm_num) (by norm_num) (by norm_num) (by positivity) ?_
    twoRegularEGFFun_hasFPowerSeriesAt_zero ?_ ?_
  · nlinarith [Real.pi_pos]
  · exact analyticOnNhd_twoRegularEGFFun (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
      (by positivity) (by nlinarith [Real.pi_pos])
  · convert tendsto_twoRegular_singularity_twoTerm using 1
    ext z
    norm_num

lemma twoRegular_Gamma_neg_half :
    Real.Gamma (-(1 / 2 : ℝ)) = -2 * Real.sqrt Real.pi := by
  have h := Real.Gamma_add_one (s := (-(1 / 2 : ℝ)))
    (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [Real.Gamma_one_half_eq] at h
  linarith

lemma twoRegular_secondOrder_model_complex_eq (n : ℕ) :
        (twoRegularSingularCoeff *
            ((((n : ℝ) ^ ((1 / 2 : ℝ) - 1) / Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) +
              ((((1 / 2 : ℝ) * ((1 / 2 : ℝ) - 1) / 2 /
                    Real.Gamma (1 / 2 : ℝ)) *
                  (n : ℝ) ^ ((1 / 2 : ℝ) - 2) : ℝ) : ℂ)) +
          twoRegularSingularCoeff *
            (((n : ℝ) ^ ((1 / 2 : ℝ) - 2) /
              Real.Gamma ((1 / 2 : ℝ) - 1) : ℝ) : ℂ)) =
    ((twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
      twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hpow1 : (n : ℝ) ^ ((1 / 2 : ℝ) - 1) =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    congr 1
    norm_num
  have hpow2 : (n : ℝ) ^ ((1 / 2 : ℝ) - 2) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    congr 1
    norm_num
  rw [hpow1, hpow2]
  unfold twoRegularSecondConstant twoRegularAsymptoticConstant twoRegularSingularCoeff
  rw [Real.Gamma_one_half_eq, show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num,
    twoRegular_Gamma_neg_half]
  norm_num [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add]
  ring

private lemma complex_re_isLittleO_ofReal {f : ℕ → ℂ} {g r : ℕ → ℝ}
    (h : (fun n : ℕ => f n - ((g n : ℝ) : ℂ)) =o[atTop] r) :
    (fun n : ℕ => (f n).re - g n) =o[atTop] r := by
  rw [Asymptotics.isLittleO_iff] at h ⊢
  intro c hc
  have hc_bound := h hc
  filter_upwards [hc_bound] with n hn
  calc
    ‖(f n).re - g n‖ = ‖(f n - (g n : ℂ)).re‖ := by
      simp [Complex.sub_re]
    _ ≤ ‖f n - (g n : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ c * ‖r n‖ := hn

theorem twoRegularEGFCoeff_secondOrder :
    (fun n : ℕ =>
      twoRegularEGFCoeff n -
        (twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hcomplex :
      (fun n : ℕ =>
        twoRegularEGFSeriesℂ.coeff n -
          ((twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
            twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - 2)) := by
    refine twoRegular_transfer_complex_secondOrder.congr_left ?_
    intro n
    rw [twoRegular_secondOrder_model_complex_eq n]
  have hreal := complex_re_isLittleO_ofReal hcomplex
  convert hreal using 1
  ext n
  congr 1
  norm_num

theorem twoRegularGraphCount_div_factorial_secondOrder :
    (fun n : ℕ =>
      twoRegularGraphCount n / (n.factorial : ℝ) -
        (twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  refine twoRegularEGFCoeff_secondOrder.congr_left ?_
  intro n
  rw [twoRegularGraphCount_div_factorial]

namespace TwoRegularClass

theorem twoRegularClass_counts_div_factorial_secondOrder :
    (fun n : ℕ =>
      (twoRegularClass.counts n : ℝ) / (n.factorial : ℝ) -
        (twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  refine twoRegularGraphCount_div_factorial_secondOrder.congr_left ?_
  intro n
  rw [twoRegularClass_counts_eq_twoRegularGraphCount n]

end TwoRegularClass

end
