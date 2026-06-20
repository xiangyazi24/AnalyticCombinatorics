import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrderGeneral
import AnalyticCombinatorics.Ch4.Analytic.ModelCoeffThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.TwoRegularSecondOrder

/-!
# Third-order asymptotics for 2-regular labelled graphs

This file proves the three-term singularity-analysis expansion for

`exp (-z/2 - z^2/4) * (1 - z)^(-1/2)`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

/-- The third-order constant for 2-regular labelled graph counts. -/
def twoRegularThirdConstant : ℝ :=
  (1 / 128 : ℝ) * twoRegularAsymptoticConstant

private def twoRegularInvSqrtSeriesℂ : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n : ℕ => Ring.choose ((1 / 2 : ℂ) + n - 1) n)

private def twoRegularInvSqrtThirdModel (n : ℕ) : ℝ :=
  ((n : ℝ) ^ (-(1 / 2 : ℝ)) / Real.Gamma (1 / 2 : ℝ)) +
    (((-(1 / 8 : ℝ)) / Real.Gamma (1 / 2 : ℝ)) *
      (n : ℝ) ^ (-(3 / 2 : ℝ))) +
      (((1 / 128 : ℝ) / Real.Gamma (1 / 2 : ℝ)) *
        (n : ℝ) ^ (-(5 / 2 : ℝ)))

private def twoRegularRemainderThirdModel (n : ℕ) : ℂ :=
  twoRegularSingularCoeff *
      (((n : ℝ) ^ (-(3 / 2 : ℝ)) /
        Real.Gamma (-(1 / 2 : ℝ)) : ℝ) : ℂ) +
    twoRegularSingularCoeff *
      (((((3 / 8 : ℝ) / Real.Gamma (-(1 / 2 : ℝ))) *
        (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) +
    (twoRegularSingularCoeff / 4) *
      (((n : ℝ) ^ (-(5 / 2 : ℝ)) /
        Real.Gamma ((-(1 / 2 : ℝ)) - 1) : ℝ) : ℂ)

private lemma rpow_sub_one_isLittleO (a : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ (a - 1)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) := by
  refine IsLittleO.of_bound ?_
  intro c hc
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ < c :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (Iio_mem_nhds hc)
  filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hninvc
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpowpos : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hnpos a
  have hleft_nonneg : 0 ≤ (n : ℝ) ^ (a - 1) := Real.rpow_nonneg (le_of_lt hnpos) _
  have hright_nonneg : 0 ≤ (n : ℝ) ^ a := le_of_lt hpowpos
  have hpow_eq : (n : ℝ) ^ (a - 1) = (n : ℝ) ^ a * (n : ℝ)⁻¹ := by
    calc
      (n : ℝ) ^ (a - 1) = (n : ℝ) ^ (a + (-(1 : ℝ))) := by ring_nf
      _ = (n : ℝ) ^ a * (n : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_add hnpos]
      _ = (n : ℝ) ^ a * (n : ℝ)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  calc
    ‖(n : ℝ) ^ (a - 1)‖ = (n : ℝ) ^ (a - 1) := Real.norm_of_nonneg hleft_nonneg
    _ = (n : ℝ) ^ a * (n : ℝ)⁻¹ := hpow_eq
    _ ≤ (n : ℝ) ^ a * c :=
      mul_le_mul_of_nonneg_left (le_of_lt hninvc) (le_of_lt hpowpos)
    _ = c * ‖(n : ℝ) ^ a‖ := by
      rw [Real.norm_of_nonneg hright_nonneg]
      ring

private lemma ofReal_isLittleO {u v : ℕ → ℝ}
    (h : u =o[atTop] v) :
    (fun n : ℕ => ((u n : ℝ) : ℂ)) =o[atTop] v := by
  exact Asymptotics.IsLittleO.of_norm_left (by
    simpa [Complex.norm_real] using h.norm_left)

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

private lemma coeff_sub_const_smul (C : ℂ)
  (p q : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
  change (p n) 1 - ((C • q) n) 1 = (p n) 1 - C * (q n) 1
  simp only [FormalMultilinearSeries.smul_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]

private lemma twoRegular_not_pole_neg_half :
    ∀ m : ℕ, (-(1 / 2 : ℝ)) ≠ 1 - (m : ℝ) := by
  intro m hm
  have h2m : (2 * (m : ℝ) : ℝ) = 3 := by nlinarith
  have hnat : 2 * m = 3 := by exact_mod_cast h2m
  omega

lemma twoRegular_Gamma_neg_three_halves :
    Real.Gamma (-(3 / 2 : ℝ)) = 4 * Real.sqrt Real.pi / 3 := by
  have h := Real.Gamma_add_one (s := (-(3 / 2 : ℝ)))
    (by norm_num : (-(3 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [twoRegular_Gamma_neg_half] at h
  nlinarith

lemma twoRegularInvSqrt_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => (1 - z) ^ (-(1 / 2 : ℂ)))
      twoRegularInvSqrtSeriesℂ (0 : ℂ) := by
  have hraw :=
    (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero
      ((1 / 2 : ℂ))).hasFPowerSeriesAt
  unfold twoRegularInvSqrtSeriesℂ
  convert hraw using 1
  ext z
  rw [Complex.cpow_neg, inv_eq_one_div]

lemma analyticOnNhd_twoRegularInvSqrt {R φ : ℝ} (hφ0 : 0 < φ) (hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-(1 / 2 : ℂ)))
      (DeltaDomainArg R φ) := by
  simpa using
    (analyticOnNhd_one_sub_cpow_deltaDomain
      (α := (1 / 2 : ℂ)) (R := R) (φ := φ) hφ0 hφπ)

lemma twoRegularPrefactor_exp_local (z : ℂ) :
    twoRegularPrefactor z =
      twoRegularSingularCoeff *
        Complex.exp ((1 - z) - (1 - z) ^ 2 / 4) := by
  unfold twoRegularPrefactor twoRegularSingularCoeff
  rw [← Complex.exp_add]
  congr 1
  ring

private lemma complex_exp_sub_quadratic_isLittleO :
    (fun x : ℂ => Complex.exp x - (1 + x + x ^ 2 / 2))
      =o[𝓝 (0 : ℂ)] (fun x : ℂ => ‖x‖ ^ 2) := by
  have h := Complex.exp_sub_sum_range_succ_isLittleO_pow 2
  have hnorm := h.norm_left.norm_right
  refine Asymptotics.IsLittleO.of_norm_left ?_
  refine hnorm.congr' ?_ ?_
  · filter_upwards with x
    congr 1
    simp [Finset.sum_range_succ]
  · filter_upwards with x
    rw [norm_pow]

private lemma twoRegularPrefactor_threeTerm_isLittleO :
    (fun z : ℂ =>
      twoRegularPrefactor z - twoRegularSingularCoeff -
        twoRegularSingularCoeff * (1 - z) -
          (twoRegularSingularCoeff / 4) * (1 - z) ^ 2)
      =o[𝓝 (1 : ℂ)] (fun z : ℂ => ‖(1 : ℂ) - z‖ ^ 2) := by
  let u : ℂ → ℂ := fun z => 1 - z
  let x : ℂ → ℂ := fun z => u z - u z ^ 2 / 4
  have hx0 : Tendsto x (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hu0 : Tendsto u (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa [u] using (tendsto_const_nhds.sub tendsto_id : Tendsto
        (fun z : ℂ => (1 : ℂ) - z) (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)))
    simpa [x] using hu0.sub ((hu0.pow 2).div_const 4)
  have hexp :=
    complex_exp_sub_quadratic_isLittleO.comp_tendsto hx0
  have hxO : (fun z : ℂ => ‖x z‖ ^ 2) =O[𝓝 (1 : ℂ)]
      (fun z : ℂ => ‖u z‖ ^ 2) := by
    have hfactor : Tendsto (fun z : ℂ => 1 - u z / 4) (𝓝 (1 : ℂ)) (𝓝 (1 : ℂ)) := by
      have hu0 : Tendsto u (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
        simpa [u] using (tendsto_const_nhds.sub tendsto_id : Tendsto
          (fun z : ℂ => (1 : ℂ) - z) (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)))
      simpa using (tendsto_const_nhds.sub (hu0.div_const 4))
    have hbound : (fun z : ℂ => 1 - u z / 4) =O[𝓝 (1 : ℂ)]
        (fun _ : ℂ => (1 : ℝ)) :=
      hfactor.isBigO_one ℝ
    have hbound_norm := hbound.norm_left
    refine IsBigO.of_bound 4 ?_
    have hsmall : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), ‖1 - u z / 4‖ ≤ 2 := by
      have hlt : ‖(1 : ℂ)‖ < (2 : ℝ) := by norm_num
      exact (hfactor.norm.eventually (Iio_mem_nhds hlt)).mono fun z hz => le_of_lt hz
    filter_upwards [hsmall] with z hz
    have hnonneg : 0 ≤ ‖u z‖ ^ 2 := by positivity
    have hx_eq : x z = u z * (1 - u z / 4) := by
      dsimp [x, u]
      ring
    calc
      ‖‖x z‖ ^ 2‖ = ‖x z‖ ^ 2 := by
        rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖x z‖ ^ 2)]
      _ = (‖u z‖ * ‖1 - u z / 4‖) ^ 2 := by
        rw [hx_eq, norm_mul]
      _ ≤ (‖u z‖ * 2) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hz (norm_nonneg _)) 2
      _ = 4 * ‖‖u z‖ ^ 2‖ := by
        rw [Real.norm_of_nonneg hnonneg]
        ring
  have hmain : (fun z : ℂ =>
        Complex.exp (x z) - (1 + x z + x z ^ 2 / 2))
      =o[𝓝 (1 : ℂ)] (fun z : ℂ => ‖u z‖ ^ 2) :=
    hexp.trans_isBigO hxO
  have htail : (fun z : ℂ => -u z ^ 3 / 4 + u z ^ 4 / 32)
      =o[𝓝 (1 : ℂ)] (fun z : ℂ => ‖u z‖ ^ 2) := by
    have hu0 : Tendsto u (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa [u] using (tendsto_const_nhds.sub tendsto_id : Tendsto
        (fun z : ℂ => (1 : ℂ) - z) (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)))
    have hcubic : (fun w : ℂ => -w ^ 3 / 4 + w ^ 4 / 32)
        =o[𝓝 (0 : ℂ)] (fun w : ℂ => ‖w‖ ^ 2) := by
      have hsmall : (fun w : ℂ => w) =o[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) :=
        Asymptotics.IsLittleO.of_norm_left
          ((isLittleO_one_iff ℝ).2 (tendsto_norm_zero : Tendsto
            (fun w : ℂ => ‖w‖) (𝓝 0) (𝓝 0)))
      have hbase : (fun w : ℂ => w ^ 2) =O[𝓝 (0 : ℂ)] (fun w : ℂ => ‖w‖ ^ 2) := by
        refine IsBigO.of_bound 1 ?_
        filter_upwards with w
        rw [norm_pow, Real.norm_of_nonneg (by positivity : 0 ≤ ‖w‖ ^ 2)]
        simp
      have hw3 : (fun w : ℂ => w ^ 3) =o[𝓝 (0 : ℂ)] (fun w : ℂ => ‖w‖ ^ 2) := by
        have h := hbase.mul_isLittleO hsmall
        refine h.congr' ?_ ?_
        · filter_upwards with w
          ring
        · filter_upwards with w
          ring
      have hw4 : (fun w : ℂ => w ^ 4) =o[𝓝 (0 : ℂ)] (fun w : ℂ => ‖w‖ ^ 2) := by
        have hsmall2 : (fun w : ℂ => w ^ 2) =o[𝓝 (0 : ℂ)] (fun _ : ℂ => (1 : ℝ)) := by
          have hnormsq : (fun w : ℂ => ‖w‖ ^ 2) =o[𝓝 (0 : ℂ)]
              (fun _ : ℂ => (1 : ℝ)) := by
            refine (isLittleO_one_iff ℝ).2 ?_
            simpa using ((tendsto_norm_zero : Tendsto (fun w : ℂ => ‖w‖)
              (𝓝 0) (𝓝 0)).pow 2)
          exact hbase.trans_isLittleO hnormsq
        have h := hbase.mul_isLittleO hsmall2
        refine h.congr' ?_ ?_
        · filter_upwards with w
          ring
        · filter_upwards with w
          ring
      exact (hw3.const_mul_left (-(1 / 4 : ℂ))).add
        (hw4.const_mul_left (1 / 32 : ℂ)) |>.congr_left (fun w => by ring)
    simpa [u] using hcubic.comp_tendsto hu0
  have hsum := hmain.add htail
  have hscaled := hsum.const_mul_left twoRegularSingularCoeff
  refine hscaled.congr_left ?_
  intro z
  rw [twoRegularPrefactor_exp_local]
  dsimp [x, u]
  ring

lemma tendsto_twoRegularPrefactor_threeTerm :
    Tendsto
      (fun z : ℂ =>
        ‖twoRegularPrefactor z - twoRegularSingularCoeff -
            twoRegularSingularCoeff * (1 - z) -
              (twoRegularSingularCoeff / 4) * (1 - z) ^ 2‖ *
          ‖(1 : ℂ) - z‖ ^ (-(2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  have hnorm := twoRegularPrefactor_threeTerm_isLittleO.norm_left
  have hquot_nhds : Tendsto
      (fun z : ℂ =>
        ‖twoRegularPrefactor z - twoRegularSingularCoeff -
            twoRegularSingularCoeff * (1 - z) -
              (twoRegularSingularCoeff / 4) * (1 - z) ^ 2‖ /
          ‖(1 : ℂ) - z‖ ^ 2)
      (𝓝 (1 : ℂ)) (𝓝 0) := by
    refine (isLittleO_iff_tendsto' ?_).mp hnorm
    filter_upwards with z hz
    have hz1 : z = 1 := by
      rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at hz
      exact hz.symm
    subst z
    norm_num [twoRegularPrefactor, twoRegularSingularCoeff]
  have hwithin : Tendsto
      (fun z : ℂ =>
        ‖twoRegularPrefactor z - twoRegularSingularCoeff -
            twoRegularSingularCoeff * (1 - z) -
              (twoRegularSingularCoeff / 4) * (1 - z) ^ 2‖ /
          ‖(1 : ℂ) - z‖ ^ 2)
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) :=
    hquot_nhds.mono_left nhdsWithin_le_nhds
  refine hwithin.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := hz.2.1
  have hnorm_ne : ‖(1 : ℂ) - z‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    simpa [sub_eq_zero] using (Ne.symm hz_ne)
  rw [Real.rpow_neg (norm_nonneg ((1 : ℂ) - z))]
  rw [div_eq_mul_inv]
  rw [Real.rpow_two]

lemma twoRegular_remainder_singularity_norm_eq {z : ℂ} (hz : z ≠ 1) :
    ‖(twoRegularEGFFun z -
          twoRegularSingularCoeff * (1 - z) ^ (-(1 / 2 : ℂ))) -
        twoRegularSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
          (twoRegularSingularCoeff / 4) * (1 - z) ^ (3 / 2 : ℂ)‖ *
        ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)) =
      ‖twoRegularPrefactor z - twoRegularSingularCoeff -
          twoRegularSingularCoeff * (1 - z) -
            (twoRegularSingularCoeff / 4) * (1 - z) ^ 2‖ *
        ‖(1 : ℂ) - z‖ ^ (-(2 : ℝ)) := by
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
  have hpow_three_half : u ^ 2 * u ^ (-(1 / 2 : ℂ)) = u ^ (3 / 2 : ℂ) := by
    have hnat : u ^ 2 = u ^ (2 : ℂ) := (Complex.cpow_natCast u 2).symm
    calc
      u ^ 2 * u ^ (-(1 / 2 : ℂ)) =
          u ^ (2 : ℂ) * u ^ (-(1 / 2 : ℂ)) := by rw [hnat]
      _ = u ^ ((2 : ℂ) + (-(1 / 2 : ℂ))) := by
          rw [← Complex.cpow_add _ _ hu_ne]
      _ = u ^ (3 / 2 : ℂ) := by norm_num
  have hpow_norm : ‖u ^ (-(1 / 2 : ℂ))‖ = ‖u‖ ^ (-(1 / 2 : ℝ)) := by
    convert Complex.norm_cpow_real u (-(1 / 2 : ℝ)) using 1
    norm_num
  unfold twoRegularEGFFun
  change ‖(twoRegularPrefactor z * u ^ (-(1 / 2 : ℂ)) -
          twoRegularSingularCoeff * u ^ (-(1 / 2 : ℂ))) -
        twoRegularSingularCoeff * u ^ (1 / 2 : ℂ) -
          (twoRegularSingularCoeff / 4) * u ^ (3 / 2 : ℂ)‖ *
        ‖u‖ ^ (-(3 / 2 : ℝ)) =
      ‖twoRegularPrefactor z - twoRegularSingularCoeff -
          twoRegularSingularCoeff * u -
            (twoRegularSingularCoeff / 4) * u ^ 2‖ *
        ‖u‖ ^ (-(2 : ℝ))
  rw [← hpow_half, ← hpow_three_half]
  rw [show (twoRegularPrefactor z * u ^ (-(1 / 2 : ℂ)) -
          twoRegularSingularCoeff * u ^ (-(1 / 2 : ℂ))) -
        twoRegularSingularCoeff * (u * u ^ (-(1 / 2 : ℂ))) -
          (twoRegularSingularCoeff / 4) * (u ^ 2 * u ^ (-(1 / 2 : ℂ))) =
      (twoRegularPrefactor z - twoRegularSingularCoeff -
          twoRegularSingularCoeff * u -
            (twoRegularSingularCoeff / 4) * u ^ 2) *
        u ^ (-(1 / 2 : ℂ)) by ring]
  rw [norm_mul, hpow_norm]
  have hmul : ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 2 : ℝ)) =
      ‖u‖ ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hu_norm_pos]
    norm_num
  rw [mul_assoc, hmul]

lemma tendsto_twoRegular_remainder_singularity :
    Tendsto
      (fun z : ℂ =>
        ‖(twoRegularEGFFun z -
              twoRegularSingularCoeff * (1 - z) ^ (-(1 / 2 : ℂ))) -
            twoRegularSingularCoeff * (1 - z) ^ (1 / 2 : ℂ) -
              (twoRegularSingularCoeff / 4) * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  refine tendsto_twoRegularPrefactor_threeTerm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (twoRegular_remainder_singularity_norm_eq hz.2.1).symm

lemma twoRegular_remainder_transfer_complex_thirdOrder :
    (fun n : ℕ =>
      (twoRegularEGFSeriesℂ - twoRegularSingularCoeff • twoRegularInvSqrtSeriesℂ).coeff n -
        twoRegularRemainderThirdModel n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  let f : ℂ → ℂ := fun z =>
    twoRegularEGFFun z -
      twoRegularSingularCoeff * (1 - z) ^ (-(1 / 2 : ℂ))
  have hp : HasFPowerSeriesAt f
      (twoRegularEGFSeriesℂ - twoRegularSingularCoeff • twoRegularInvSqrtSeriesℂ)
      (0 : ℂ) := by
    have hsub := twoRegularEGFFun_hasFPowerSeriesAt_zero.sub
      (twoRegularInvSqrt_hasFPowerSeriesAt_zero.const_smul (c := twoRegularSingularCoeff))
    simpa [f, smul_eq_mul] using hsub
  have hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    have hφπ : Real.pi / 4 < Real.pi := by nlinarith [Real.pi_pos]
    simpa [f] using
      (analyticOnNhd_twoRegularEGFFun (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
        (by positivity) hφπ).sub
        ((analyticOnNhd_twoRegularInvSqrt (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
          (by positivity) hφπ).const_smul (c := twoRegularSingularCoeff))
  have htransfer := transfer_twoTerm_secondOrder_general
    (α := (-(1 / 2 : ℝ))) (C0 := twoRegularSingularCoeff)
    (C1 := twoRegularSingularCoeff / 4)
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (f := f)
    (p := twoRegularEGFSeriesℂ - twoRegularSingularCoeff • twoRegularInvSqrtSeriesℂ)
    twoRegular_not_pole_neg_half (by norm_num) (by positivity)
    (by nlinarith [Real.pi_pos]) hp hΔ ?_
  · refine htransfer.congr' ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      unfold twoRegularRemainderThirdModel
      norm_num
      ring
    · refine Eventually.of_forall fun n => ?_
      norm_num
  · convert tendsto_twoRegular_remainder_singularity using 1
    ext z
    norm_num [f]

lemma twoRegular_invSqrt_model_thirdOrder :
    (fun n : ℕ =>
      twoRegularSingularCoeff * twoRegularInvSqrtSeriesℂ.coeff n -
        twoRegularSingularCoeff * ((twoRegularInvSqrtThirdModel n : ℝ) : ℂ))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hmodelO := modelCoeff_thirdOrder (α := (1 / 2 : ℝ)) (by norm_num)
  have htail : (fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - 4))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
    convert rpow_sub_one_isLittleO (-(5 / 2 : ℝ)) using 1
    ext n
    congr 1
    norm_num
  have hmodel := hmodelO.trans_isLittleO htail
  have hcomplex := (ofReal_isLittleO hmodel).const_mul_left twoRegularSingularCoeff
  refine hcomplex.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hpow0 : (n : ℝ) ^ ((1 / 2 : ℝ) - 1) =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    congr 1
    norm_num
  have hpow1 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹ =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hinv : (n : ℝ)⁻¹ = (n : ℝ) ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg hnpos.le, Real.rpow_one]
    calc
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹ =
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ)) := by rw [hinv]
      _ = (n : ℝ) ^ (-(1 / 2 : ℝ) + -(1 : ℝ)) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (-(3 / 2 : ℝ)) := by ring_nf
  have hpow2 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ)⁻¹) ^ 2 =
      (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
    have hinv2 : ((n : ℝ)⁻¹) ^ 2 = (n : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hnpos.le]
      norm_num
    calc
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ)⁻¹) ^ 2 =
          (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(2 : ℝ)) := by rw [hinv2]
      _ = (n : ℝ) ^ (-(1 / 2 : ℝ) + -(2 : ℝ)) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (-(5 / 2 : ℝ)) := by ring_nf
  have hpow1' : (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ)⁻¹ =
      (n : ℝ) ^ (-3 / 2 : ℝ) := by
    convert hpow1 using 2 <;> norm_num
  have hpow2' : (n : ℝ) ^ (-1 / 2 : ℝ) * ((n : ℝ)⁻¹) ^ 2 =
      (n : ℝ) ^ (-5 / 2 : ℝ) := by
    convert hpow2 using 2 <;> norm_num
  have hraw :
      ((n : ℝ) ^ ((1 / 2 : ℝ) - 1) / Real.Gamma (1 / 2 : ℝ)) *
          (1 + ((1 / 2 : ℝ) * ((1 / 2 : ℝ) - 1) / 2) * (n : ℝ)⁻¹ +
            ((1 / 2 : ℝ) * ((1 / 2 : ℝ) - 1) * ((1 / 2 : ℝ) - 2) *
                (3 * (1 / 2 : ℝ) - 1) / 24) * ((n : ℝ)⁻¹) ^ 2) =
        twoRegularInvSqrtThirdModel n := by
    unfold twoRegularInvSqrtThirdModel
    rw [hpow0]
    norm_num
    ring_nf
    rw [
      show (n : ℝ) ^ (-1 / 2 : ℝ) * (Real.Gamma (1 / 2 : ℝ))⁻¹ * (n : ℝ)⁻¹ =
          (Real.Gamma (1 / 2 : ℝ))⁻¹ * (n : ℝ) ^ (-3 / 2 : ℝ) by
        rw [← hpow1']
        ring,
      show (n : ℝ) ^ (-1 / 2 : ℝ) * (Real.Gamma (1 / 2 : ℝ))⁻¹ *
            ((n : ℝ)⁻¹) ^ 2 =
          (Real.Gamma (1 / 2 : ℝ))⁻¹ * (n : ℝ) ^ (-5 / 2 : ℝ) by
        rw [← hpow2']
        ring]
  unfold twoRegularInvSqrtSeriesℂ
  rw [FormalMultilinearSeries.coeff_ofScalars]
  have hchoose :
      Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n =
        ((Ring.choose ((1 / 2 : ℝ) + (n : ℕ) - 1) n : ℝ) : ℂ) := by
    simpa using choose_ofReal_model (1 / 2 : ℝ) n
  rw [hchoose]
  rw [hraw]
  rw [Complex.ofReal_sub]
  ring

lemma twoRegular_thirdOrder_model_complex_eq (n : ℕ) :
    twoRegularSingularCoeff * ((twoRegularInvSqrtThirdModel n : ℝ) : ℂ) +
        twoRegularRemainderThirdModel n =
      ((twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            twoRegularThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) := by
  unfold twoRegularInvSqrtThirdModel twoRegularRemainderThirdModel
    twoRegularThirdConstant twoRegularSecondConstant twoRegularAsymptoticConstant
    twoRegularSingularCoeff
  rw [Real.Gamma_one_half_eq, twoRegular_Gamma_neg_half,
    show (-(1 / 2 : ℝ)) - 1 = -(3 / 2 : ℝ) by norm_num,
    twoRegular_Gamma_neg_three_halves]
  norm_num [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_sub]
  ring

lemma twoRegular_transfer_complex_thirdOrder :
    (fun n : ℕ =>
      twoRegularEGFSeriesℂ.coeff n -
        ((twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            twoRegularThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hsum := twoRegular_invSqrt_model_thirdOrder.add
    twoRegular_remainder_transfer_complex_thirdOrder
  refine hsum.congr_left ?_
  intro n
  rw [coeff_sub_const_smul]
  rw [← twoRegular_thirdOrder_model_complex_eq n]
  ring

theorem twoRegularEGFCoeff_thirdOrder :
    (fun n : ℕ =>
      twoRegularEGFCoeff n -
        (twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            twoRegularThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  exact complex_re_isLittleO_ofReal twoRegular_transfer_complex_thirdOrder

theorem twoRegularGraphCount_div_factorial_thirdOrder :
    (fun n : ℕ =>
      twoRegularGraphCount n / (n.factorial : ℝ) -
        (twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            twoRegularThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  refine twoRegularEGFCoeff_thirdOrder.congr_left ?_
  intro n
  rw [twoRegularGraphCount_div_factorial]

namespace TwoRegularClass

theorem twoRegularClass_counts_div_factorial_thirdOrder :
    (fun n : ℕ =>
      (twoRegularClass.counts n : ℝ) / (n.factorial : ℝ) -
        (twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          twoRegularSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            twoRegularThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  refine twoRegularGraphCount_div_factorial_thirdOrder.congr_left ?_
  intro n
  rw [twoRegularClass_counts_eq_twoRegularGraphCount n]

end TwoRegularClass

end
