import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrderGeneral

/-!
# Second-order square-root singularity applicator

This file packages the `α = -1/2` case of
`transfer_twoTerm_secondOrder_general`.  The caller supplies the local
two-term square-root singular expansion after subtracting the analytic constant
and linear terms at the dominant point.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

def sqrtSingularityC0 (B0 : ℂ) : ℂ :=
  -B0 / (((2 * Real.sqrt Real.pi : ℝ) : ℂ))

def sqrtSingularityC1Rescaled (B0 B1 : ℂ) : ℂ :=
  -(3 : ℂ) * B0 / (((16 * Real.sqrt Real.pi : ℝ) : ℂ)) -
    (3 : ℂ) * B1 / (((4 * Real.sqrt Real.pi : ℝ) : ℂ))

def sqrtSingularityC1 (ρ : ℝ) (Bρ Bderivρ : ℂ) : ℂ :=
  sqrtSingularityC1Rescaled Bρ (((ρ : ℝ) : ℂ) * Bderivρ)

def sqrtSingularityRelativeC1 (B0 B1 : ℂ) : ℂ :=
  (3 / 8 : ℂ) + (3 / 2 : ℂ) * B1 / B0

lemma sqrt_toFMLS_add (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f + g) = PowerSeries.toFMLS f + PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma sqrt_toFMLS_sub (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f - g) = PowerSeries.toFMLS f - PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma sqrt_toFMLS_C (c : ℂ) :
    PowerSeries.toFMLS (PowerSeries.C c) =
      constFormalMultilinearSeries ℂ ℂ c := by
  ext n
  cases n <;>
    simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
      constFormalMultilinearSeries]

lemma sqrt_hasFPowerSeriesAt_const_toFMLS_C (c : ℂ) :
    HasFPowerSeriesAt (fun _ : ℂ => c)
      (PowerSeries.toFMLS (PowerSeries.C c)) (0 : ℂ) := by
  simpa [sqrt_toFMLS_C] using
    (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
      (c := c) (e := (0 : ℂ)))

lemma sqrt_toFMLS_C_mul_X (c : ℂ) :
    PowerSeries.toFMLS (PowerSeries.C c * (PowerSeries.X : PowerSeries ℂ)) =
      c • PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ) := by
  ext n
  cases n with
  | zero =>
      simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]
  | succ n =>
      cases n with
      | zero =>
          simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]
      | succ n =>
          simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
            PowerSeries.coeff_X]

lemma sqrt_hasFPowerSeriesAt_id_toFMLS_X :
    HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards with z
  let term : ℕ → ℂ :=
    fun n => z ^ n • (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)).coeff n
  have hsingle : HasSum term (term 1) := by
    apply hasSum_single
    intro n hn
    simp [term, PowerSeries.coeff_X, hn]
  convert hsingle using 1
  simp [term, PowerSeries.toFMLS]

def sqrtLinearAtOneSeries (A0 A1 : ℂ) : PowerSeries ℂ :=
  PowerSeries.C (A0 - A1) + PowerSeries.C A1 * PowerSeries.X

def sqrtLinearAtOneFun (A0 A1 : ℂ) (z : ℂ) : ℂ :=
  (A0 - A1) + A1 * z

def sqrtAdjustedSeries (P : PowerSeries ℂ) (A0 A1 : ℂ) : PowerSeries ℂ :=
  P - sqrtLinearAtOneSeries A0 A1

def sqrtAdjustedFun (f : ℂ → ℂ) (A0 A1 : ℂ) (z : ℂ) : ℂ :=
  f z - sqrtLinearAtOneFun A0 A1 z

lemma sqrtLinearAtOneFun_eq (A0 A1 z : ℂ) :
    sqrtLinearAtOneFun A0 A1 z = A0 + A1 * (z - 1) := by
  unfold sqrtLinearAtOneFun
  ring

lemma sqrt_neg_half_pole :
    ∀ m : ℕ, (-(1 / 2 : ℝ)) ≠ 1 - (m : ℝ) := by
  intro m h
  have hm2R : (2 * m : ℝ) = 3 := by nlinarith
  have hm2N : 2 * m = 3 := by exact_mod_cast hm2R
  omega

lemma sqrt_Real_Gamma_neg_half :
    Real.Gamma (-(1 / 2 : ℝ)) = -2 * Real.sqrt Real.pi := by
  have h := Real.Gamma_add_one (s := (-(1 / 2 : ℝ)))
    (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [Real.Gamma_one_half_eq] at h
  linarith

lemma sqrt_Real_Gamma_neg_three_halves :
    Real.Gamma (-(3 / 2 : ℝ)) = 4 * Real.sqrt Real.pi / 3 := by
  have h := Real.Gamma_add_one (s := (-(3 / 2 : ℝ)))
    (by norm_num : (-(3 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [sqrt_Real_Gamma_neg_half] at h
  nlinarith

lemma sqrtLinearAtOneFun_hasFPowerSeriesAt_zero (A0 A1 : ℂ) :
    HasFPowerSeriesAt (sqrtLinearAtOneFun A0 A1)
      (PowerSeries.toFMLS (sqrtLinearAtOneSeries A0 A1)) (0 : ℂ) := by
  have hconst := sqrt_hasFPowerSeriesAt_const_toFMLS_C (A0 - A1)
  have hid := sqrt_hasFPowerSeriesAt_id_toFMLS_X
  have hlin := hid.const_smul (c := A1)
  have hsum := hconst.add hlin
  convert hsum using 1
  ext n
  cases n with
  | zero =>
      simp [sqrtLinearAtOneSeries]
  | succ n =>
      cases n with
      | zero =>
          simp [sqrtLinearAtOneSeries]
      | succ n =>
          simp [sqrtLinearAtOneSeries, PowerSeries.coeff_X]

lemma analyticOnNhd_sqrtLinearAtOneFun (A0 A1 : ℂ) (s : Set ℂ) :
    AnalyticOnNhd ℂ (sqrtLinearAtOneFun A0 A1) s := by
  simpa [sqrtLinearAtOneFun] using
    analyticOnNhd_const.add (analyticOnNhd_const.mul analyticOnNhd_id)

lemma sqrtAdjustedFun_hasFPowerSeriesAt_zero
    {f : ℂ → ℂ} {P : PowerSeries ℂ} {A0 A1 : ℂ}
    (hp : HasFPowerSeriesAt f (PowerSeries.toFMLS P) (0 : ℂ)) :
    HasFPowerSeriesAt (sqrtAdjustedFun f A0 A1)
      (PowerSeries.toFMLS (sqrtAdjustedSeries P A0 A1)) (0 : ℂ) := by
  have hlin := sqrtLinearAtOneFun_hasFPowerSeriesAt_zero A0 A1
  have hsub := hp.sub hlin
  simpa [sqrtAdjustedFun, sqrtAdjustedSeries, sqrt_toFMLS_sub] using hsub

lemma analyticOnNhd_sqrtAdjustedFun
    {R φ : ℝ} {f : ℂ → ℂ} {A0 A1 : ℂ}
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ)) :
    AnalyticOnNhd ℂ (sqrtAdjustedFun f A0 A1) (DeltaDomainArg R φ) := by
  simpa [sqrtAdjustedFun] using
    hΔ.sub (analyticOnNhd_sqrtLinearAtOneFun A0 A1 (DeltaDomainArg R φ))

lemma coeff_sqrtLinearAtOneSeries_of_two_le
    {A0 A1 : ℂ} {n : ℕ} (hn : 2 ≤ n) :
    PowerSeries.coeff (R := ℂ) n (sqrtLinearAtOneSeries A0 A1) = 0 := by
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hn1 : n ≠ 1 := ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  simp [sqrtLinearAtOneSeries, PowerSeries.coeff_X, PowerSeries.coeff_C, hn0, hn1]

lemma coeff_sqrtAdjustedSeries_of_two_le
    {P : PowerSeries ℂ} {A0 A1 : ℂ} {n : ℕ} (hn : 2 ≤ n) :
    (PowerSeries.toFMLS (sqrtAdjustedSeries P A0 A1)).coeff n =
      PowerSeries.coeff (R := ℂ) n P := by
  rw [PowerSeries.coeff_toFMLS]
  simp [sqrtAdjustedSeries, coeff_sqrtLinearAtOneSeries_of_two_le hn]

lemma sqrt_secondOrder_model_complex_eq (B0 B1 : ℂ) (n : ℕ) :
    (B0 *
        ((((n : ℝ) ^ ((-(1 / 2 : ℝ)) - 1) /
              Real.Gamma (-(1 / 2 : ℝ)) : ℝ) : ℂ) +
          ((((-(1 / 2 : ℝ)) * ((-(1 / 2 : ℝ)) - 1) / 2 /
                Real.Gamma (-(1 / 2 : ℝ))) *
              (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) : ℝ) : ℂ)) +
      (-B1) *
        (((n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) /
          Real.Gamma ((-(1 / 2 : ℝ)) - 1) : ℝ) : ℂ)) =
      sqrtSingularityC0 B0 *
          (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
        sqrtSingularityC1Rescaled B0 B1 *
          (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hpow1 : (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 1) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    congr 1
    norm_num
  have hpow2 : (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) =
      (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
    congr 1
    norm_num
  rw [hpow1, hpow2]
  unfold sqrtSingularityC0 sqrtSingularityC1Rescaled
  rw [sqrt_Real_Gamma_neg_half,
    show (-(1 / 2 : ℝ)) - 1 = -(3 / 2 : ℝ) by norm_num,
    sqrt_Real_Gamma_neg_three_halves]
  norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_neg, sub_eq_add_neg]
  ring

theorem sqrt_singularity_secondOrder_rescaled_of_singularity
    {R φ : ℝ} {f : ℂ → ℂ} {P : PowerSeries ℂ}
    {A0 A1 B0 B1 : ℂ}
    (hB0 : B0 ≠ 0)
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f (PowerSeries.toFMLS P) (0 : ℂ))
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖sqrtAdjustedFun f A0 A1 z -
            B0 * (1 - z) ^ (1 / 2 : ℂ) -
            (-B1) * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n P -
        (sqrtSingularityC0 B0 *
            (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
          sqrtSingularityC1Rescaled B0 B1 *
            (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have _ := hB0
  have hp_adj := sqrtAdjustedFun_hasFPowerSeriesAt_zero
    (f := f) (P := P) (A0 := A0) (A1 := A1) hp
  have hΔ_adj := analyticOnNhd_sqrtAdjustedFun
    (R := R) (φ := φ) (f := f) (A0 := A0) (A1 := A1) hΔ
  have htransfer := transfer_twoTerm_secondOrder_general
    (α := (-(1 / 2 : ℝ))) (C0 := B0) (C1 := -B1)
    (R := R) (φ := φ)
    (f := sqrtAdjustedFun f A0 A1)
    (p := PowerSeries.toFMLS (sqrtAdjustedSeries P A0 A1))
    sqrt_neg_half_pole hR hφ0 hφ2 hp_adj hΔ_adj ?_
  · have hcomplex :
        (fun n : ℕ =>
          (PowerSeries.toFMLS (sqrtAdjustedSeries P A0 A1)).coeff n -
            (sqrtSingularityC0 B0 *
                (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
              sqrtSingularityC1Rescaled B0 B1 *
                (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
          =o[atTop] (fun n : ℕ => (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2)) := by
      refine htransfer.congr_left ?_
      intro n
      rw [sqrt_secondOrder_model_complex_eq B0 B1 n]
    have hmain :
        (fun n : ℕ =>
          (PowerSeries.toFMLS (sqrtAdjustedSeries P A0 A1)).coeff n -
            (sqrtSingularityC0 B0 *
                (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
              sqrtSingularityC1Rescaled B0 B1 *
                (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
          =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
      convert hcomplex using 1
      ext n
      congr 1
      norm_num
    refine hmain.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [coeff_sqrtAdjustedSeries_of_two_le hn]
  · convert hsing using 1
    ext z
    norm_num

theorem sqrt_singularity_secondOrder_original_of_rescaled_singularity
    {ρ R φ : ℝ} {F : ℂ → ℂ} {P : PowerSeries ℂ}
    {A0 A1 Bρ Bderivρ : ℂ}
    (hρ : 0 < ρ) (hBρ : Bρ ≠ 0)
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt (fun z : ℂ => F (((ρ : ℝ) : ℂ) * z))
      (PowerSeries.toFMLS (PowerSeries.rescale (((ρ : ℝ) : ℂ)) P)) (0 : ℂ))
    (hΔ : AnalyticOnNhd ℂ (fun z : ℂ => F (((ρ : ℝ) : ℂ) * z))
      (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖sqrtAdjustedFun (fun w : ℂ => F (((ρ : ℝ) : ℂ) * w)) A0 A1 z -
            Bρ * (1 - z) ^ (1 / 2 : ℂ) -
            (-(((ρ : ℝ) : ℂ) * Bderivρ)) * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n P -
        (((((ρ : ℝ) : ℂ)⁻¹) ^ n) *
          (sqrtSingularityC0 Bρ *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1 ρ Bρ Bderivρ *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))))
      =o[atTop]
        (fun n : ℕ =>
          ‖(((((ρ : ℝ) : ℂ)⁻¹) ^ n) *
            (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  let ρc : ℂ := ((ρ : ℝ) : ℂ)
  let B1 : ℂ := ρc * Bderivρ
  have hρc : ρc ≠ 0 := by
    dsimp [ρc]
    exact_mod_cast (ne_of_gt hρ)
  have hrescaled := sqrt_singularity_secondOrder_rescaled_of_singularity
    (R := R) (φ := φ)
    (f := fun z : ℂ => F (ρc * z))
    (P := PowerSeries.rescale ρc P)
    (A0 := A0) (A1 := A1) (B0 := Bρ) (B1 := B1)
    hBρ hR hφ0 hφ2 ?_ ?_ ?_
  · rw [Asymptotics.isLittleO_iff] at hrescaled ⊢
    intro c hc
    have hbound := hrescaled hc
    filter_upwards [hbound] with n hn
    let model : ℂ :=
      sqrtSingularityC0 Bρ *
          (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
        sqrtSingularityC1 ρ Bρ Bderivρ *
          (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)
    let r : ℂ := (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)
    have hC1 : sqrtSingularityC1 ρ Bρ Bderivρ =
        sqrtSingularityC1Rescaled Bρ B1 := by
      simp [sqrtSingularityC1, B1, ρc]
    have hcoeff_rescale :
        PowerSeries.coeff (R := ℂ) n (PowerSeries.rescale ρc P) =
          PowerSeries.coeff (R := ℂ) n P * ρc ^ n := by
      simp [PowerSeries.coeff_rescale, mul_comm]
    have hpow_cancel : ρc ^ n * ρc⁻¹ ^ n = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hρc, one_pow]
    have hleft :
        PowerSeries.coeff (R := ℂ) n P - ρc⁻¹ ^ n * model =
          ρc⁻¹ ^ n *
            (PowerSeries.coeff (R := ℂ) n (PowerSeries.rescale ρc P) -
              (sqrtSingularityC0 Bρ *
                  (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
                sqrtSingularityC1Rescaled Bρ B1 *
                  (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))) := by
      rw [hcoeff_rescale, ← hC1]
      dsimp [model]
      calc
        PowerSeries.coeff (R := ℂ) n P - ρc⁻¹ ^ n *
            (sqrtSingularityC0 Bρ *
                (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
              sqrtSingularityC1 ρ Bρ Bderivρ *
                (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))
            =
            ρc⁻¹ ^ n *
              (PowerSeries.coeff (R := ℂ) n P * ρc ^ n -
                (sqrtSingularityC0 Bρ *
                    (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
                  sqrtSingularityC1 ρ Bρ Bderivρ *
                    (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))) := by
              rw [mul_sub]
              have hcomm : ρc⁻¹ ^ n * (PowerSeries.coeff (R := ℂ) n P * ρc ^ n) =
                  PowerSeries.coeff (R := ℂ) n P * (ρc ^ n * ρc⁻¹ ^ n) := by
                ring
              rw [hcomm, hpow_cancel, mul_one]
        _ = ρc⁻¹ ^ n *
              (PowerSeries.coeff (R := ℂ) n P * ρc ^ n -
                (sqrtSingularityC0 Bρ *
                    (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
                  sqrtSingularityC1 ρ Bρ Bderivρ *
                    (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))) := rfl
    have hnorm_target :
        ‖‖ρc⁻¹ ^ n * r‖‖ = ‖ρc⁻¹ ^ n‖ * ‖(((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)‖ := by
      simp [r, norm_mul]
    calc
      ‖PowerSeries.coeff (R := ℂ) n P - ρc⁻¹ ^ n * model‖
          = ‖ρc⁻¹ ^ n *
              (PowerSeries.coeff (R := ℂ) n (PowerSeries.rescale ρc P) -
                (sqrtSingularityC0 Bρ *
                    (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
                  sqrtSingularityC1Rescaled Bρ B1 *
                    (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))‖ := by
              rw [hleft]
      _ = ‖ρc⁻¹ ^ n‖ *
            ‖PowerSeries.coeff (R := ℂ) n (PowerSeries.rescale ρc P) -
              (sqrtSingularityC0 Bρ *
                  (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
                sqrtSingularityC1Rescaled Bρ B1 *
                  (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))‖ := by
              rw [norm_mul]
      _ ≤ ‖ρc⁻¹ ^ n‖ * (c * ‖(n : ℝ) ^ (-(5 / 2 : ℝ))‖) := by
              exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = c * ‖‖ρc⁻¹ ^ n * r‖‖ := by
              rw [hnorm_target, Complex.norm_real]
              ring
      _ = c * ‖‖(((((ρ : ℝ) : ℂ)⁻¹) ^ n) *
            (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))‖‖ := by
              simp [ρc, r]
  · simpa [ρc] using hp
  · simpa [ρc] using hΔ
  · simpa [ρc, B1] using hsing

end
