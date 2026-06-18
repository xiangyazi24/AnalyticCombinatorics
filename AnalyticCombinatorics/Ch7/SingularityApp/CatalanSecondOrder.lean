import AnalyticCombinatorics.Ch4.Analytic.TransferSecondOrderGeneral
import AnalyticCombinatorics.Ch4.Analytic.Catalan
import AnalyticCombinatorics.Ch7.SingularityApp.Motzkin
import Mathlib.RingTheory.PowerSeries.Catalan

/-!
# Second-order Catalan asymptotics

This file applies the general second-order transfer theorem at `α = -1/2` to
the centered rescaled Catalan OGF

`2 / (1 + sqrt (1 - z)) - 2 - 2 * (1 - z)`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

def catalanAsymptoticConstant : ℝ :=
  1 / Real.sqrt Real.pi

def catalanRelativeSecondConstant : ℝ :=
  -(9 / 8 : ℝ)

def catalanSecondAsymptoticConstant : ℝ :=
  -(9 / (8 * Real.sqrt Real.pi) : ℝ)

def catalanSeriesℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n => (catalan n : ℂ)

@[simp] lemma coeff_catalanSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n catalanSeriesℂ = (catalan n : ℂ) := by
  simp [catalanSeriesℂ]

lemma catalanSeriesℂ_sq_mul_X_add_one :
    catalanSeriesℂ ^ 2 * PowerSeries.X + 1 = catalanSeriesℂ := by
  ext n
  cases n with
  | zero =>
      simp [catalanSeriesℂ, catalan_zero]
  | succ n =>
      simp_rw [add_comm, map_add, PowerSeries.coeff_one, if_neg n.succ_ne_zero,
        zero_add, PowerSeries.coeff_succ_mul_X, sq, PowerSeries.coeff_mul,
        coeff_catalanSeriesℂ, catalan_succ']
      norm_num [Nat.cast_sum]

def catalanRescaledSeriesℂ : PowerSeries ℂ :=
  PowerSeries.rescale ((4 : ℂ)⁻¹) catalanSeriesℂ

@[simp] lemma coeff_catalanRescaledSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n catalanRescaledSeriesℂ =
      (catalan n : ℂ) * ((4 : ℂ)⁻¹) ^ n := by
  simp [catalanRescaledSeriesℂ, PowerSeries.coeff_rescale, mul_comm]

def catalanScaleX : PowerSeries ℂ :=
  PowerSeries.C ((4 : ℂ)⁻¹) * PowerSeries.X

lemma catalanRescaledSeriesℂ_quadratic :
    catalanRescaledSeriesℂ =
      1 + catalanScaleX * catalanRescaledSeriesℂ ^ 2 := by
  change PowerSeries.rescale ((4 : ℂ)⁻¹) catalanSeriesℂ =
    1 + catalanScaleX * catalanRescaledSeriesℂ ^ 2
  rw [← catalanSeriesℂ_sq_mul_X_add_one]
  simp only [map_add, map_mul, map_one, map_pow, PowerSeries.rescale_X]
  simp [catalanRescaledSeriesℂ, catalanScaleX, pow_two, mul_assoc]
  ring

def catalanSqrtOneSub (z : ℂ) : ℂ :=
  (1 - z) ^ (1 / 2 : ℂ)

def catalanRescaledFun (z : ℂ) : ℂ :=
  2 / (1 + catalanSqrtOneSub z)

def catalanOneSubSeriesℂ : PowerSeries ℂ :=
  (1 : PowerSeries ℂ) - PowerSeries.X

def catalanAdjustedRescaledSeriesℂ : PowerSeries ℂ :=
  catalanRescaledSeriesℂ - PowerSeries.C (2 : ℂ) -
    PowerSeries.C (2 : ℂ) * catalanOneSubSeriesℂ

def catalanAdjustedRescaledFMLS : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS catalanAdjustedRescaledSeriesℂ

def catalanAdjustedRescaledFun (z : ℂ) : ℂ :=
  catalanRescaledFun z - 2 - 2 * (1 - z)

lemma catalanSqrtDenom_ne_zero (z : ℂ) :
    1 + catalanSqrtOneSub z ≠ 0 := by
  intro h
  have hs : catalanSqrtOneSub z = -1 := by
    have h' : catalanSqrtOneSub z + 1 = 0 := by
      simpa [add_comm] using h
    rw [add_eq_zero_iff_eq_neg] at h'
    exact h'
  have hsq : (1 : ℂ) - z = 1 := by
    have hpow := congrArg (fun w : ℂ => w ^ 2) hs
    simpa [catalanSqrtOneSub, Complex_cpow_half_sq] using hpow
  have hz : z = 0 := by
    linear_combination -hsq
  subst z
  norm_num [catalanSqrtOneSub] at hs

lemma catalanRescaledFun_quadratic (z : ℂ) :
    catalanRescaledFun z =
      1 + ((4 : ℂ)⁻¹ * z) * catalanRescaledFun z ^ 2 := by
  let s : ℂ := catalanSqrtOneSub z
  have hs_sq : s ^ 2 = 1 - z := by
    dsimp [s, catalanSqrtOneSub]
    exact Complex_cpow_half_sq (1 - z)
  have hden : 1 + s ≠ 0 := by
    dsimp [s]
    exact catalanSqrtDenom_ne_zero z
  have hz_eq : z = 1 - s ^ 2 := by
    rw [hs_sq]
    ring
  unfold catalanRescaledFun
  change 2 / (1 + s) = 1 + (4 : ℂ)⁻¹ * z * (2 / (1 + s)) ^ 2
  field_simp [hden]
  rw [hz_eq]
  ring

lemma analyticAt_catalanSqrtOneSub_zero :
    AnalyticAt ℂ catalanSqrtOneSub (0 : ℂ) := by
  have hbase : AnalyticAt ℂ (fun z : ℂ => 1 - z) (0 : ℂ) :=
    analyticAt_const.sub analyticAt_id
  have hexp : AnalyticAt ℂ (fun _ : ℂ => (1 / 2 : ℂ)) (0 : ℂ) :=
    analyticAt_const
  have hslit : (1 : ℂ) - 0 ∈ Complex.slitPlane := by
    simpa only [sub_zero] using
      Complex.ofReal_mem_slitPlane.2 (by norm_num : (0 : ℝ) < 1)
  convert hbase.cpow hexp hslit using 1

lemma analyticAt_catalanRescaledFun_zero :
    AnalyticAt ℂ catalanRescaledFun (0 : ℂ) := by
  have hden : AnalyticAt ℂ (fun z : ℂ => 1 + catalanSqrtOneSub z) (0 : ℂ) :=
    analyticAt_const.add analyticAt_catalanSqrtOneSub_zero
  have hnum : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) (0 : ℂ) := analyticAt_const
  simpa [catalanRescaledFun] using
    hnum.div hden (by norm_num [catalanSqrtOneSub])

lemma coeff_catalanScaleX_mul_zero (P : PowerSeries ℂ) :
    PowerSeries.coeff (R := ℂ) 0 (catalanScaleX * P) = 0 := by
  simp [catalanScaleX]

lemma coeff_catalanScaleX_mul_succ (P : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1) (catalanScaleX * P) =
      (4 : ℂ)⁻¹ * PowerSeries.coeff (R := ℂ) n P := by
  rw [catalanScaleX, mul_assoc, PowerSeries.coeff_C_mul]
  simp

lemma catalan_quadratic_solution_unique {P Q : PowerSeries ℂ}
    (hP : P = 1 + catalanScaleX * P ^ 2)
    (hQ : Q = 1 + catalanScaleX * Q ^ 2) :
    P = Q := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          calc
            PowerSeries.coeff (R := ℂ) 0 P =
                PowerSeries.coeff (R := ℂ) 0 (1 + catalanScaleX * P ^ 2) :=
              congrArg (fun S : PowerSeries ℂ => PowerSeries.coeff (R := ℂ) 0 S) hP
            _ = 1 := by simp [catalanScaleX]
            _ = PowerSeries.coeff (R := ℂ) 0 (1 + catalanScaleX * Q ^ 2) := by
                simp [catalanScaleX]
            _ = PowerSeries.coeff (R := ℂ) 0 Q :=
              (congrArg (fun S : PowerSeries ℂ => PowerSeries.coeff (R := ℂ) 0 S) hQ).symm
      | succ n =>
          have hsquares :
              PowerSeries.coeff (R := ℂ) n (P ^ 2) =
                PowerSeries.coeff (R := ℂ) n (Q ^ 2) := by
            rw [pow_two, pow_two, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
            apply Finset.sum_congr rfl
            intro kl hkl
            have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
            have h1 : kl.1 < n + 1 := by omega
            have h2 : kl.2 < n + 1 := by omega
            rw [ih kl.1 h1, ih kl.2 h2]
          calc
            PowerSeries.coeff (R := ℂ) (n + 1) P =
                PowerSeries.coeff (R := ℂ) (n + 1)
                  (1 + catalanScaleX * P ^ 2) :=
              congrArg (fun S : PowerSeries ℂ => PowerSeries.coeff (R := ℂ) (n + 1) S) hP
            _ = (4 : ℂ)⁻¹ * PowerSeries.coeff (R := ℂ) n (P ^ 2) := by
                simp [coeff_catalanScaleX_mul_succ]
            _ = (4 : ℂ)⁻¹ * PowerSeries.coeff (R := ℂ) n (Q ^ 2) := by rw [hsquares]
            _ = PowerSeries.coeff (R := ℂ) (n + 1)
                  (1 + catalanScaleX * Q ^ 2) := by
                simp [coeff_catalanScaleX_mul_succ]
            _ = PowerSeries.coeff (R := ℂ) (n + 1) Q :=
              (congrArg (fun S : PowerSeries ℂ =>
                PowerSeries.coeff (R := ℂ) (n + 1) S) hQ).symm

lemma catalan_taylor_quadratic
    (q : FormalMultilinearSeries ℂ ℂ ℂ)
    (hq : HasFPowerSeriesAt catalanRescaledFun q (0 : ℂ)) :
    powerSeriesOfFMLSℂ q =
      1 + catalanScaleX * (powerSeriesOfFMLSℂ q) ^ 2 := by
  let Q : PowerSeries ℂ := powerSeriesOfFMLSℂ q
  have hqQ : HasFPowerSeriesAt catalanRescaledFun (PowerSeries.toFMLS Q) (0 : ℂ) := by
    simpa [Q, toFMLS_powerSeriesOfFMLSℂ] using hq
  have hscale : HasFPowerSeriesAt (fun z : ℂ => (4 : ℂ)⁻¹ * z)
      (PowerSeries.toFMLS catalanScaleX) (0 : ℂ) := by
    have h := hasFPowerSeriesAt_mul_toFMLS
      (hasFPowerSeriesAt_const_toFMLS_C ((4 : ℂ)⁻¹))
      hasFPowerSeriesAt_id_toFMLS_X
    simpa [catalanScaleX] using h
  have hsquare : HasFPowerSeriesAt (fun z : ℂ => catalanRescaledFun z * catalanRescaledFun z)
      (PowerSeries.toFMLS (Q ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using hasFPowerSeriesAt_mul_toFMLS hqQ hqQ
  have hprod : HasFPowerSeriesAt
      (fun z : ℂ => ((4 : ℂ)⁻¹ * z) *
        (catalanRescaledFun z * catalanRescaledFun z))
      (PowerSeries.toFMLS (catalanScaleX * Q ^ 2)) (0 : ℂ) := by
    simpa using hasFPowerSeriesAt_mul_toFMLS hscale hsquare
  have hone := hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hrhs : HasFPowerSeriesAt
      (fun z : ℂ => 1 + ((4 : ℂ)⁻¹ * z) *
        (catalanRescaledFun z * catalanRescaledFun z))
      (PowerSeries.toFMLS (1 + catalanScaleX * Q ^ 2)) (0 : ℂ) := by
    simpa [Pi.add_apply, toFMLS_add] using hone.add hprod
  have hrhs_f : HasFPowerSeriesAt catalanRescaledFun
      (PowerSeries.toFMLS (1 + catalanScaleX * Q ^ 2)) (0 : ℂ) := by
    convert hrhs using 1
    · ext z
      calc
        catalanRescaledFun z =
            1 + ((4 : ℂ)⁻¹ * z) * catalanRescaledFun z ^ 2 :=
          catalanRescaledFun_quadratic z
        _ = 1 + ((4 : ℂ)⁻¹ * z) *
            (catalanRescaledFun z * catalanRescaledFun z) := by ring
  have hFMLS := hqQ.eq_formalMultilinearSeries hrhs_f
  have hQ : Q = 1 + catalanScaleX * Q ^ 2 :=
    PowerSeries_toFMLS_injective hFMLS
  simpa [Q] using hQ

theorem catalanRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt catalanRescaledFun
      (PowerSeries.toFMLS catalanRescaledSeriesℂ) (0 : ℂ) := by
  let q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ
      (fun n => iteratedDeriv n catalanRescaledFun (0 : ℂ) / (n.factorial : ℂ))
  have hq : HasFPowerSeriesAt catalanRescaledFun q (0 : ℂ) :=
    analyticAt_catalanRescaledFun_zero.hasFPowerSeriesAt
  let Q : PowerSeries ℂ := powerSeriesOfFMLSℂ q
  have hQquad : Q = 1 + catalanScaleX * Q ^ 2 := by
    simpa [Q] using catalan_taylor_quadratic q hq
  have hQ : Q = catalanRescaledSeriesℂ :=
    catalan_quadratic_solution_unique hQquad catalanRescaledSeriesℂ_quadratic
  have hqQ : HasFPowerSeriesAt catalanRescaledFun (PowerSeries.toFMLS Q) (0 : ℂ) := by
    simpa [Q, toFMLS_powerSeriesOfFMLSℂ] using hq
  simpa [hQ] using hqQ

lemma hasFPowerSeriesAt_catalanOneSub :
    HasFPowerSeriesAt (fun z : ℂ => 1 - z)
      (PowerSeries.toFMLS catalanOneSubSeriesℂ) (0 : ℂ) := by
  have hconst := hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hid := hasFPowerSeriesAt_id_toFMLS_X
  have hsub := hconst.sub hid
  simpa [catalanOneSubSeriesℂ, toFMLS_sub] using hsub

theorem catalanAdjustedRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt catalanAdjustedRescaledFun
      catalanAdjustedRescaledFMLS (0 : ℂ) := by
  have hlinear : HasFPowerSeriesAt (fun z : ℂ => 2 * (1 - z))
      (PowerSeries.toFMLS (PowerSeries.C (2 : ℂ) * catalanOneSubSeriesℂ)) (0 : ℂ) := by
    have hconst := hasFPowerSeriesAt_const_toFMLS_C (2 : ℂ)
    simpa [mul_assoc] using hasFPowerSeriesAt_mul_toFMLS hconst hasFPowerSeriesAt_catalanOneSub
  have hconst := hasFPowerSeriesAt_const_toFMLS_C (2 : ℂ)
  have hsub := (catalanRescaledFun_hasFPowerSeriesAt_zero.sub hconst).sub hlinear
  simpa [catalanAdjustedRescaledFun, catalanAdjustedRescaledFMLS,
    catalanAdjustedRescaledSeriesℂ, toFMLS_sub] using hsub

lemma analyticOnNhd_catalanSqrtOneSub :
    AnalyticOnNhd ℂ catalanSqrtOneSub
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have h := analyticOnNhd_one_sub_cpow_deltaDomain (α := (-(1 / 2 : ℂ)))
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4) (by positivity) (by nlinarith [Real.pi_pos])
  convert h using 1
  ext z
  norm_num [catalanSqrtOneSub]

lemma analyticOnNhd_catalanRescaledFun :
    AnalyticOnNhd ℂ catalanRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hden : AnalyticOnNhd ℂ (fun z : ℂ => 1 + catalanSqrtOneSub z)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) :=
    analyticOnNhd_const.add analyticOnNhd_catalanSqrtOneSub
  simpa [catalanRescaledFun] using
    (analyticOnNhd_const.div hden (fun z _hz => catalanSqrtDenom_ne_zero z))

lemma analyticOnNhd_catalanAdjustedRescaledFun :
    AnalyticOnNhd ℂ catalanAdjustedRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hlinear : AnalyticOnNhd ℂ (fun z : ℂ => 2 * (1 - z))
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    simpa [smul_eq_mul] using
      (analyticOnNhd_const.mul (analyticOnNhd_const.sub analyticOnNhd_id))
  simpa [catalanAdjustedRescaledFun] using
    (analyticOnNhd_catalanRescaledFun.sub analyticOnNhd_const).sub hlinear

lemma coeff_catalanAdjustedRescaledSeriesℂ_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    PowerSeries.coeff (R := ℂ) n catalanAdjustedRescaledSeriesℂ =
      PowerSeries.coeff (R := ℂ) n catalanRescaledSeriesℂ := by
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hn1 : n ≠ 1 := ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  simp [catalanAdjustedRescaledSeriesℂ, catalanOneSubSeriesℂ, PowerSeries.coeff_C,
    PowerSeries.coeff_X, PowerSeries.coeff_one, hn0, hn1]

lemma coeff_catalanAdjustedRescaledFMLS_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    catalanAdjustedRescaledFMLS.coeff n =
      PowerSeries.coeff (R := ℂ) n catalanRescaledSeriesℂ := by
  rw [catalanAdjustedRescaledFMLS, PowerSeries.coeff_toFMLS,
    coeff_catalanAdjustedRescaledSeriesℂ_of_two_le hn]

lemma tendsto_catalanSqrtOneSub :
    Tendsto catalanSqrtOneSub
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  have hu : Tendsto (fun z : ℂ => 1 - z)
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 - z) 1 := by fun_prop
    simpa using Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds
  have hcpow := (Complex.continuousAt_cpow_const_of_re_pos (z := (0 : ℂ))
    (w := (1 / 2 : ℂ)) (Or.inl (by norm_num : (0 : ℝ) ≤ (0 : ℂ).re))
    (by norm_num)).tendsto.comp hu
  convert hcpow using 1
  ext z
  simp

lemma catalan_adjusted_residual_eq {z : ℂ} (hz : z ≠ 1) :
    catalanAdjustedRescaledFun z -
        (-2 : ℂ) * (1 - z) ^ (1 / 2 : ℂ) -
        (-2 : ℂ) * (1 - z) ^ (3 / 2 : ℂ) =
      (2 : ℂ) * ((1 - z) ^ 2) / (1 + catalanSqrtOneSub z) := by
  let u : ℂ := 1 - z
  let s : ℂ := catalanSqrtOneSub z
  have hu_ne : u ≠ 0 := by
    dsimp [u]
    exact sub_ne_zero.mpr (Ne.symm hz)
  have hs_sq : s ^ 2 = u := by
    dsimp [s, u, catalanSqrtOneSub]
    exact Complex_cpow_half_sq (1 - z)
  have hpow_three : u ^ (3 / 2 : ℂ) = u * s := by
    dsimp [s, u, catalanSqrtOneSub]
    rw [show (3 / 2 : ℂ) = 1 + (1 / 2 : ℂ) by norm_num]
    rw [Complex.cpow_add _ _ hu_ne, Complex.cpow_one]
  have hden : 1 + s ≠ 0 := by
    dsimp [s]
    exact catalanSqrtDenom_ne_zero z
  unfold catalanAdjustedRescaledFun catalanRescaledFun
  change 2 / (1 + s) - 2 - 2 * u - (-2) * s - (-2) * u ^ (3 / 2 : ℂ) =
    2 * u ^ 2 / (1 + s)
  rw [hpow_three, ← hs_sq]
  field_simp [hden]
  ring

lemma catalan_adjusted_singularity_norm_eq {z : ℂ} (hz : z ≠ 1) :
    ‖catalanAdjustedRescaledFun z -
        (-2 : ℂ) * (1 - z) ^ (1 / 2 : ℂ) -
        (-2 : ℂ) * (1 - z) ^ (3 / 2 : ℂ)‖ *
      ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)) =
    ‖(2 : ℂ) / (1 + catalanSqrtOneSub z)‖ * ‖catalanSqrtOneSub z‖ := by
  let u : ℂ := 1 - z
  let s : ℂ := catalanSqrtOneSub z
  have hu_ne : u ≠ 0 := by
    dsimp [u]
    exact sub_ne_zero.mpr (Ne.symm hz)
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  have hs_norm : ‖s‖ = ‖u‖ ^ (1 / 2 : ℝ) := by
    dsimp [s, u, catalanSqrtOneSub]
    convert Complex.norm_cpow_real ((1 : ℂ) - z) (1 / 2 : ℝ) using 1
    norm_num
  rw [catalan_adjusted_residual_eq hz]
  change ‖(2 : ℂ) * u ^ 2 / (1 + s)‖ * ‖u‖ ^ (-(3 / 2 : ℝ)) =
    ‖(2 : ℂ) / (1 + s)‖ * ‖s‖
  rw [show (2 : ℂ) * u ^ 2 / (1 + s) = ((2 : ℂ) / (1 + s)) * u ^ 2 by ring]
  rw [norm_mul, norm_pow]
  rw [show ‖u‖ ^ 2 = ‖u‖ ^ (2 : ℝ) by
    exact (Real.rpow_natCast ‖u‖ 2).symm]
  rw [show ‖(2 : ℂ) / (1 + s)‖ * ‖u‖ ^ (2 : ℝ) *
      ‖u‖ ^ (-(3 / 2 : ℝ)) =
      ‖(2 : ℂ) / (1 + s)‖ *
        (‖u‖ ^ (2 : ℝ) * ‖u‖ ^ (-(3 / 2 : ℝ))) by ring]
  have hpow : ‖u‖ ^ (2 : ℝ) * ‖u‖ ^ (-(3 / 2 : ℝ)) =
      ‖u‖ ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hu_pos]
    norm_num
  rw [hpow, ← hs_norm]

lemma catalanAdjustedRescaledFun_singularity_twoTerm :
    Tendsto
      (fun z : ℂ =>
        ‖catalanAdjustedRescaledFun z -
            (-2 : ℂ) * (1 - z) ^ (1 / 2 : ℂ) -
            (-2 : ℂ) * (1 - z) ^ (3 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(3 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hden : Tendsto
      (fun z : ℂ => ‖(2 : ℂ) / (1 + catalanSqrtOneSub z)‖) l (𝓝 ‖(2 : ℂ)‖) := by
    have hone : Tendsto (fun _ : ℂ => (1 : ℂ)) l (𝓝 (1 : ℂ)) := tendsto_const_nhds
    have hdenom : Tendsto (fun z : ℂ => 1 + catalanSqrtOneSub z) l (𝓝 (1 : ℂ)) := by
      simpa using hone.add tendsto_catalanSqrtOneSub
    have hcomplex : Tendsto
        (fun z : ℂ => (2 : ℂ) / (1 + catalanSqrtOneSub z)) l (𝓝 ((2 : ℂ) / 1)) := by
      exact tendsto_const_nhds.div hdenom (by norm_num : (1 : ℂ) ≠ 0)
    simpa using hcomplex.norm
  have hprod : Tendsto
      (fun z : ℂ => ‖(2 : ℂ) / (1 + catalanSqrtOneSub z)‖ *
        ‖catalanSqrtOneSub z‖) l (𝓝 0) := by
    convert hden.mul tendsto_catalanSqrtOneSub.norm using 1
    norm_num
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (catalan_adjusted_singularity_norm_eq hz.2.1).symm

lemma catalan_neg_half_pole :
    ∀ m : ℕ, (-(1 / 2 : ℝ)) ≠ 1 - (m : ℝ) := by
  intro m h
  have hm2R : (2 * m : ℝ) = 3 := by nlinarith
  have hm2N : 2 * m = 3 := by exact_mod_cast hm2R
  omega

lemma catalan_Real_Gamma_neg_half :
    Real.Gamma (-(1 / 2 : ℝ)) = -2 * Real.sqrt Real.pi := by
  have h := Real.Gamma_add_one (s := (-(1 / 2 : ℝ)))
    (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [Real.Gamma_one_half_eq] at h
  linarith

lemma catalan_Real_Gamma_neg_three_halves :
    Real.Gamma (-(3 / 2 : ℝ)) = 4 * Real.sqrt Real.pi / 3 := by
  have h := Real.Gamma_add_one (s := (-(3 / 2 : ℝ)))
    (by norm_num : (-(3 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [catalan_Real_Gamma_neg_half] at h
  nlinarith

lemma catalanSecondAsymptoticConstant_eq_relative :
    catalanSecondAsymptoticConstant =
      catalanAsymptoticConstant * catalanRelativeSecondConstant := by
  unfold catalanSecondAsymptoticConstant catalanAsymptoticConstant
    catalanRelativeSecondConstant
  ring

lemma catalan_secondOrder_model_complex_eq (n : ℕ) :
    ((-2 : ℂ) *
        ((((n : ℝ) ^ ((-(1 / 2 : ℝ)) - 1) /
              Real.Gamma (-(1 / 2 : ℝ)) : ℝ) : ℂ) +
          ((((-(1 / 2 : ℝ)) * ((-(1 / 2 : ℝ)) - 1) / 2 /
                Real.Gamma (-(1 / 2 : ℝ))) *
              (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) : ℝ) : ℂ)) +
      (-2 : ℂ) *
        (((n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) /
          Real.Gamma ((-(1 / 2 : ℝ)) - 1) : ℝ) : ℂ)) =
      (((catalanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
          catalanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have hpow1 : (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 1) =
      (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    congr 1
    norm_num
  have hpow2 : (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2) =
      (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
    congr 1
    norm_num
  rw [hpow1, hpow2]
  unfold catalanAsymptoticConstant catalanSecondAsymptoticConstant
  rw [catalan_Real_Gamma_neg_half,
    show (-(1 / 2 : ℝ)) - 1 = -(3 / 2 : ℝ) by norm_num,
    catalan_Real_Gamma_neg_three_halves]
  norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_neg]
  ring

theorem catalanAdjustedRescaledCoeff_secondOrder :
    (fun n : ℕ =>
      catalanAdjustedRescaledFMLS.coeff n -
        (((catalanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            catalanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have htransfer := transfer_twoTerm_secondOrder_general
    (α := (-(1 / 2 : ℝ))) (C0 := (-2 : ℂ)) (C1 := (-2 : ℂ))
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (f := catalanAdjustedRescaledFun) (p := catalanAdjustedRescaledFMLS)
    catalan_neg_half_pole (by norm_num) (by positivity) ?_
    catalanAdjustedRescaledFun_hasFPowerSeriesAt_zero
    analyticOnNhd_catalanAdjustedRescaledFun ?_
  · have hcomplex :
        (fun n : ℕ =>
          catalanAdjustedRescaledFMLS.coeff n -
            (((catalanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
                catalanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
          =o[atTop] (fun n : ℕ => (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 2)) := by
      refine htransfer.congr_left ?_
      intro n
      rw [catalan_secondOrder_model_complex_eq n]
    convert hcomplex using 1
    ext n
    congr 1
    norm_num
  · nlinarith [Real.pi_pos]
  · convert catalanAdjustedRescaledFun_singularity_twoTerm using 1
    ext z
    norm_num

theorem catalanRescaled_complex_secondOrder :
    (fun n : ℕ =>
      (catalan n : ℂ) * ((4 : ℂ)⁻¹) ^ n -
        (((catalanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            catalanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have h := catalanAdjustedRescaledCoeff_secondOrder
  refine h.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [coeff_catalanAdjustedRescaledFMLS_of_two_le hn, coeff_catalanRescaledSeriesℂ]

theorem catalan_complex_secondOrder :
    (fun n : ℕ =>
      (catalan n : ℂ) -
        (4 : ℂ) ^ n *
          (((catalanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
              catalanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop]
        (fun n : ℕ =>
          ‖(4 : ℂ) ^ n *
            (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)‖) := by
  have hrescaled := catalanRescaled_complex_secondOrder
  rw [Asymptotics.isLittleO_iff] at hrescaled ⊢
  intro c hc
  have hbound := hrescaled hc
  filter_upwards [hbound] with n hn
  let model : ℂ :=
    (((catalanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
        catalanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))
  let r : ℂ := (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)
  have hpow_cancel : (4 : ℂ) ^ n * ((4 : ℂ)⁻¹) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hcancel :
      (4 : ℂ) ^ n * ((catalan n : ℂ) * ((4 : ℂ)⁻¹) ^ n) =
        (catalan n : ℂ) := by
    calc
      (4 : ℂ) ^ n * ((catalan n : ℂ) * ((4 : ℂ)⁻¹) ^ n)
          = (catalan n : ℂ) * ((4 : ℂ) ^ n * ((4 : ℂ)⁻¹) ^ n) := by ring
      _ = (catalan n : ℂ) := by rw [hpow_cancel, mul_one]
  have hleft :
      (catalan n : ℂ) - (4 : ℂ) ^ n * model =
        (4 : ℂ) ^ n * (((catalan n : ℂ) * ((4 : ℂ)⁻¹) ^ n) - model) := by
    rw [mul_sub, hcancel]
  have hnorm_target :
      ‖‖(4 : ℂ) ^ n * r‖‖ = ‖(4 : ℂ) ^ n‖ * ‖r‖ := by
    simp [norm_mul]
  calc
    ‖(catalan n : ℂ) - (4 : ℂ) ^ n * model‖
        = ‖(4 : ℂ) ^ n *
            (((catalan n : ℂ) * ((4 : ℂ)⁻¹) ^ n) - model)‖ := by rw [hleft]
    _ = ‖(4 : ℂ) ^ n‖ *
          ‖(catalan n : ℂ) * ((4 : ℂ)⁻¹) ^ n - model‖ := by rw [norm_mul]
    _ ≤ ‖(4 : ℂ) ^ n‖ * (c * ‖(n : ℝ) ^ (-(5 / 2 : ℝ))‖) :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = c * ‖‖(4 : ℂ) ^ n * r‖‖ := by
        rw [hnorm_target]
        simp [r, Complex.norm_real]
        ring

end
