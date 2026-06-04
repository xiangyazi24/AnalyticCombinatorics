import Mathlib
import AnalyticCombinatorics.Ch4.Analytic.Bridge
import AnalyticCombinatorics.Ch4.Analytic.TransferGeneral
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics

/-!
# Motzkin-number asymptotic

This file isolates the Motzkin recurrence and the constant produced by the
square-root singularity at `1 / 3`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

/-- Motzkin numbers, with `M 0 = 1` and
`M (n + 1) = M n + sum_{k < n} M k * M (n - 1 - k)`. -/
def motzkin : ℕ → ℕ
  | 0 => 1
  | n + 1 => motzkin n + ∑ k : Fin n, motzkin k * motzkin (n - 1 - k)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_self n
  · exact Nat.lt_succ_of_lt k.2
  · exact Nat.lt_succ_of_le
      ((Nat.sub_le (n - 1) k).trans (Nat.pred_le n))

@[simp] lemma motzkin_zero : motzkin 0 = 1 := by
  simp [motzkin]

@[simp] lemma motzkin_succ (n : ℕ) :
    motzkin (n + 1) =
      motzkin n + ∑ k : Fin n, motzkin k * motzkin (n - 1 - k) := by
  simp [motzkin]

lemma motzkin_one : motzkin 1 = 1 := by
  simp

lemma motzkin_two : motzkin 2 = 2 := by
  norm_num [motzkin_succ, motzkin_one]

/-- The ordinary generating function as a formal power series over `ℂ`. -/
def motzkinSeriesℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n => (motzkin n : ℂ)

@[simp] lemma coeff_motzkinSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n motzkinSeriesℂ = (motzkin n : ℂ) := by
  simp [motzkinSeriesℂ]

@[simp] lemma constantCoeff_motzkinSeriesℂ :
    PowerSeries.constantCoeff motzkinSeriesℂ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

lemma coeff_X_mul_motzkinSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1) (PowerSeries.X * motzkinSeriesℂ) =
      (motzkin n : ℂ) := by
  simp

lemma coeff_X_sq_mul_motzkinSeriesℂ_sq (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1)
        ((PowerSeries.X : PowerSeries ℂ) ^ 2 * motzkinSeriesℂ ^ 2) =
      ∑ k : Fin n, (motzkin k : ℂ) * (motzkin (n - 1 - k) : ℂ) := by
  cases n with
  | zero =>
      simp [PowerSeries.coeff_X_pow_mul']
  | succ n =>
      rw [show n + 1 + 1 = n + 2 by omega]
      rw [PowerSeries.coeff_X_pow_mul (p := motzkinSeriesℂ ^ 2) (n := 2) (d := n)]
      rw [pow_two, PowerSeries.coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun x y => PowerSeries.coeff (R := ℂ) x motzkinSeriesℂ *
          PowerSeries.coeff (R := ℂ) y motzkinSeriesℂ) n]
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro x hx
      have hxle : x ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      simp [hxle]

/-- The Motzkin OGF satisfies `M = 1 + X M + X^2 M^2`. -/
theorem motzkinSeriesℂ_eq_one_add_X_mul_add_X_sq_mul_sq :
    motzkinSeriesℂ =
      1 + PowerSeries.X * motzkinSeriesℂ +
        (PowerSeries.X : PowerSeries ℂ) ^ 2 * motzkinSeriesℂ ^ 2 := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      simp only [coeff_motzkinSeriesℂ, map_add, PowerSeries.coeff_one, Nat.succ_ne_zero,
        ↓reduceIte, zero_add]
      rw [coeff_X_mul_motzkinSeriesℂ, coeff_X_sq_mul_motzkinSeriesℂ_sq]
      norm_num [motzkin_succ]

/-- The rescaled series `M(z / 3)`. -/
def motzkinRescaledSeriesℂ : PowerSeries ℂ :=
  PowerSeries.rescale ((3 : ℂ)⁻¹) motzkinSeriesℂ

@[simp] lemma coeff_motzkinRescaledSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n motzkinRescaledSeriesℂ =
      (motzkin n : ℂ) * ((3 : ℂ)⁻¹) ^ n := by
  simp [motzkinRescaledSeriesℂ, PowerSeries.coeff_rescale, mul_comm]

/-- The formal substitution variable `z / 3`. -/
def motzkinScaleX : PowerSeries ℂ :=
  PowerSeries.C ((3 : ℂ)⁻¹) * PowerSeries.X

lemma motzkinRescaledSeriesℂ_quadratic :
    motzkinRescaledSeriesℂ =
      1 + motzkinScaleX * motzkinRescaledSeriesℂ +
        (motzkinScaleX * motzkinRescaledSeriesℂ) ^ 2 := by
  change PowerSeries.rescale ((3 : ℂ)⁻¹) motzkinSeriesℂ =
    1 + motzkinScaleX * motzkinRescaledSeriesℂ +
      (motzkinScaleX * motzkinRescaledSeriesℂ) ^ 2
  rw [motzkinSeriesℂ_eq_one_add_X_mul_add_X_sq_mul_sq]
  simp only [map_add, map_mul, map_one, map_pow, PowerSeries.rescale_X]
  simp [motzkinRescaledSeriesℂ, motzkinScaleX, pow_two, mul_assoc]
  ring

/-- The singular coefficient of `M(z / 3)` at `z = 1`. -/
def motzkinSingularCoeff : ℂ := -((3 * Real.sqrt 3 : ℝ) : ℂ)

def motzkinSqrtPlus (z : ℂ) : ℂ :=
  (1 + z / 3) ^ (1 / 2 : ℂ)

def motzkinSqrtOneSub (z : ℂ) : ℂ :=
  (1 - z) ^ (1 / 2 : ℂ)

def motzkinSqrtThreeℂ : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)

/-- Denominator of the explicit rescaled Motzkin OGF. -/
def motzkinRescaledDenominator (z : ℂ) : ℂ :=
  1 - z / 3 + motzkinSqrtPlus z * motzkinSqrtOneSub z

/-- The explicit analytic branch of `M(z / 3)`. -/
def motzkinRescaledFun (z : ℂ) : ℂ :=
  2 / motzkinRescaledDenominator z

/-- The centered explicit branch, with the regular value at `z = 1` removed. -/
def motzkinCenteredRescaledFun (z : ℂ) : ℂ :=
  motzkinRescaledFun z - 3

def motzkinSingularityQuotientModel (z : ℂ) : ℂ :=
  (((-1 + 3 * motzkinSqrtThreeℂ * motzkinSqrtPlus z) * motzkinSqrtOneSub z) +
      (3 * motzkinSqrtThreeℂ * (1 - z / 3) - 3 * motzkinSqrtPlus z)) /
    motzkinRescaledDenominator z

lemma Complex_cpow_half_sq (z : ℂ) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  rw [show (1 / 2 : ℂ) = (2⁻¹ : ℂ) by norm_num]
  exact Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)

lemma motzkinSqrtOneSub_sq (z : ℂ) : motzkinSqrtOneSub z ^ 2 = 1 - z := by
  rw [motzkinSqrtOneSub, Complex_cpow_half_sq]

lemma motzkinSqrtOneSub_ne_zero_of_ne_one {z : ℂ} (hz : z ≠ 1) :
    motzkinSqrtOneSub z ≠ 0 := by
  intro ht0
  have hsq := congrArg (fun w : ℂ => w ^ 2) ht0
  change motzkinSqrtOneSub z ^ 2 = 0 ^ 2 at hsq
  rw [motzkinSqrtOneSub_sq] at hsq
  norm_num at hsq
  exact hz (sub_eq_zero.mp hsq).symm

lemma motzkinRescaledDenominator_ne_zero (z : ℂ) :
    motzkinRescaledDenominator z ≠ 0 := by
  intro h
  have hmul :
      (1 + z / 3) ^ (1 / 2 : ℂ) * (1 - z) ^ (1 / 2 : ℂ) = z / 3 - 1 := by
    have h' := h
    unfold motzkinRescaledDenominator motzkinSqrtPlus motzkinSqrtOneSub at h'
    linear_combination h'
  have hsq := congrArg (fun w : ℂ => w ^ 2) hmul
  change (((1 + z / 3) ^ (1 / 2 : ℂ) * (1 - z) ^ (1 / 2 : ℂ)) ^ 2 =
    (z / 3 - 1) ^ 2) at hsq
  rw [mul_pow, Complex_cpow_half_sq, Complex_cpow_half_sq] at hsq
  have hz2 : z ^ 2 = 0 := by
    linear_combination (-9 / 4 : ℂ) * hsq
  have hz : z = 0 := eq_zero_of_pow_eq_zero hz2
  subst z
  norm_num [motzkinRescaledDenominator, motzkinSqrtPlus, motzkinSqrtOneSub] at h

lemma motzkinRescaledFun_quadratic (z : ℂ) :
    motzkinRescaledFun z =
      1 + (z / 3) * motzkinRescaledFun z +
        ((z / 3) * motzkinRescaledFun z) ^ 2 := by
  unfold motzkinRescaledFun
  field_simp [motzkinRescaledDenominator_ne_zero z]
  unfold motzkinRescaledDenominator motzkinSqrtPlus motzkinSqrtOneSub
  ring_nf
  rw [Complex_cpow_half_sq, Complex_cpow_half_sq]
  ring_nf

lemma one_add_div_three_mem_slitPlane_of_norm_lt_three {z : ℂ} (hz : ‖z‖ < 3) :
    1 + z / 3 ∈ Complex.slitPlane := by
  refine Or.inl ?_
  have hdiv : ‖z / 3‖ < 1 := by
    rw [norm_div]
    norm_num at hz ⊢
    linarith
  have hge : -(‖z / 3‖) ≤ (z / 3).re := by
    exact (abs_le.mp (Complex.abs_re_le_norm (z / 3))).1
  have hre : -1 < (z / 3).re := by linarith
  change 0 < (1 + z / 3).re
  rw [Complex.add_re, Complex.one_re]
  linarith

lemma analyticOnNhd_motzkin_sqrt_plus :
    AnalyticOnNhd ℂ motzkinSqrtPlus
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hbase : AnalyticOnNhd ℂ (fun z : ℂ => 1 + z / 3)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    exact analyticOnNhd_const.add analyticOnNhd_id.div_const
  convert hbase.cpow analyticOnNhd_const (fun z hz => by
    apply one_add_div_three_mem_slitPlane_of_norm_lt_three
    have hzR : ‖z‖ < (3 / 2 : ℝ) := hz.1
    nlinarith) using 1

lemma analyticOnNhd_motzkin_sqrt_one_sub :
    AnalyticOnNhd ℂ motzkinSqrtOneSub
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have h := analyticOnNhd_one_sub_cpow_deltaDomain (α := (-1 / 2 : ℂ))
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4) (by positivity) (by nlinarith [Real.pi_pos])
  convert h using 1
  ext z
  norm_num [motzkinSqrtOneSub]

lemma analyticOnNhd_motzkinRescaledDenominator :
    AnalyticOnNhd ℂ motzkinRescaledDenominator
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hlinear : AnalyticOnNhd ℂ (fun z : ℂ => 1 - z / 3)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    exact analyticOnNhd_const.sub analyticOnNhd_id.div_const
  convert hlinear.add
    (analyticOnNhd_motzkin_sqrt_plus.mul analyticOnNhd_motzkin_sqrt_one_sub) using 1

lemma analyticOnNhd_motzkinRescaledFun :
    AnalyticOnNhd ℂ motzkinRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [motzkinRescaledFun] using
    (analyticOnNhd_const.div analyticOnNhd_motzkinRescaledDenominator
      (fun z _hz => motzkinRescaledDenominator_ne_zero z))

lemma analyticOnNhd_motzkinCenteredRescaledFun :
    AnalyticOnNhd ℂ motzkinCenteredRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [motzkinCenteredRescaledFun] using
    analyticOnNhd_motzkinRescaledFun.sub analyticOnNhd_const

lemma motzkin_singularity_quotient_eq {z : ℂ} (hz : z ≠ 1) :
    (motzkinCenteredRescaledFun z -
        motzkinSingularCoeff * motzkinSqrtOneSub z) / motzkinSqrtOneSub z =
      motzkinSingularityQuotientModel z := by
  have ht : motzkinSqrtOneSub z ≠ 0 := motzkinSqrtOneSub_ne_zero_of_ne_one hz
  unfold motzkinSingularityQuotientModel motzkinCenteredRescaledFun motzkinRescaledFun
    motzkinSingularCoeff motzkinSqrtThreeℂ
  field_simp [ht, motzkinRescaledDenominator_ne_zero z]
  unfold motzkinRescaledDenominator motzkinSqrtPlus motzkinSqrtOneSub
  ring_nf
  rw [Complex_cpow_half_sq]
  norm_num [Complex.ofReal_mul]
  ring_nf

lemma Real_sqrt_four_thirds :
    Real.sqrt (4 / 3 : ℝ) = 2 / Real.sqrt 3 := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4) (3 : ℝ)]
  norm_num [Real.sqrt_eq_rpow]

lemma Complex_cpow_four_thirds_half :
    (((4 / 3 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = ((2 / Real.sqrt 3 : ℝ) : ℂ) := by
  convert (show (((4 / 3 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) =
      ((2 / Real.sqrt 3 : ℝ) : ℂ) by
    rw [← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 4 / 3) (1 / 2 : ℝ)]
    congr
    rw [← Real.sqrt_eq_rpow]
    exact Real_sqrt_four_thirds) using 2
  norm_num

lemma tendsto_motzkinSqrtOneSub :
    Tendsto motzkinSqrtOneSub
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

lemma tendsto_motzkinSqrtPlus :
    Tendsto motzkinSqrtPlus
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ))
      (𝓝 ((2 / Real.sqrt 3 : ℝ) : ℂ)) := by
  have hb : Tendsto (fun z : ℂ => 1 + z / 3)
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ))
      (𝓝 (((4 / 3 : ℝ) : ℂ))) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 + z / 3) 1 := by fun_prop
    convert Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds using 1
    norm_num
  have hcpow0 : ContinuousAt (fun x : ℂ => x ^ (1 / 2 : ℂ))
      (((4 / 3 : ℝ) : ℂ)) :=
    continuousAt_cpow_const
      (Complex.ofReal_mem_slitPlane.2 (by norm_num : (0 : ℝ) < 4 / 3))
  have hcpow := hcpow0.tendsto.comp hb
  rw [Complex_cpow_four_thirds_half] at hcpow
  exact hcpow

lemma tendsto_motzkinRescaledDenominator :
    Tendsto motzkinRescaledDenominator
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 (2 / 3 : ℂ)) := by
  have hlinear : Tendsto (fun z : ℂ => 1 - z / 3)
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 (2 / 3 : ℂ)) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 - z / 3) 1 := by fun_prop
    convert Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds using 1
    norm_num
  have hprod := tendsto_motzkinSqrtPlus.mul tendsto_motzkinSqrtOneSub
  convert hlinear.add hprod using 1
  simp

lemma motzkin_sqrt_constant_cancel :
    3 * motzkinSqrtThreeℂ * (2 / 3 : ℂ) -
        3 * (((2 / Real.sqrt 3 : ℝ) : ℂ)) = 0 := by
  unfold motzkinSqrtThreeℂ
  have hs3r : (Real.sqrt 3 : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)
  have hs3c : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hs3r
  rw [Complex.ofReal_div]
  field_simp [hs3c]
  norm_num [Complex.ofReal_mul, Complex.ofReal_inv]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

lemma tendsto_motzkinSingularityQuotientModel :
    Tendsto motzkinSingularityQuotientModel
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hlinear : Tendsto (fun z : ℂ => 1 - z / 3) l (𝓝 (2 / 3 : ℂ)) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 - z / 3) 1 := by fun_prop
    convert Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds using 1
    norm_num
  have hcoef : Tendsto
      (fun z : ℂ => -1 + 3 * motzkinSqrtThreeℂ * motzkinSqrtPlus z) l
      (𝓝 (-1 + 3 * motzkinSqrtThreeℂ * (((2 / Real.sqrt 3 : ℝ) : ℂ)))) := by
    have hcont : ContinuousAt
        (fun w : ℂ => -1 + 3 * motzkinSqrtThreeℂ * w)
        (((2 / Real.sqrt 3 : ℝ) : ℂ)) := by fun_prop
    exact hcont.tendsto.comp tendsto_motzkinSqrtPlus
  have hterm1 : Tendsto
      (fun z : ℂ =>
        (-1 + 3 * motzkinSqrtThreeℂ * motzkinSqrtPlus z) * motzkinSqrtOneSub z) l
      (𝓝 0) := by
    convert hcoef.mul tendsto_motzkinSqrtOneSub using 1
    simp
  have hleft : Tendsto (fun z : ℂ => 3 * motzkinSqrtThreeℂ * (1 - z / 3)) l
      (𝓝 (3 * motzkinSqrtThreeℂ * (2 / 3 : ℂ))) := by
    have hcont : ContinuousAt (fun w : ℂ => 3 * motzkinSqrtThreeℂ * w) (2 / 3 : ℂ) := by
      fun_prop
    exact hcont.tendsto.comp hlinear
  have hright : Tendsto (fun z : ℂ => 3 * motzkinSqrtPlus z) l
      (𝓝 (3 * (((2 / Real.sqrt 3 : ℝ) : ℂ)))) := by
    have hcont : ContinuousAt (fun w : ℂ => 3 * w) (((2 / Real.sqrt 3 : ℝ) : ℂ)) := by
      fun_prop
    exact hcont.tendsto.comp tendsto_motzkinSqrtPlus
  have hterm2 : Tendsto
      (fun z : ℂ => 3 * motzkinSqrtThreeℂ * (1 - z / 3) - 3 * motzkinSqrtPlus z) l
      (𝓝 0) := by
    have h := hleft.sub hright
    rwa [motzkin_sqrt_constant_cancel] at h
  have hnum : Tendsto
      (fun z : ℂ =>
        ((-1 + 3 * motzkinSqrtThreeℂ * motzkinSqrtPlus z) * motzkinSqrtOneSub z) +
          (3 * motzkinSqrtThreeℂ * (1 - z / 3) - 3 * motzkinSqrtPlus z)) l
      (𝓝 0) := by
    convert hterm1.add hterm2 using 1
    simp
  have hquot := hnum.div tendsto_motzkinRescaledDenominator (by norm_num : (2 / 3 : ℂ) ≠ 0)
  convert hquot using 1
  ext z
  simp

lemma tendsto_motzkinCenteredRescaledFun_singularity :
    Tendsto
      (fun z : ℂ =>
        ‖motzkinCenteredRescaledFun z - motzkinSingularCoeff * motzkinSqrtOneSub z‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hevq :
      (fun z : ℂ =>
        (motzkinCenteredRescaledFun z -
          motzkinSingularCoeff * motzkinSqrtOneSub z) / motzkinSqrtOneSub z)
        =ᶠ[l] motzkinSingularityQuotientModel := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact motzkin_singularity_quotient_eq hz.2.1
  have hquot : Tendsto
      (fun z : ℂ =>
        (motzkinCenteredRescaledFun z -
          motzkinSingularCoeff * motzkinSqrtOneSub z) / motzkinSqrtOneSub z)
      l (𝓝 0) :=
    tendsto_motzkinSingularityQuotientModel.congr' hevq.symm
  have hnorm : Tendsto
      (fun z : ℂ =>
        ‖(motzkinCenteredRescaledFun z -
          motzkinSingularCoeff * motzkinSqrtOneSub z) / motzkinSqrtOneSub z‖)
      l (𝓝 0) := by
    simpa using hquot.norm
  have heq :
      (fun z : ℂ =>
        ‖motzkinCenteredRescaledFun z - motzkinSingularCoeff * motzkinSqrtOneSub z‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
        =ᶠ[l]
      (fun z : ℂ =>
        ‖(motzkinCenteredRescaledFun z -
          motzkinSingularCoeff * motzkinSqrtOneSub z) / motzkinSqrtOneSub z‖) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz_ne : z ≠ 1 := hz.2.1
    have ht : motzkinSqrtOneSub z ≠ 0 := motzkinSqrtOneSub_ne_zero_of_ne_one hz_ne
    have hu_pos : 0 < ‖(1 : ℂ) - z‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz_ne))
    have hnormT : ‖motzkinSqrtOneSub z‖ = ‖(1 : ℂ) - z‖ ^ (1 / 2 : ℝ) := by
      unfold motzkinSqrtOneSub
      convert Complex.norm_cpow_real ((1 : ℂ) - z) (1 / 2 : ℝ) using 1
      norm_num
    calc
      ‖motzkinCenteredRescaledFun z - motzkinSingularCoeff * motzkinSqrtOneSub z‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ))
          = ‖motzkinCenteredRescaledFun z - motzkinSingularCoeff * motzkinSqrtOneSub z‖ /
              ‖(1 : ℂ) - z‖ ^ (1 / 2 : ℝ) := by
            rw [Real.rpow_neg hu_pos.le]
            rfl
      _ = ‖motzkinCenteredRescaledFun z - motzkinSingularCoeff * motzkinSqrtOneSub z‖ /
              ‖motzkinSqrtOneSub z‖ := by rw [hnormT]
      _ = ‖(motzkinCenteredRescaledFun z -
              motzkinSingularCoeff * motzkinSqrtOneSub z) / motzkinSqrtOneSub z‖ := by
            rw [norm_div]
  exact hnorm.congr' heq.symm

/-- The rescaled Motzkin series with its regular constant term at the dominant
singularity subtracted.  This is the series to which the square-root transfer is
applied. -/
def motzkinCenteredRescaledSeriesℂ : PowerSeries ℂ :=
  motzkinRescaledSeriesℂ - PowerSeries.C (3 : ℂ)

lemma coeff_motzkinCenteredRescaledSeriesℂ_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff (R := ℂ) n motzkinCenteredRescaledSeriesℂ =
      PowerSeries.coeff (R := ℂ) n motzkinRescaledSeriesℂ := by
  simp [motzkinCenteredRescaledSeriesℂ, PowerSeries.coeff_C, hn]

def powerSeriesOfFMLSℂ (p : FormalMultilinearSeries ℂ ℂ ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => p.coeff n

lemma toFMLS_powerSeriesOfFMLSℂ (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    PowerSeries.toFMLS (powerSeriesOfFMLSℂ p) = p := by
  ext n
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
      (PowerSeries.toFMLS (powerSeriesOfFMLSℂ p)) n,
    ← FormalMultilinearSeries.mkPiRing_coeff_eq p n]
  simp [powerSeriesOfFMLSℂ]

lemma PowerSeries_toFMLS_injective :
    Function.Injective (PowerSeries.toFMLS :
      PowerSeries ℂ → FormalMultilinearSeries ℂ ℂ ℂ) := by
  intro f g h
  ext n
  have hcoeff := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) h
  simpa using hcoeff

lemma toFMLS_add (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f + g) = PowerSeries.toFMLS f + PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma toFMLS_sub (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f - g) = PowerSeries.toFMLS f - PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma toFMLS_C (c : ℂ) :
    PowerSeries.toFMLS (PowerSeries.C c) =
      constFormalMultilinearSeries ℂ ℂ c := by
  ext n
  cases n <;>
    simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
      constFormalMultilinearSeries]

lemma hasFPowerSeriesAt_const_toFMLS_C (c : ℂ) :
    HasFPowerSeriesAt (fun _ : ℂ => c)
      (PowerSeries.toFMLS (PowerSeries.C c)) (0 : ℂ) := by
  simpa [toFMLS_C] using
    (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
      (c := c) (e := (0 : ℂ)))

lemma hasFPowerSeriesAt_id_toFMLS_X :
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

lemma hasFPowerSeriesAt_mul_toFMLS {f g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hf : HasFPowerSeriesAt f (PowerSeries.toFMLS F) (0 : ℂ))
    (hg : HasFPowerSeriesAt g (PowerSeries.toFMLS G) (0 : ℂ)) :
    HasFPowerSeriesAt (fun z : ℂ => f z * g z)
      (PowerSeries.toFMLS (F * G)) (0 : ℂ) := by
  rcases hf with ⟨rf, hrf⟩
  rcases hg with ⟨rg, hrg⟩
  rw [hasFPowerSeriesAt_iff]
  refine eventually_of_mem
    (Metric.eball_mem_nhds (0 : ℂ) (lt_min hrf.r_pos hrg.r_pos)) ?_
  intro z hz
  have hzf : z ∈ Metric.eball (0 : ℂ) rf := by
    exact Metric.mem_eball.mpr
      (lt_of_lt_of_le (Metric.mem_eball.mp hz) (min_le_left _ _))
  have hzg : z ∈ Metric.eball (0 : ℂ) rg := by
    exact Metric.mem_eball.mpr
      (lt_of_lt_of_le (Metric.mem_eball.mp hz) (min_le_right _ _))
  let a : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n F
  let b : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n G
  have hsumf : HasSum a (f z) := by
    have h := hrf.hasSum hzf
    simpa [a, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hsumg : HasSum b (g z) := by
    have h := hrg.hasSum hzg
    simpa [b, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hzfrad : z ∈ Metric.eball (0 : ℂ) (PowerSeries.toFMLS F).radius :=
    Metric.eball_subset_eball hrf.r_le hzf
  have hzgrad : z ∈ Metric.eball (0 : ℂ) (PowerSeries.toFMLS G).radius :=
    Metric.eball_subset_eball hrg.r_le hzg
  have hnormf : Summable fun n : ℕ => ‖a n‖ := by
    simpa [a, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (PowerSeries.toFMLS F).summable_norm_apply hzfrad
  have hnormg : Summable fun n : ℕ => ‖b n‖ := by
    simpa [b, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (PowerSeries.toFMLS G).summable_norm_apply hzgrad
  let cseq : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n (F * G)
  let d : ℕ → ℂ := fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2
  have hcd : ∀ n, cseq n = d n := by
    intro n
    change z ^ n * PowerSeries.coeff (R := ℂ) n (F * G) =
      ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro kl hkl
    have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
    simp [a, b]
    rw [← hsum, pow_add]
    ring
  have hnormd : Summable fun n : ℕ => ‖d n‖ := by
    simpa [d] using summable_norm_sum_mul_antidiagonal_of_summable_norm hnormf hnormg
  have hnormc : Summable fun n : ℕ => ‖cseq n‖ := by
    exact hnormd.congr (fun n => by rw [hcd n])
  have hsumc : Summable cseq := hnormc.of_norm
  have htsum : (∑' n : ℕ, cseq n) = f z * g z := by
    have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnormf hnormg
    rw [hsumf.tsum_eq, hsumg.tsum_eq] at hprod
    rw [tsum_congr hcd, ← hprod]
  have hmain : HasSum cseq (f z * g z) := hsumc.hasSum_iff.mpr htsum
  simpa [cseq, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using hmain

lemma coeff_motzkinScaleX_mul_zero (P : PowerSeries ℂ) :
    PowerSeries.coeff (R := ℂ) 0 (motzkinScaleX * P) = 0 := by
  simp [motzkinScaleX]

lemma coeff_motzkinScaleX_mul_succ (P : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1) (motzkinScaleX * P) =
      (3 : ℂ)⁻¹ * PowerSeries.coeff (R := ℂ) n P := by
  rw [motzkinScaleX, mul_assoc, PowerSeries.coeff_C_mul]
  simp

lemma coeff_motzkinScaleX_mul_sq_succ_congr {P Q : PowerSeries ℂ} {n : ℕ}
    (h : ∀ k < n, PowerSeries.coeff (R := ℂ) k P =
      PowerSeries.coeff (R := ℂ) k Q) :
    PowerSeries.coeff (R := ℂ) (n + 1) ((motzkinScaleX * P) ^ 2) =
      PowerSeries.coeff (R := ℂ) (n + 1) ((motzkinScaleX * Q) ^ 2) := by
  rw [pow_two, pow_two, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hsum : kl.1 + kl.2 = n + 1 := Finset.mem_antidiagonal.mp hkl
  by_cases h1 : kl.1 = 0
  · simp [h1, coeff_motzkinScaleX_mul_zero]
  by_cases h2 : kl.2 = 0
  · simp [h2, coeff_motzkinScaleX_mul_zero]
  obtain ⟨i, hi_eq⟩ := Nat.exists_eq_succ_of_ne_zero h1
  obtain ⟨j, hj_eq⟩ := Nat.exists_eq_succ_of_ne_zero h2
  cases kl with
  | mk k l =>
      simp only at hi_eq hj_eq hsum ⊢
      subst k
      subst l
      have hi : i < n := by omega
      have hj : j < n := by omega
      simp [coeff_motzkinScaleX_mul_succ, h i hi, h j hj]

lemma motzkin_quadratic_solution_unique {P Q : PowerSeries ℂ}
    (hP : P = 1 + motzkinScaleX * P + (motzkinScaleX * P) ^ 2)
    (hQ : Q = 1 + motzkinScaleX * Q + (motzkinScaleX * Q) ^ 2) :
    P = Q := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          have hp := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) 0 S) hP
          have hq := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) 0 S) hQ
          simp [motzkinScaleX] at hp hq
          simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, hq]
      | succ n =>
          have hp := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) (n + 1) S) hP
          have hq := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) (n + 1) S) hQ
          simp only [map_add] at hp hq
          rw [hp, hq]
          congr 1
          · rw [coeff_motzkinScaleX_mul_succ, coeff_motzkinScaleX_mul_succ,
              ih n (Nat.lt_succ_self n)]
          · exact coeff_motzkinScaleX_mul_sq_succ_congr
              (fun k hk => ih k (Nat.lt_trans hk (Nat.lt_succ_self n)))

theorem motzkinRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt motzkinRescaledFun
      (PowerSeries.toFMLS motzkinRescaledSeriesℂ) (0 : ℂ) := by
  have han : AnalyticAt ℂ motzkinRescaledFun (0 : ℂ) :=
    analyticOnNhd_motzkinRescaledFun 0
      (zero_mem_deltaDomainArg (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
        (by norm_num) (by nlinarith [Real.pi_pos]))
  rcases han with ⟨p, hp⟩
  let P : PowerSeries ℂ := powerSeriesOfFMLSℂ p
  have hPto : PowerSeries.toFMLS P = p := by
    simpa [P] using toFMLS_powerSeriesOfFMLSℂ p
  have hpP : HasFPowerSeriesAt motzkinRescaledFun
      (PowerSeries.toFMLS P) (0 : ℂ) := by
    simpa [hPto] using hp
  have hconstScale : HasFPowerSeriesAt (fun _ : ℂ => ((3 : ℂ)⁻¹))
      (PowerSeries.toFMLS (PowerSeries.C ((3 : ℂ)⁻¹))) (0 : ℂ) :=
    hasFPowerSeriesAt_const_toFMLS_C ((3 : ℂ)⁻¹)
  have hscale0 := hasFPowerSeriesAt_mul_toFMLS hconstScale
    hasFPowerSeriesAt_id_toFMLS_X
  have hscale : HasFPowerSeriesAt (fun z : ℂ => z / 3)
      (PowerSeries.toFMLS motzkinScaleX) (0 : ℂ) := by
    refine hscale0.congr (Eventually.of_forall ?_)
    intro z
    ring
  have hscaleF := hasFPowerSeriesAt_mul_toFMLS hscale hpP
  have hsquare := hasFPowerSeriesAt_mul_toFMLS hscaleF hscaleF
  have hconstOne : HasFPowerSeriesAt (fun _ : ℂ => (1 : ℂ))
      (PowerSeries.toFMLS (1 : PowerSeries ℂ)) (0 : ℂ) := by
    simpa using hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hrhs0 := (hconstOne.add hscaleF).add hsquare
  have hrhs : HasFPowerSeriesAt
      (fun z : ℂ =>
        1 + (z / 3) * motzkinRescaledFun z +
          ((z / 3) * motzkinRescaledFun z) ^ 2)
      (PowerSeries.toFMLS
        (1 + motzkinScaleX * P + (motzkinScaleX * P) ^ 2)) (0 : ℂ) := by
    simpa [toFMLS_add, pow_two, add_assoc] using hrhs0
  have hFMLS :
      PowerSeries.toFMLS P =
        PowerSeries.toFMLS
          (1 + motzkinScaleX * P + (motzkinScaleX * P) ^ 2) :=
    hpP.eq_formalMultilinearSeries_of_eventually hrhs
      (Eventually.of_forall fun z => motzkinRescaledFun_quadratic z)
  have hPquad :
      P = 1 + motzkinScaleX * P + (motzkinScaleX * P) ^ 2 :=
    PowerSeries_toFMLS_injective hFMLS
  have hP_eq : P = motzkinRescaledSeriesℂ :=
    motzkin_quadratic_solution_unique hPquad motzkinRescaledSeriesℂ_quadratic
  simpa [hP_eq] using hpP

theorem motzkinCenteredRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt motzkinCenteredRescaledFun
      (PowerSeries.toFMLS motzkinCenteredRescaledSeriesℂ) (0 : ℂ) := by
  have hsub := motzkinRescaledFun_hasFPowerSeriesAt_zero.sub
    (hasFPowerSeriesAt_const_toFMLS_C (3 : ℂ))
  simpa [motzkinCenteredRescaledFun, motzkinCenteredRescaledSeriesℂ, toFMLS_sub] using hsub

/-- The real transfer constant in the form `K * 3^n * n^(-3/2)`. -/
def motzkinAsymptoticConstant : ℝ :=
  3 * Real.sqrt 3 / (2 * Real.sqrt Real.pi)

lemma neg_half_not_neg_nat : ∀ m : ℕ, (-1 / 2 : ℂ) ≠ -m := by
  intro m hm
  have hr := congrArg Complex.re hm
  norm_num at hr
  cases m with
  | zero =>
      norm_num at hr
  | succ m =>
      have hmge : (1 : ℝ) ≤ (m + 1 : ℕ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      linarith

lemma Complex_Gamma_neg_half :
    Complex.Gamma (-1 / 2 : ℂ) = -2 * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  have h := Complex.Gamma_add_one (-1 / 2 : ℂ) (by norm_num)
  have hhalf : (-1 / 2 : ℂ) + 1 = 1 / 2 := by norm_num
  have hsqrt : ((Real.sqrt Real.pi : ℝ) : ℂ) =
      (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa using Complex.ofReal_cpow Real.pi_nonneg (1 / 2 : ℝ)
  rw [hhalf, Complex.Gamma_one_half_eq, ← hsqrt] at h
  calc
    Complex.Gamma (-1 / 2 : ℂ)
        = (-2 : ℂ) * ((-1 / 2 : ℂ) * Complex.Gamma (-1 / 2 : ℂ)) := by ring
    _ = -2 * ((Real.sqrt Real.pi : ℝ) : ℂ) := by rw [← h]

lemma motzkin_transfer_constant_complex :
    motzkinSingularCoeff / Complex.Gamma (-1 / 2 : ℂ) =
      ((motzkinAsymptoticConstant : ℝ) : ℂ) := by
  rw [motzkinSingularCoeff, motzkinAsymptoticConstant, Complex_Gamma_neg_half]
  have hsqrtπ_ne : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hleft :
      -((3 * Real.sqrt 3 : ℝ) : ℂ) /
          (-2 * ((Real.sqrt Real.pi : ℝ) : ℂ)) =
        (((-(3 * Real.sqrt 3)) / (-(2 * Real.sqrt Real.pi)) : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg]
  rw [hleft]
  congr 1
  ring_nf

lemma motzkin_rescale_back (n : ℕ) :
    ((motzkin n : ℂ) * ((3 : ℂ)⁻¹) ^ n) * (3 : ℂ) ^ n =
      (motzkin n : ℂ) := by
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ h3, one_pow, mul_one]

lemma motzkin_rescale_back_eventuallyEq :
    (fun n : ℕ =>
        ((motzkin n : ℂ) * ((3 : ℂ)⁻¹) ^ n) * (3 : ℂ) ^ n) =ᶠ[atTop]
      (fun n : ℕ => (motzkin n : ℂ)) := by
  exact Eventually.of_forall motzkin_rescale_back

lemma transfer_target_to_motzkin_complex_eventuallyEq :
    (fun n : ℕ =>
        (motzkinSingularCoeff * (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) /
            Complex.Gamma (-1 / 2 : ℂ)) *
          (3 : ℂ) ^ n) =ᶠ[atTop]
      (fun n : ℕ =>
        ((motzkinAsymptoticConstant * (3 : ℝ) ^ n *
            (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  refine (eventually_ne_atTop 0).mono ?_
  intro n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hcpow :
      (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) =
        (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
    have hnnonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    have h := (Complex.ofReal_cpow hnnonneg (-(3 / 2 : ℝ))).symm
    norm_num at h ⊢
    exact h
  calc
    (motzkinSingularCoeff * (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) /
          Complex.Gamma (-1 / 2 : ℂ)) * (3 : ℂ) ^ n
        = (motzkinSingularCoeff / Complex.Gamma (-1 / 2 : ℂ)) *
            (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) * (3 : ℂ) ^ n := by ring
    _ = (motzkinAsymptoticConstant : ℂ) *
            (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((3 : ℝ) ^ n : ℂ) := by
          rw [motzkin_transfer_constant_complex, hcpow]
          norm_num [Complex.ofReal_pow]
    _ = ((motzkinAsymptoticConstant * (3 : ℝ) ^ n *
            (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
          norm_num [Complex.ofReal_mul, Complex.ofReal_pow]
          ring

/--
Coefficient asymptotic from the corrected singularity-analysis hypotheses for
the centered rescaled Motzkin OGF.  The constant term `3` at `z = 1` has already
been subtracted, so the transfer theorem sees a function tending to `0` with
leading term `motzkinSingularCoeff * (1 - z)^(1/2)`.
-/
theorem motzkin_isEquivalent_complex_of_centered_rescaled_transfer
    {R φ : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f (PowerSeries.toFMLS motzkinCenteredRescaledSeriesℂ) 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖f z - motzkinSingularCoeff * (1 - z) ^ (1 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => (motzkin n : ℂ)) ~[atTop]
    (fun n : ℕ =>
        ((motzkinAsymptoticConstant * (3 : ℝ) ^ n *
            (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have hsing_transfer : Tendsto
      (fun z : ℂ =>
        ‖f z - motzkinSingularCoeff * (1 - z) ^ (-(-1 / 2 : ℂ))‖ *
          ‖(1 : ℂ) - z‖ ^ ((-1 / 2 : ℂ).re))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    convert hsing using 1
    ext z
    norm_num
  have htransfer :=
    transfer_theorem (α := (-1 / 2 : ℂ)) (C := motzkinSingularCoeff)
      (R := R) (φ := φ) (f := f) (p := PowerSeries.toFMLS motzkinCenteredRescaledSeriesℂ)
      neg_half_not_neg_nat (by norm_num [motzkinSingularCoeff]) hR hφ0 hφ2 hp hΔ
      hsing_transfer
  · have hmul :
        (fun n : ℕ =>
          (PowerSeries.toFMLS motzkinCenteredRescaledSeriesℂ).coeff n * (3 : ℂ) ^ n)
          ~[atTop]
        (fun n : ℕ =>
          (motzkinSingularCoeff * (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) /
              Complex.Gamma (-1 / 2 : ℂ)) *
            (3 : ℂ) ^ n) := by
        simpa only [Pi.mul_apply] using
          htransfer.mul
            (Asymptotics.IsEquivalent.refl (l := atTop) (u := fun n : ℕ => (3 : ℂ) ^ n))
    have hcoeff :
        (fun n : ℕ =>
          (PowerSeries.toFMLS motzkinCenteredRescaledSeriesℂ).coeff n * (3 : ℂ) ^ n) =ᶠ[atTop]
          (fun n : ℕ => (motzkin n : ℂ)) := by
      refine (eventually_ne_atTop 0).mono ?_
      intro n hn
      change (PowerSeries.toFMLS motzkinCenteredRescaledSeriesℂ).coeff n * (3 : ℂ) ^ n =
        (motzkin n : ℂ)
      rw [PowerSeries.coeff_toFMLS, coeff_motzkinCenteredRescaledSeriesℂ_of_ne_zero hn,
        coeff_motzkinRescaledSeriesℂ]
      exact motzkin_rescale_back n
    exact hcoeff.symm.trans_isEquivalent
      (hmul.trans_eventuallyEq transfer_target_to_motzkin_complex_eventuallyEq)

/-- Real-valued form of `motzkin_isEquivalent_complex_of_centered_rescaled_transfer`. -/
theorem motzkin_isEquivalent_real_of_centered_rescaled_transfer
    {R φ : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f (PowerSeries.toFMLS motzkinCenteredRescaledSeriesℂ) 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖f z - motzkinSingularCoeff * (1 - z) ^ (1 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => (motzkin n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        motzkinAsymptoticConstant * (3 : ℝ) ^ n *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  rw [← ofReal_isEquivalent_iff]
  exact motzkin_isEquivalent_complex_of_centered_rescaled_transfer hR hφ0 hφ2 hp hΔ hsing

theorem motzkin_isEquivalent_of_centered_explicit_hasFPowerSeries
    (hp : HasFPowerSeriesAt motzkinCenteredRescaledFun
      (PowerSeries.toFMLS motzkinCenteredRescaledSeriesℂ) 0) :
    (fun n : ℕ => (motzkin n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        motzkinAsymptoticConstant * (3 : ℝ) ^ n *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  refine motzkin_isEquivalent_real_of_centered_rescaled_transfer
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (f := motzkinCenteredRescaledFun) ?_ ?_ ?_ hp
    analyticOnNhd_motzkinCenteredRescaledFun ?_
  · norm_num
  · positivity
  · nlinarith [Real.pi_pos]
  · simpa [motzkinSqrtOneSub] using tendsto_motzkinCenteredRescaledFun_singularity

theorem motzkin_isEquivalent :
    (fun n : ℕ => (motzkin n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        motzkinAsymptoticConstant * (3 : ℝ) ^ n *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
  motzkin_isEquivalent_of_centered_explicit_hasFPowerSeries
    motzkinCenteredRescaledFun_hasFPowerSeriesAt_zero
