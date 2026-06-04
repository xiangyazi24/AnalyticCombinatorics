import Mathlib
import AnalyticCombinatorics.Ch7.SingularityApp.Motzkin
import AnalyticCombinatorics.Ch4.Analytic.TransferGeneral
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics

/-!
# Large Schroeder-number asymptotic

This file proves the square-root singularity asymptotic for the large
Schroeder numbers with OGF
`S(z) = (1 - z - sqrt (1 - 6 z + z^2)) / (2 z)`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

/-- Large Schroeder numbers, with `S 0 = 1` and
`S (n + 1) = S n + sum_{k = 0}^n S k * S (n - k)`. -/
def schroeder : ℕ → ℕ
  | 0 => 1
  | n + 1 => schroeder n + ∑ k : Fin (n + 1), schroeder k * schroeder (n - k)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_self n
  · exact k.2
  · exact Nat.lt_succ_of_le (Nat.sub_le n k)

@[simp] lemma schroeder_zero : schroeder 0 = 1 := by
  simp [schroeder]

@[simp] lemma schroeder_succ (n : ℕ) :
    schroeder (n + 1) =
      schroeder n + ∑ k : Fin (n + 1), schroeder k * schroeder (n - k) := by
  simp [schroeder]

lemma schroeder_one : schroeder 1 = 2 := by
  norm_num [schroeder_succ]

/-- Dominant singularity, the smaller root of `1 - 6 z + z^2`. -/
def schroederRho : ℝ := 3 - 2 * Real.sqrt 2

/-- Exponential growth base, the reciprocal of `schroederRho`. -/
def schroederGrowthBase : ℝ := 3 + 2 * Real.sqrt 2

lemma schroeder_rho_mul_growthBase :
    schroederRho * schroederGrowthBase = 1 := by
  rw [schroederRho, schroederGrowthBase]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma schroederGrowthBase_pos : 0 < schroederGrowthBase := by
  rw [schroederGrowthBase]
  positivity

lemma schroederGrowthBase_gt_one : 1 < schroederGrowthBase := by
  rw [schroederGrowthBase]
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

lemma schroederRho_pos : 0 < schroederRho := by
  have hmul := schroeder_rho_mul_growthBase
  have hg := schroederGrowthBase_pos
  nlinarith

lemma schroederRho_ne_zero : schroederRho ≠ 0 :=
  ne_of_gt schroederRho_pos

lemma schroederRho_inv : schroederRho⁻¹ = schroederGrowthBase := by
  have hmul := schroeder_rho_mul_growthBase
  have hρ : schroederRho ≠ 0 := schroederRho_ne_zero
  calc
    schroederRho⁻¹ = schroederRho⁻¹ * (schroederRho * schroederGrowthBase) := by
      rw [hmul, mul_one]
    _ = schroederGrowthBase := by
      rw [← mul_assoc, inv_mul_cancel₀ hρ, one_mul]

lemma schroederRho_lt_one : schroederRho < 1 := by
  have hmul := schroeder_rho_mul_growthBase
  have hg := schroederGrowthBase_gt_one
  have hρpos := schroederRho_pos
  nlinarith

lemma schroederRho_nonneg : 0 ≤ schroederRho :=
  le_of_lt schroederRho_pos

lemma schroederRho_lt_growthBase : schroederRho < schroederGrowthBase := by
  have hρ := schroederRho_lt_one
  have hg := schroederGrowthBase_gt_one
  linarith

lemma one_sub_schroederRho_pos : 0 < 1 - schroederRho := by
  linarith [schroederRho_lt_one]

lemma one_sub_schroederRho_ne_zero : (1 - schroederRho : ℝ) ≠ 0 :=
  ne_of_gt one_sub_schroederRho_pos

lemma one_sub_schroederRho_ne_zeroℂ :
    (((1 - schroederRho : ℝ) : ℂ)) ≠ 0 := by
  exact_mod_cast one_sub_schroederRho_ne_zero

lemma one_sub_schroederRho_sq :
    (1 - schroederRho) ^ 2 = 4 * schroederRho := by
  rw [schroederRho]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

lemma schroederRho_quadratic :
    1 - 6 * schroederRho + schroederRho ^ 2 = 0 := by
  rw [schroederRho]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

lemma one_sub_schroederRho_sq_pos : 0 < 1 - schroederRho ^ 2 := by
  nlinarith [schroederRho_pos, schroederRho_lt_one]

lemma one_sub_schroederRho_sq_nonneg : 0 ≤ 1 - schroederRho ^ 2 :=
  le_of_lt one_sub_schroederRho_sq_pos

lemma schroederRho_sq_mul_three_halves_lt_one :
    schroederRho ^ 2 * (3 / 2 : ℝ) < 1 := by
  have hρpos := schroederRho_pos
  have hρlt : schroederRho < 1 / 2 := by
    rw [schroederRho]
    have hsqrt_gt : (5 / 4 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 4)]
      norm_num
    nlinarith
  nlinarith

lemma schroeder_rho_over_growthBase :
    schroederRho / schroederGrowthBase = schroederRho ^ 2 := by
  rw [← schroederRho_inv]
  field_simp [schroederRho_ne_zero]

/-- The ordinary generating function as a formal power series over `ℂ`. -/
def schroederSeriesℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n => (schroeder n : ℂ)

@[simp] lemma coeff_schroederSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n schroederSeriesℂ = (schroeder n : ℂ) := by
  simp [schroederSeriesℂ]

@[simp] lemma constantCoeff_schroederSeriesℂ :
    PowerSeries.constantCoeff schroederSeriesℂ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

lemma coeff_X_mul_schroederSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1) (PowerSeries.X * schroederSeriesℂ) =
      (schroeder n : ℂ) := by
  simp

lemma coeff_schroederSeriesℂ_sq (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (schroederSeriesℂ ^ 2) =
      ∑ k : Fin (n + 1), (schroeder k : ℂ) * (schroeder (n - k) : ℂ) := by
  rw [pow_two, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => PowerSeries.coeff (R := ℂ) x schroederSeriesℂ *
      PowerSeries.coeff (R := ℂ) y schroederSeriesℂ) n]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro x hx
  have hxle : x ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  simp [hxle]

lemma coeff_X_mul_schroederSeriesℂ_sq (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1)
        (PowerSeries.X * schroederSeriesℂ ^ 2) =
      ∑ k : Fin (n + 1), (schroeder k : ℂ) * (schroeder (n - k) : ℂ) := by
  rw [← coeff_schroederSeriesℂ_sq n]
  simp

/-- The Schroeder OGF satisfies `S = 1 + X S + X S^2`. -/
theorem schroederSeriesℂ_eq_one_add_X_mul_add_X_mul_sq :
    schroederSeriesℂ =
      1 + PowerSeries.X * schroederSeriesℂ +
        PowerSeries.X * schroederSeriesℂ ^ 2 := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      simp only [coeff_schroederSeriesℂ, map_add, PowerSeries.coeff_one, Nat.succ_ne_zero,
        ↓reduceIte, zero_add]
      rw [coeff_X_mul_schroederSeriesℂ, coeff_X_mul_schroederSeriesℂ_sq]
      norm_num [schroeder_succ]

/-- The rescaled series `S(rho z)`. -/
def schroederRescaledSeriesℂ : PowerSeries ℂ :=
  PowerSeries.rescale ((schroederRho : ℝ) : ℂ) schroederSeriesℂ

@[simp] lemma coeff_schroederRescaledSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n schroederRescaledSeriesℂ =
      (schroeder n : ℂ) * (((schroederRho : ℝ) : ℂ)) ^ n := by
  simp [schroederRescaledSeriesℂ, PowerSeries.coeff_rescale, mul_comm]

/-- The formal substitution variable `rho z`. -/
def schroederScaleX : PowerSeries ℂ :=
  PowerSeries.C (((schroederRho : ℝ) : ℂ)) * PowerSeries.X

lemma schroederRescaledSeriesℂ_quadratic :
    schroederRescaledSeriesℂ =
      1 + schroederScaleX * schroederRescaledSeriesℂ +
        schroederScaleX * schroederRescaledSeriesℂ ^ 2 := by
  change PowerSeries.rescale (((schroederRho : ℝ) : ℂ)) schroederSeriesℂ =
    1 + schroederScaleX * schroederRescaledSeriesℂ +
      schroederScaleX * schroederRescaledSeriesℂ ^ 2
  rw [schroederSeriesℂ_eq_one_add_X_mul_add_X_mul_sq]
  simp only [map_add, map_mul, map_one, map_pow, PowerSeries.rescale_X]
  simp [schroederRescaledSeriesℂ, schroederScaleX, pow_two, mul_assoc]

def schroederRhoℂ : ℂ := ((schroederRho : ℝ) : ℂ)

def schroederOneSubRhoℂ : ℂ := (((1 - schroederRho : ℝ) : ℂ))

def schroederSqrtRegularAtOneℂ : ℂ :=
  ((Real.sqrt (1 - schroederRho ^ 2) : ℝ) : ℂ)

/-- The singular coefficient of `S(rho z)` at `z = 1`. -/
def schroederSingularCoeff : ℂ :=
  -2 * schroederSqrtRegularAtOneℂ / schroederOneSubRhoℂ ^ 2

def schroederSqrtRegular (z : ℂ) : ℂ :=
  (1 - schroederRhoℂ ^ 2 * z) ^ (1 / 2 : ℂ)

def schroederSqrtOneSub (z : ℂ) : ℂ :=
  (1 - z) ^ (1 / 2 : ℂ)

/-- Denominator of the explicit rescaled Schroeder OGF. -/
def schroederRescaledDenominator (z : ℂ) : ℂ :=
  1 - schroederRhoℂ * z + schroederSqrtRegular z * schroederSqrtOneSub z

/-- The explicit analytic branch of `S(rho z)`. -/
def schroederRescaledFun (z : ℂ) : ℂ :=
  2 / schroederRescaledDenominator z

def schroederRegularValueℂ : ℂ :=
  2 / schroederOneSubRhoℂ

/-- The centered explicit branch, with the regular value at `z = 1` removed. -/
def schroederCenteredRescaledFun (z : ℂ) : ℂ :=
  schroederRescaledFun z - schroederRegularValueℂ

def schroederSingularityQuotientModel (z : ℂ) : ℂ :=
  -(2 * (schroederRhoℂ * schroederSqrtOneSub z + schroederSqrtRegular z)) /
      (schroederOneSubRhoℂ * schroederRescaledDenominator z) -
    schroederSingularCoeff

lemma schroederSqrtOneSub_sq (z : ℂ) : schroederSqrtOneSub z ^ 2 = 1 - z := by
  rw [schroederSqrtOneSub, Complex_cpow_half_sq]

lemma schroederSqrtOneSub_ne_zero_of_ne_one {z : ℂ} (hz : z ≠ 1) :
    schroederSqrtOneSub z ≠ 0 := by
  intro ht0
  have hsq := congrArg (fun w : ℂ => w ^ 2) ht0
  change schroederSqrtOneSub z ^ 2 = 0 ^ 2 at hsq
  rw [schroederSqrtOneSub_sq] at hsq
  norm_num at hsq
  exact hz (sub_eq_zero.mp hsq).symm

lemma schroederSqrtRegular_sq (z : ℂ) :
    schroederSqrtRegular z ^ 2 = 1 - schroederRhoℂ ^ 2 * z := by
  rw [schroederSqrtRegular, Complex_cpow_half_sq]

lemma schroeder_one_sub_rho_sq_complex :
    (1 - schroederRhoℂ) ^ 2 = 4 * schroederRhoℂ := by
  unfold schroederRhoℂ
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
  exact_mod_cast one_sub_schroederRho_sq

lemma schroederRescaledDenominator_ne_zero (z : ℂ) :
    schroederRescaledDenominator z ≠ 0 := by
  intro h
  have hmul :
      schroederSqrtRegular z * schroederSqrtOneSub z =
        schroederRhoℂ * z - 1 := by
    have h' := h
    unfold schroederRescaledDenominator at h'
    linear_combination h'
  have hsq := congrArg (fun w : ℂ => w ^ 2) hmul
  change (schroederSqrtRegular z * schroederSqrtOneSub z) ^ 2 =
    (schroederRhoℂ * z - 1) ^ 2 at hsq
  rw [mul_pow, schroederSqrtRegular_sq, schroederSqrtOneSub_sq] at hsq
  have hzprod : (1 - schroederRhoℂ) ^ 2 * z = 0 := by
    calc
      (1 - schroederRhoℂ) ^ 2 * z =
          (schroederRhoℂ * z - 1) ^ 2 -
            (1 - schroederRhoℂ ^ 2 * z) * (1 - z) := by ring
      _ = 0 := by
        rw [← hsq]
        ring
  have hone : (1 - schroederRhoℂ) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro hzero
    have hreal : (1 - schroederRho : ℝ) = 0 := by
      apply Complex.ofReal_injective
      simpa [schroederRhoℂ, Complex.ofReal_sub] using hzero
    exact one_sub_schroederRho_ne_zero hreal
  have hz : z = 0 := by
    exact eq_zero_of_ne_zero_of_mul_left_eq_zero hone hzprod
  subst z
  norm_num [schroederRescaledDenominator, schroederSqrtRegular, schroederSqrtOneSub,
    schroederRhoℂ] at h

lemma schroederRescaledFun_quadratic (z : ℂ) :
    schroederRescaledFun z =
      1 + (schroederRhoℂ * z) * schroederRescaledFun z +
        (schroederRhoℂ * z) * schroederRescaledFun z ^ 2 := by
  unfold schroederRescaledFun
  field_simp [schroederRescaledDenominator_ne_zero z]
  unfold schroederRescaledDenominator schroederSqrtRegular schroederSqrtOneSub
  ring_nf
  rw [Complex_cpow_half_sq, Complex_cpow_half_sq]
  have hsq := schroeder_one_sub_rho_sq_complex
  ring_nf at hsq ⊢
  linear_combination z * hsq

lemma one_sub_rho_sq_mul_mem_slitPlane_of_norm_lt_three_halves {z : ℂ}
    (hz : ‖z‖ < (3 / 2 : ℝ)) :
    1 - schroederRhoℂ ^ 2 * z ∈ Complex.slitPlane := by
  refine Or.inl ?_
  let w : ℂ := schroederRhoℂ ^ 2 * z
  have hnormρ : ‖schroederRhoℂ ^ 2‖ = schroederRho ^ 2 := by
    rw [norm_pow, schroederRhoℂ]
    simp [Real.norm_of_nonneg schroederRho_nonneg]
  have hw_norm : ‖w‖ < 1 := by
    have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
    have hρsq_nonneg : 0 ≤ schroederRho ^ 2 := sq_nonneg schroederRho
    change ‖schroederRhoℂ ^ 2 * z‖ < 1
    rw [norm_mul, hnormρ]
    nlinarith [hz, schroederRho_sq_mul_three_halves_lt_one]
  have hre_le : w.re ≤ ‖w‖ := (abs_le.mp (Complex.abs_re_le_norm w)).2
  change 0 < (1 - schroederRhoℂ ^ 2 * z).re
  rw [show schroederRhoℂ ^ 2 * z = w by rfl, Complex.sub_re, Complex.one_re]
  linarith

lemma analyticOnNhd_schroeder_sqrt_regular :
    AnalyticOnNhd ℂ schroederSqrtRegular
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hbase : AnalyticOnNhd ℂ (fun z : ℂ => 1 - schroederRhoℂ ^ 2 * z)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    exact analyticOnNhd_const.sub (analyticOnNhd_const.mul analyticOnNhd_id)
  convert hbase.cpow analyticOnNhd_const (fun z hz => by
    exact one_sub_rho_sq_mul_mem_slitPlane_of_norm_lt_three_halves hz.1) using 1

lemma analyticOnNhd_schroeder_sqrt_one_sub :
    AnalyticOnNhd ℂ schroederSqrtOneSub
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [schroederSqrtOneSub, motzkinSqrtOneSub] using
    analyticOnNhd_motzkin_sqrt_one_sub

lemma analyticOnNhd_schroederRescaledDenominator :
    AnalyticOnNhd ℂ schroederRescaledDenominator
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hlinear : AnalyticOnNhd ℂ (fun z : ℂ => 1 - schroederRhoℂ * z)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    exact analyticOnNhd_const.sub (analyticOnNhd_const.mul analyticOnNhd_id)
  convert hlinear.add
    (analyticOnNhd_schroeder_sqrt_regular.mul analyticOnNhd_schroeder_sqrt_one_sub) using 1

lemma analyticOnNhd_schroederRescaledFun :
    AnalyticOnNhd ℂ schroederRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [schroederRescaledFun] using
    (analyticOnNhd_const.div analyticOnNhd_schroederRescaledDenominator
      (fun z _hz => schroederRescaledDenominator_ne_zero z))

lemma analyticOnNhd_schroederCenteredRescaledFun :
    AnalyticOnNhd ℂ schroederCenteredRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [schroederCenteredRescaledFun] using
    analyticOnNhd_schroederRescaledFun.sub analyticOnNhd_const

lemma Complex_cpow_one_sub_schroederRho_sq_half :
    (((1 - schroederRho ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
      schroederSqrtRegularAtOneℂ := by
  unfold schroederSqrtRegularAtOneℂ
  convert (show (((1 - schroederRho ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) =
      ((Real.sqrt (1 - schroederRho ^ 2) : ℝ) : ℂ) by
    rw [← Complex.ofReal_cpow one_sub_schroederRho_sq_nonneg (1 / 2 : ℝ)]
    congr
    rw [← Real.sqrt_eq_rpow]) using 2
  norm_num

lemma tendsto_schroederSqrtOneSub :
    Tendsto schroederSqrtOneSub
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  simpa [schroederSqrtOneSub, motzkinSqrtOneSub] using tendsto_motzkinSqrtOneSub

lemma tendsto_schroederSqrtRegular :
    Tendsto schroederSqrtRegular
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ))
      (𝓝 schroederSqrtRegularAtOneℂ) := by
  have hb : Tendsto (fun z : ℂ => 1 - schroederRhoℂ ^ 2 * z)
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ))
      (𝓝 (((1 - schroederRho ^ 2 : ℝ) : ℂ))) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 - schroederRhoℂ ^ 2 * z) 1 := by
      fun_prop
    convert Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds using 1
    simp [schroederRhoℂ, Complex.ofReal_sub, Complex.ofReal_pow]
  have hcpow0 : ContinuousAt (fun x : ℂ => x ^ (1 / 2 : ℂ))
      (((1 - schroederRho ^ 2 : ℝ) : ℂ)) :=
    continuousAt_cpow_const
      (Complex.ofReal_mem_slitPlane.2 one_sub_schroederRho_sq_pos)
  have hcpow := hcpow0.tendsto.comp hb
  rwa [Complex_cpow_one_sub_schroederRho_sq_half] at hcpow

lemma tendsto_schroederRescaledDenominator :
    Tendsto schroederRescaledDenominator
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ))
      (𝓝 schroederOneSubRhoℂ) := by
  have hlinear : Tendsto (fun z : ℂ => 1 - schroederRhoℂ * z)
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ))
      (𝓝 schroederOneSubRhoℂ) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 - schroederRhoℂ * z) 1 := by
      fun_prop
    convert Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds using 1
    simp [schroederOneSubRhoℂ, schroederRhoℂ, Complex.ofReal_sub]
  have hprod := tendsto_schroederSqrtRegular.mul tendsto_schroederSqrtOneSub
  convert hlinear.add hprod using 1
  simp

lemma tendsto_schroederSingularityQuotientModel :
    Tendsto schroederSingularityQuotientModel
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hnum0 : Tendsto
      (fun z : ℂ => schroederRhoℂ * schroederSqrtOneSub z + schroederSqrtRegular z)
      l (𝓝 schroederSqrtRegularAtOneℂ) := by
    have hleft : Tendsto (fun z : ℂ => schroederRhoℂ * schroederSqrtOneSub z)
        l (𝓝 0) := by
      convert tendsto_const_nhds.mul tendsto_schroederSqrtOneSub using 1
      simp
    convert hleft.add tendsto_schroederSqrtRegular using 1
    simp
  have hden0 : Tendsto
      (fun z : ℂ => schroederOneSubRhoℂ * schroederRescaledDenominator z)
      l (𝓝 (schroederOneSubRhoℂ ^ 2)) := by
    convert tendsto_const_nhds.mul tendsto_schroederRescaledDenominator using 1
    ring
  have hden_ne : schroederOneSubRhoℂ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 one_sub_schroederRho_ne_zeroℂ
  have hquot : Tendsto
      (fun z : ℂ =>
        -(2 * (schroederRhoℂ * schroederSqrtOneSub z + schroederSqrtRegular z)) /
          (schroederOneSubRhoℂ * schroederRescaledDenominator z))
      l (𝓝 schroederSingularCoeff) := by
    have hconst : Tendsto (fun _ : ℂ => (-2 : ℂ)) l (𝓝 (-2 : ℂ)) :=
      tendsto_const_nhds
    have h := (hconst.mul hnum0).div hden0 hden_ne
    simpa [schroederSingularCoeff] using h
  have hsub : Tendsto
      (fun z : ℂ =>
        -(2 * (schroederRhoℂ * schroederSqrtOneSub z + schroederSqrtRegular z)) /
            (schroederOneSubRhoℂ * schroederRescaledDenominator z) -
          schroederSingularCoeff)
      l (𝓝 (schroederSingularCoeff - schroederSingularCoeff)) :=
    hquot.sub tendsto_const_nhds
  simpa [schroederSingularityQuotientModel] using hsub

lemma schroeder_singularity_quotient_eq {z : ℂ} (hz : z ≠ 1) :
    (schroederCenteredRescaledFun z -
        schroederSingularCoeff * schroederSqrtOneSub z) / schroederSqrtOneSub z =
      schroederSingularityQuotientModel z := by
  have ht : schroederSqrtOneSub z ≠ 0 := schroederSqrtOneSub_ne_zero_of_ne_one hz
  unfold schroederSingularityQuotientModel schroederCenteredRescaledFun schroederRescaledFun
    schroederRegularValueℂ
  field_simp [ht, schroederRescaledDenominator_ne_zero z, one_sub_schroederRho_ne_zeroℂ]
  unfold schroederRescaledDenominator schroederOneSubRhoℂ schroederRhoℂ
  have ha : (1 - ((schroederRho : ℝ) : ℂ)) ≠ 0 := by
    simpa [Complex.ofReal_sub] using one_sub_schroederRho_ne_zeroℂ
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  ring_nf
  rw [schroederSqrtOneSub_sq]
  field_simp [ha]
  ring

lemma tendsto_schroederCenteredRescaledFun_singularity :
    Tendsto
      (fun z : ℂ =>
        ‖schroederCenteredRescaledFun z - schroederSingularCoeff * schroederSqrtOneSub z‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hevq :
      (fun z : ℂ =>
        (schroederCenteredRescaledFun z -
          schroederSingularCoeff * schroederSqrtOneSub z) / schroederSqrtOneSub z)
        =ᶠ[l] schroederSingularityQuotientModel := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact schroeder_singularity_quotient_eq hz.2.1
  have hquot : Tendsto
      (fun z : ℂ =>
        (schroederCenteredRescaledFun z -
          schroederSingularCoeff * schroederSqrtOneSub z) / schroederSqrtOneSub z)
      l (𝓝 0) :=
    tendsto_schroederSingularityQuotientModel.congr' hevq.symm
  have hnorm : Tendsto
      (fun z : ℂ =>
        ‖(schroederCenteredRescaledFun z -
          schroederSingularCoeff * schroederSqrtOneSub z) / schroederSqrtOneSub z‖)
      l (𝓝 0) := by
    simpa using hquot.norm
  have heq :
      (fun z : ℂ =>
        ‖schroederCenteredRescaledFun z - schroederSingularCoeff * schroederSqrtOneSub z‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
        =ᶠ[l]
      (fun z : ℂ =>
        ‖(schroederCenteredRescaledFun z -
          schroederSingularCoeff * schroederSqrtOneSub z) / schroederSqrtOneSub z‖) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz_ne : z ≠ 1 := hz.2.1
    have ht : schroederSqrtOneSub z ≠ 0 := schroederSqrtOneSub_ne_zero_of_ne_one hz_ne
    have hu_pos : 0 < ‖(1 : ℂ) - z‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz_ne))
    have hnormT : ‖schroederSqrtOneSub z‖ = ‖(1 : ℂ) - z‖ ^ (1 / 2 : ℝ) := by
      unfold schroederSqrtOneSub
      convert Complex.norm_cpow_real ((1 : ℂ) - z) (1 / 2 : ℝ) using 1
      norm_num
    calc
      ‖schroederCenteredRescaledFun z - schroederSingularCoeff * schroederSqrtOneSub z‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ))
          = ‖schroederCenteredRescaledFun z - schroederSingularCoeff * schroederSqrtOneSub z‖ /
              ‖(1 : ℂ) - z‖ ^ (1 / 2 : ℝ) := by
            rw [Real.rpow_neg hu_pos.le]
            rfl
      _ = ‖schroederCenteredRescaledFun z - schroederSingularCoeff * schroederSqrtOneSub z‖ /
              ‖schroederSqrtOneSub z‖ := by rw [hnormT]
      _ = ‖(schroederCenteredRescaledFun z -
              schroederSingularCoeff * schroederSqrtOneSub z) / schroederSqrtOneSub z‖ := by
            rw [norm_div]
  exact hnorm.congr' heq.symm

/-- The rescaled Schroeder series with its regular constant term at the dominant
singularity subtracted. -/
def schroederCenteredRescaledSeriesℂ : PowerSeries ℂ :=
  schroederRescaledSeriesℂ - PowerSeries.C schroederRegularValueℂ

lemma coeff_schroederCenteredRescaledSeriesℂ_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff (R := ℂ) n schroederCenteredRescaledSeriesℂ =
      PowerSeries.coeff (R := ℂ) n schroederRescaledSeriesℂ := by
  simp [schroederCenteredRescaledSeriesℂ, PowerSeries.coeff_C, hn]

lemma coeff_schroederScaleX_mul_zero (P : PowerSeries ℂ) :
    PowerSeries.coeff (R := ℂ) 0 (schroederScaleX * P) = 0 := by
  simp [schroederScaleX]

lemma coeff_schroederScaleX_mul_succ (P : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1) (schroederScaleX * P) =
      schroederRhoℂ * PowerSeries.coeff (R := ℂ) n P := by
  rw [schroederScaleX, schroederRhoℂ, mul_assoc, PowerSeries.coeff_C_mul]
  simp

lemma coeff_schroederScaleX_mul_sq_succ_congr {P Q : PowerSeries ℂ} {n : ℕ}
    (h : ∀ k ≤ n, PowerSeries.coeff (R := ℂ) k P =
      PowerSeries.coeff (R := ℂ) k Q) :
    PowerSeries.coeff (R := ℂ) (n + 1) (schroederScaleX * P ^ 2) =
      PowerSeries.coeff (R := ℂ) (n + 1) (schroederScaleX * Q ^ 2) := by
  rw [coeff_schroederScaleX_mul_succ, coeff_schroederScaleX_mul_succ]
  congr 1
  rw [pow_two, pow_two, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
  have h1 : kl.1 ≤ n := by omega
  have h2 : kl.2 ≤ n := by omega
  simp [h kl.1 h1, h kl.2 h2]

lemma schroeder_quadratic_solution_unique {P Q : PowerSeries ℂ}
    (hP : P = 1 + schroederScaleX * P + schroederScaleX * P ^ 2)
    (hQ : Q = 1 + schroederScaleX * Q + schroederScaleX * Q ^ 2) :
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
          simp [schroederScaleX] at hp hq
          simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, hq]
      | succ n =>
          have hp := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) (n + 1) S) hP
          have hq := congrArg (fun S : PowerSeries ℂ =>
            PowerSeries.coeff (R := ℂ) (n + 1) S) hQ
          simp only [map_add] at hp hq
          rw [hp, hq]
          congr 1
          · rw [coeff_schroederScaleX_mul_succ, coeff_schroederScaleX_mul_succ,
              ih n (Nat.lt_succ_self n)]
          · exact coeff_schroederScaleX_mul_sq_succ_congr
              (fun k hk => ih k (Nat.lt_succ_of_le hk))

theorem schroederRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt schroederRescaledFun
      (PowerSeries.toFMLS schroederRescaledSeriesℂ) (0 : ℂ) := by
  have han : AnalyticAt ℂ schroederRescaledFun (0 : ℂ) :=
    analyticOnNhd_schroederRescaledFun 0
      (zero_mem_deltaDomainArg (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
        (by norm_num) (by nlinarith [Real.pi_pos]))
  rcases han with ⟨p, hp⟩
  let P : PowerSeries ℂ := powerSeriesOfFMLSℂ p
  have hPto : PowerSeries.toFMLS P = p := by
    simpa [P] using toFMLS_powerSeriesOfFMLSℂ p
  have hpP : HasFPowerSeriesAt schroederRescaledFun
      (PowerSeries.toFMLS P) (0 : ℂ) := by
    simpa [hPto] using hp
  have hconstScale : HasFPowerSeriesAt (fun _ : ℂ => schroederRhoℂ)
      (PowerSeries.toFMLS (PowerSeries.C schroederRhoℂ)) (0 : ℂ) :=
    hasFPowerSeriesAt_const_toFMLS_C schroederRhoℂ
  have hscale0 := hasFPowerSeriesAt_mul_toFMLS hconstScale
    hasFPowerSeriesAt_id_toFMLS_X
  have hscale : HasFPowerSeriesAt (fun z : ℂ => schroederRhoℂ * z)
      (PowerSeries.toFMLS schroederScaleX) (0 : ℂ) := by
    refine hscale0.congr (Eventually.of_forall ?_)
    intro z
    ring
  have hscaleF := hasFPowerSeriesAt_mul_toFMLS hscale hpP
  have hsquare := hasFPowerSeriesAt_mul_toFMLS hpP hpP
  have hscaleSquare := hasFPowerSeriesAt_mul_toFMLS hscale hsquare
  have hconstOne : HasFPowerSeriesAt (fun _ : ℂ => (1 : ℂ))
      (PowerSeries.toFMLS (1 : PowerSeries ℂ)) (0 : ℂ) := by
    simpa using hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hrhs0 := (hconstOne.add hscaleF).add hscaleSquare
  have hrhs : HasFPowerSeriesAt
      (fun z : ℂ =>
        1 + (schroederRhoℂ * z) * schroederRescaledFun z +
          (schroederRhoℂ * z) * schroederRescaledFun z ^ 2)
      (PowerSeries.toFMLS
        (1 + schroederScaleX * P + schroederScaleX * P ^ 2)) (0 : ℂ) := by
    simpa [toFMLS_add, pow_two, add_assoc] using hrhs0
  have hFMLS :
      PowerSeries.toFMLS P =
        PowerSeries.toFMLS
          (1 + schroederScaleX * P + schroederScaleX * P ^ 2) :=
    hpP.eq_formalMultilinearSeries_of_eventually hrhs
      (Eventually.of_forall fun z => schroederRescaledFun_quadratic z)
  have hPquad :
      P = 1 + schroederScaleX * P + schroederScaleX * P ^ 2 :=
    PowerSeries_toFMLS_injective hFMLS
  have hP_eq : P = schroederRescaledSeriesℂ :=
    schroeder_quadratic_solution_unique hPquad schroederRescaledSeriesℂ_quadratic
  simpa [hP_eq] using hpP

theorem schroederCenteredRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt schroederCenteredRescaledFun
      (PowerSeries.toFMLS schroederCenteredRescaledSeriesℂ) (0 : ℂ) := by
  have hsub := schroederRescaledFun_hasFPowerSeriesAt_zero.sub
    (hasFPowerSeriesAt_const_toFMLS_C schroederRegularValueℂ)
  simpa [schroederCenteredRescaledFun, schroederCenteredRescaledSeriesℂ, toFMLS_sub] using hsub

/-- The real transfer constant in the form `C * rho⁻¹^n * n^(-3/2)`. -/
def schroederAsymptoticConstant : ℝ :=
  Real.sqrt (1 - schroederRho ^ 2) /
    ((1 - schroederRho) ^ 2 * Real.sqrt Real.pi)

lemma schroederAsymptoticConstant_complex :
    ((schroederAsymptoticConstant : ℝ) : ℂ) =
      schroederSqrtRegularAtOneℂ /
        (schroederOneSubRhoℂ ^ 2 * ((Real.sqrt Real.pi : ℝ) : ℂ)) := by
  rw [schroederAsymptoticConstant]
  unfold schroederSqrtRegularAtOneℂ schroederOneSubRhoℂ
  norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]

lemma schroeder_transfer_constant_complex :
    schroederSingularCoeff / Complex.Gamma (-1 / 2 : ℂ) =
      ((schroederAsymptoticConstant : ℝ) : ℂ) := by
  rw [schroederAsymptoticConstant_complex, schroederSingularCoeff, Complex_Gamma_neg_half]
  have hsqrtπ_ne : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hone_ne : schroederOneSubRhoℂ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 one_sub_schroederRho_ne_zeroℂ
  field_simp [hsqrtπ_ne, hone_ne]

lemma schroederAsymptoticConstant_eq_rho_form :
    schroederAsymptoticConstant =
      Real.sqrt (1 - schroederRho ^ 2) /
        (4 * schroederRho * Real.sqrt Real.pi) := by
  rw [schroederAsymptoticConstant, one_sub_schroederRho_sq]

lemma schroeder_rescale_back (n : ℕ) :
    ((schroeder n : ℂ) * schroederRhoℂ ^ n) * (schroederRhoℂ⁻¹) ^ n =
      (schroeder n : ℂ) := by
  have hρ : schroederRhoℂ ≠ 0 := by
    unfold schroederRhoℂ
    exact_mod_cast schroederRho_ne_zero
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hρ, one_pow, mul_one]

lemma transfer_target_to_schroeder_complex_eventuallyEq :
    (fun n : ℕ =>
        (schroederSingularCoeff * (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) /
            Complex.Gamma (-1 / 2 : ℂ)) *
          (schroederRhoℂ⁻¹) ^ n) =ᶠ[atTop]
      (fun n : ℕ =>
        ((schroederAsymptoticConstant * schroederRho⁻¹ ^ n *
            (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  refine (eventually_ne_atTop 0).mono ?_
  intro n hn
  have hcpow :
      (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) =
        (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
    have hnnonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    have h := (Complex.ofReal_cpow hnnonneg (-(3 / 2 : ℝ))).symm
    norm_num at h ⊢
    exact h
  have hρpow :
      (schroederRhoℂ⁻¹) ^ n = (((schroederRho⁻¹) ^ n : ℝ) : ℂ) := by
    unfold schroederRhoℂ
    rw [← Complex.ofReal_inv]
    rw [Complex.ofReal_pow]
  calc
    (schroederSingularCoeff * (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) /
          Complex.Gamma (-1 / 2 : ℂ)) * (schroederRhoℂ⁻¹) ^ n
        = (schroederSingularCoeff / Complex.Gamma (-1 / 2 : ℂ)) *
            (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) * (schroederRhoℂ⁻¹) ^ n := by ring
    _ = (schroederAsymptoticConstant : ℂ) *
            (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
            (((schroederRho⁻¹) ^ n : ℝ) : ℂ) := by
          rw [schroeder_transfer_constant_complex, hcpow, hρpow]
    _ = ((schroederAsymptoticConstant * schroederRho⁻¹ ^ n *
            (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
          norm_num [Complex.ofReal_mul, Complex.ofReal_pow]
          ring

/--
Coefficient asymptotic from the square-root transfer theorem for the centered
rescaled Schroeder OGF.
-/
theorem schroeder_isEquivalent_complex_of_centered_rescaled_transfer
    {R φ : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f (PowerSeries.toFMLS schroederCenteredRescaledSeriesℂ) 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖f z - schroederSingularCoeff * (1 - z) ^ (1 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => (schroeder n : ℂ)) ~[atTop]
    (fun n : ℕ =>
        ((schroederAsymptoticConstant * schroederRho⁻¹ ^ n *
            (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have hsing_transfer : Tendsto
      (fun z : ℂ =>
        ‖f z - schroederSingularCoeff * (1 - z) ^ (-(-1 / 2 : ℂ))‖ *
          ‖(1 : ℂ) - z‖ ^ ((-1 / 2 : ℂ).re))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    convert hsing using 1
    ext z
    norm_num
  have hC : schroederSingularCoeff ≠ 0 := by
    have hsqrt_ne : schroederSqrtRegularAtOneℂ ≠ 0 := by
      unfold schroederSqrtRegularAtOneℂ
      exact_mod_cast (Real.sqrt_ne_zero'.mpr one_sub_schroederRho_sq_pos)
    have hone_ne : schroederOneSubRhoℂ ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 one_sub_schroederRho_ne_zeroℂ
    rw [schroederSingularCoeff]
    exact div_ne_zero (mul_ne_zero (by norm_num) hsqrt_ne) hone_ne
  have htransfer :=
    transfer_theorem (α := (-1 / 2 : ℂ)) (C := schroederSingularCoeff)
      (R := R) (φ := φ) (f := f)
      (p := PowerSeries.toFMLS schroederCenteredRescaledSeriesℂ)
      neg_half_not_neg_nat hC hR hφ0 hφ2 hp hΔ hsing_transfer
  have hmul :
      (fun n : ℕ =>
        (PowerSeries.toFMLS schroederCenteredRescaledSeriesℂ).coeff n *
          (schroederRhoℂ⁻¹) ^ n)
        ~[atTop]
      (fun n : ℕ =>
        (schroederSingularCoeff * (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) /
            Complex.Gamma (-1 / 2 : ℂ)) *
          (schroederRhoℂ⁻¹) ^ n) := by
      simpa only [Pi.mul_apply] using
        htransfer.mul
          (Asymptotics.IsEquivalent.refl
            (l := atTop) (u := fun n : ℕ => (schroederRhoℂ⁻¹) ^ n))
  have hcoeff :
      (fun n : ℕ =>
        (PowerSeries.toFMLS schroederCenteredRescaledSeriesℂ).coeff n *
          (schroederRhoℂ⁻¹) ^ n) =ᶠ[atTop]
        (fun n : ℕ => (schroeder n : ℂ)) := by
    refine (eventually_ne_atTop 0).mono ?_
    intro n hn
    change (PowerSeries.toFMLS schroederCenteredRescaledSeriesℂ).coeff n *
        (schroederRhoℂ⁻¹) ^ n =
      (schroeder n : ℂ)
    rw [PowerSeries.coeff_toFMLS, coeff_schroederCenteredRescaledSeriesℂ_of_ne_zero hn,
      coeff_schroederRescaledSeriesℂ]
    exact schroeder_rescale_back n
  exact hcoeff.symm.trans_isEquivalent
    (hmul.trans_eventuallyEq transfer_target_to_schroeder_complex_eventuallyEq)

/-- Real-valued form of the Schroeder transfer theorem. -/
theorem schroeder_isEquivalent_real_of_centered_rescaled_transfer
    {R φ : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f (PowerSeries.toFMLS schroederCenteredRescaledSeriesℂ) 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖f z - schroederSingularCoeff * (1 - z) ^ (1 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => (schroeder n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        schroederAsymptoticConstant * schroederRho⁻¹ ^ n *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  rw [← ofReal_isEquivalent_iff]
  exact schroeder_isEquivalent_complex_of_centered_rescaled_transfer hR hφ0 hφ2 hp hΔ hsing

theorem schroeder_isEquivalent_of_centered_explicit_hasFPowerSeries
    (hp : HasFPowerSeriesAt schroederCenteredRescaledFun
      (PowerSeries.toFMLS schroederCenteredRescaledSeriesℂ) 0) :
    (fun n : ℕ => (schroeder n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        schroederAsymptoticConstant * schroederRho⁻¹ ^ n *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  refine schroeder_isEquivalent_real_of_centered_rescaled_transfer
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (f := schroederCenteredRescaledFun) ?_ ?_ ?_ hp
    analyticOnNhd_schroederCenteredRescaledFun ?_
  · norm_num
  · positivity
  · nlinarith [Real.pi_pos]
  · simpa [schroederSqrtOneSub] using tendsto_schroederCenteredRescaledFun_singularity

theorem schroeder_isEquivalent :
    (fun n : ℕ => (schroeder n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        schroederAsymptoticConstant * schroederRho⁻¹ ^ n *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
  schroeder_isEquivalent_of_centered_explicit_hasFPowerSeries
    schroederCenteredRescaledFun_hasFPowerSeriesAt_zero

def schroederAsymptoticRatio (n : ℕ) : Float :=
  (schroeder n).toFloat /
    (Float.sqrt (4.0 + 3.0 * Float.sqrt 2.0) / (2.0 * Float.sqrt 3.141592653589793) *
      (3.0 + 2.0 * Float.sqrt 2.0) ^ n.toFloat *
      n.toFloat ^ (-1.5))

#eval (schroeder 2, schroeder 3, schroeder 4, schroeder 5, schroeder 10)
#eval [2, 3, 4, 5, 10].map schroederAsymptoticRatio
