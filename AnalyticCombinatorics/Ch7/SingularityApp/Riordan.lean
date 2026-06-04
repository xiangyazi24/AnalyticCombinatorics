import Mathlib
import AnalyticCombinatorics.Ch7.SingularityApp.Motzkin
import AnalyticCombinatorics.Ch7.SingularityApp.Schroeder
import AnalyticCombinatorics.Ch4.Analytic.TransferGeneral
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics

/-!
# Riordan-number asymptotic

This file proves the square-root singularity asymptotic for the Riordan
numbers, using the first-return decomposition of Riordan paths:

`R(z) = 1 + z^2 M(z) R(z)`.

The explicit branch is

`R(z) = 2 / (1 + z + sqrt(1 - 2 z - 3 z^2))`.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

/-- Riordan numbers: Motzkin paths with no horizontal step at height zero.
The recurrence is the first-return decomposition
`R = 1 + z^2 M R`. -/
def riordan : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => ∑ k : Fin (n + 1), motzkin k * riordan (n - k)
termination_by n => n
decreasing_by omega

@[simp] lemma riordan_zero : riordan 0 = 1 := by
  simp [riordan]

@[simp] lemma riordan_one : riordan 1 = 0 := by
  simp [riordan]

@[simp] lemma riordan_succ_succ (n : ℕ) :
    riordan (n + 2) = ∑ k : Fin (n + 1), motzkin k * riordan (n - k) := by
  simp [riordan]

lemma riordan_two : riordan 2 = 1 := by
  norm_num [riordan_succ_succ]

/-- The ordinary generating function as a formal power series over `ℂ`. -/
def riordanSeriesℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n => (riordan n : ℂ)

@[simp] lemma coeff_riordanSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n riordanSeriesℂ = (riordan n : ℂ) := by
  simp [riordanSeriesℂ]

@[simp] lemma constantCoeff_riordanSeriesℂ :
    PowerSeries.constantCoeff riordanSeriesℂ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

lemma coeff_motzkinSeriesℂ_mul_riordanSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (motzkinSeriesℂ * riordanSeriesℂ) =
      ∑ k : Fin (n + 1), (motzkin k : ℂ) * (riordan (n - k) : ℂ) := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => PowerSeries.coeff (R := ℂ) x motzkinSeriesℂ *
      PowerSeries.coeff (R := ℂ) y riordanSeriesℂ) n]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro x hx
  have hxle : x ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  simp [hxle]

lemma coeff_X_sq_mul_motzkinSeriesℂ_mul_riordanSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 2)
        ((PowerSeries.X : PowerSeries ℂ) ^ 2 *
          (motzkinSeriesℂ * riordanSeriesℂ)) =
      ∑ k : Fin (n + 1), (motzkin k : ℂ) * (riordan (n - k) : ℂ) := by
  rw [PowerSeries.coeff_X_pow_mul (p := motzkinSeriesℂ * riordanSeriesℂ)
    (n := 2) (d := n)]
  exact coeff_motzkinSeriesℂ_mul_riordanSeriesℂ n

/-- The Riordan OGF satisfies the first-return equation `R = 1 + X^2 M R`. -/
theorem riordanSeriesℂ_eq_one_add_X_sq_mul_motzkin_mul :
    riordanSeriesℂ =
      1 + (PowerSeries.X : PowerSeries ℂ) ^ 2 *
        (motzkinSeriesℂ * riordanSeriesℂ) := by
  ext n
  cases n with
  | zero =>
      simp
  | succ n =>
      cases n with
      | zero =>
          simp [PowerSeries.coeff_X_pow_mul']
      | succ n =>
          simp only [coeff_riordanSeriesℂ, map_add, PowerSeries.coeff_one,
            Nat.succ_ne_zero, ↓reduceIte, zero_add]
          rw [coeff_X_sq_mul_motzkinSeriesℂ_mul_riordanSeriesℂ]
          norm_num [riordan_succ_succ]

/-- The rescaled series `R(z / 3)`. -/
def riordanRescaledSeriesℂ : PowerSeries ℂ :=
  PowerSeries.rescale ((3 : ℂ)⁻¹) riordanSeriesℂ

@[simp] lemma coeff_riordanRescaledSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n riordanRescaledSeriesℂ =
      (riordan n : ℂ) * ((3 : ℂ)⁻¹) ^ n := by
  simp [riordanRescaledSeriesℂ, PowerSeries.coeff_rescale, mul_comm]

/-- The formal substitution variable `z / 3`. -/
def riordanScaleX : PowerSeries ℂ :=
  PowerSeries.C ((3 : ℂ)⁻¹) * PowerSeries.X

lemma riordanRescaledSeriesℂ_functional :
    riordanRescaledSeriesℂ =
      1 + riordanScaleX ^ 2 *
        (motzkinRescaledSeriesℂ * riordanRescaledSeriesℂ) := by
  change PowerSeries.rescale ((3 : ℂ)⁻¹) riordanSeriesℂ =
    1 + riordanScaleX ^ 2 *
      (motzkinRescaledSeriesℂ * riordanRescaledSeriesℂ)
  rw [riordanSeriesℂ_eq_one_add_X_sq_mul_motzkin_mul]
  simp only [map_add, map_mul, map_one, map_pow, PowerSeries.rescale_X]
  simp [riordanRescaledSeriesℂ, motzkinRescaledSeriesℂ, riordanScaleX, pow_two, mul_assoc]

def riordanSqrtPlus (z : ℂ) : ℂ :=
  motzkinSqrtPlus z

def riordanSqrtOneSub (z : ℂ) : ℂ :=
  motzkinSqrtOneSub z

def riordanAℂ : ℂ := 4 / 3

def riordanSqrtPlusAtOneℂ : ℂ :=
  ((2 / Real.sqrt 3 : ℝ) : ℂ)

/-- The singular coefficient of `R(z / 3)` at `z = 1`. -/
def riordanSingularCoeff : ℂ :=
  -(((3 * Real.sqrt 3 / 4 : ℝ) : ℂ))

/-- Denominator of the explicit rescaled Riordan OGF. -/
def riordanRescaledDenominator (z : ℂ) : ℂ :=
  1 + z / 3 + riordanSqrtPlus z * riordanSqrtOneSub z

/-- The explicit analytic branch of `R(z / 3)`. -/
def riordanRescaledFun (z : ℂ) : ℂ :=
  2 / riordanRescaledDenominator z

def riordanRegularValueℂ : ℂ := 3 / 2

/-- The centered explicit branch, with the regular value at `z = 1` removed. -/
def riordanCenteredRescaledFun (z : ℂ) : ℂ :=
  riordanRescaledFun z - riordanRegularValueℂ

def riordanSingularityQuotientModel (z : ℂ) : ℂ :=
  ((2 / 3 : ℂ) * riordanSqrtOneSub z -
      2 * riordanSqrtPlus z -
      riordanSingularCoeff * riordanAℂ * (1 + z / 3) -
      riordanSingularCoeff * riordanAℂ * riordanSqrtPlus z * riordanSqrtOneSub z) /
    (riordanAℂ * riordanRescaledDenominator z)

lemma riordanSqrtOneSub_sq (z : ℂ) : riordanSqrtOneSub z ^ 2 = 1 - z := by
  simpa [riordanSqrtOneSub] using motzkinSqrtOneSub_sq z

lemma riordanSqrtOneSub_ne_zero_of_ne_one {z : ℂ} (hz : z ≠ 1) :
    riordanSqrtOneSub z ≠ 0 := by
  simpa [riordanSqrtOneSub] using motzkinSqrtOneSub_ne_zero_of_ne_one hz

lemma riordanSqrtPlus_sq (z : ℂ) : riordanSqrtPlus z ^ 2 = 1 + z / 3 := by
  simp [riordanSqrtPlus, motzkinSqrtPlus]

lemma riordanRescaledDenominator_ne_zero_of_norm_lt_three {z : ℂ}
    (hz : ‖z‖ < 3) :
    riordanRescaledDenominator z ≠ 0 := by
  intro h
  have hmul :
      riordanSqrtPlus z * riordanSqrtOneSub z = -(1 + z / 3) := by
    have h' := h
    unfold riordanRescaledDenominator at h'
    linear_combination h'
  have hsq := congrArg (fun w : ℂ => w ^ 2) hmul
  change (riordanSqrtPlus z * riordanSqrtOneSub z) ^ 2 =
    (-(1 + z / 3)) ^ 2 at hsq
  rw [mul_pow, riordanSqrtPlus_sq, riordanSqrtOneSub_sq] at hsq
  have hzprod : z * (1 + z / 3) = 0 := by
    linear_combination (-3 / 4 : ℂ) * hsq
  rcases mul_eq_zero.mp hzprod with hz0 | hfactor
  · subst z
    norm_num [riordanRescaledDenominator, riordanSqrtPlus, riordanSqrtOneSub,
      motzkinSqrtPlus, motzkinSqrtOneSub] at h
  · have hz_eq : z = -3 := by
      linear_combination 3 * hfactor
    have hnorm : ‖z‖ = 3 := by
      rw [hz_eq]
      norm_num
    nlinarith

lemma riordanRescaledDenominator_ne_zero_delta
    {z : ℂ} (hz : z ∈ DeltaDomainArg (3 / 2) (Real.pi / 4)) :
    riordanRescaledDenominator z ≠ 0 := by
  exact riordanRescaledDenominator_ne_zero_of_norm_lt_three (by nlinarith [hz.1])

lemma riordanRescaledFun_functional_of_norm_lt_three {z : ℂ} (hz : ‖z‖ < 3) :
    riordanRescaledFun z =
      1 + (z / 3) ^ 2 * motzkinRescaledFun z * riordanRescaledFun z := by
  unfold riordanRescaledFun motzkinRescaledFun
  field_simp [riordanRescaledDenominator_ne_zero_of_norm_lt_three hz,
    motzkinRescaledDenominator_ne_zero z]
  unfold riordanRescaledDenominator motzkinRescaledDenominator riordanSqrtPlus
    riordanSqrtOneSub motzkinSqrtPlus motzkinSqrtOneSub
  ring_nf
  rw [Complex_cpow_half_sq, Complex_cpow_half_sq]
  ring_nf

lemma analyticOnNhd_riordan_sqrt_plus :
    AnalyticOnNhd ℂ riordanSqrtPlus
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [riordanSqrtPlus] using analyticOnNhd_motzkin_sqrt_plus

lemma analyticOnNhd_riordan_sqrt_one_sub :
    AnalyticOnNhd ℂ riordanSqrtOneSub
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [riordanSqrtOneSub] using analyticOnNhd_motzkin_sqrt_one_sub

lemma analyticOnNhd_riordanRescaledDenominator :
    AnalyticOnNhd ℂ riordanRescaledDenominator
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  have hlinear : AnalyticOnNhd ℂ (fun z : ℂ => 1 + z / 3)
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
    exact analyticOnNhd_const.add analyticOnNhd_id.div_const
  convert hlinear.add
    (analyticOnNhd_riordan_sqrt_plus.mul analyticOnNhd_riordan_sqrt_one_sub) using 1

lemma analyticOnNhd_riordanRescaledFun :
    AnalyticOnNhd ℂ riordanRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [riordanRescaledFun] using
    (analyticOnNhd_const.div analyticOnNhd_riordanRescaledDenominator
      (fun z hz => riordanRescaledDenominator_ne_zero_delta hz))

lemma analyticOnNhd_riordanCenteredRescaledFun :
    AnalyticOnNhd ℂ riordanCenteredRescaledFun
      (DeltaDomainArg (3 / 2) (Real.pi / 4)) := by
  simpa [riordanCenteredRescaledFun] using
    analyticOnNhd_riordanRescaledFun.sub analyticOnNhd_const

lemma tendsto_riordanSqrtOneSub :
    Tendsto riordanSqrtOneSub
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  simpa [riordanSqrtOneSub] using tendsto_motzkinSqrtOneSub

lemma tendsto_riordanSqrtPlus :
    Tendsto riordanSqrtPlus
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ))
      (𝓝 riordanSqrtPlusAtOneℂ) := by
  simpa [riordanSqrtPlus, riordanSqrtPlusAtOneℂ] using tendsto_motzkinSqrtPlus

lemma tendsto_riordanRescaledDenominator :
    Tendsto riordanRescaledDenominator
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 riordanAℂ) := by
  have hlinear : Tendsto (fun z : ℂ => 1 + z / 3)
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 riordanAℂ) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 + z / 3) 1 := by fun_prop
    convert Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds using 1
    norm_num [riordanAℂ]
  have hprod := tendsto_riordanSqrtPlus.mul tendsto_riordanSqrtOneSub
  convert hlinear.add hprod using 1
  simp

lemma riordan_sqrt_constant_cancel :
    -2 * riordanSqrtPlusAtOneℂ -
        riordanSingularCoeff * riordanAℂ * riordanAℂ = 0 := by
  unfold riordanSqrtPlusAtOneℂ riordanSingularCoeff riordanAℂ
  have hs3r : (Real.sqrt 3 : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)
  have hs3c : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hs3r
  rw [Complex.ofReal_div]
  field_simp [hs3c]
  norm_num [Complex.ofReal_mul, Complex.ofReal_inv]
  ring_nf
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

lemma tendsto_riordanSingularityQuotientModel :
    Tendsto riordanSingularityQuotientModel
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hlinear : Tendsto (fun z : ℂ => 1 + z / 3) l (𝓝 riordanAℂ) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 + z / 3) 1 := by fun_prop
    convert Tendsto.mono_left hcont.tendsto nhdsWithin_le_nhds using 1
    norm_num [riordanAℂ]
  have hterm1 : Tendsto (fun z : ℂ => (2 / 3 : ℂ) * riordanSqrtOneSub z) l
      (𝓝 0) := by
    convert tendsto_const_nhds.mul tendsto_riordanSqrtOneSub using 1
    simp
  have hterm2 : Tendsto
      (fun z : ℂ =>
        -2 * riordanSqrtPlus z -
          riordanSingularCoeff * riordanAℂ * (1 + z / 3)) l
      (𝓝 0) := by
    have hleft : Tendsto (fun z : ℂ => -2 * riordanSqrtPlus z) l
        (𝓝 (-2 * riordanSqrtPlusAtOneℂ)) := by
      have hcont : ContinuousAt (fun w : ℂ => -2 * w) riordanSqrtPlusAtOneℂ := by
        fun_prop
      exact hcont.tendsto.comp tendsto_riordanSqrtPlus
    have hright : Tendsto
        (fun z : ℂ => riordanSingularCoeff * riordanAℂ * (1 + z / 3)) l
        (𝓝 (riordanSingularCoeff * riordanAℂ * riordanAℂ)) := by
      have hcont : ContinuousAt
          (fun w : ℂ => riordanSingularCoeff * riordanAℂ * w) riordanAℂ := by
        fun_prop
      exact hcont.tendsto.comp hlinear
    have h := hleft.sub hright
    rwa [riordan_sqrt_constant_cancel] at h
  have hterm3 : Tendsto
      (fun z : ℂ =>
        riordanSingularCoeff * riordanAℂ *
          riordanSqrtPlus z * riordanSqrtOneSub z) l (𝓝 0) := by
    have hprod := tendsto_riordanSqrtPlus.mul tendsto_riordanSqrtOneSub
    have hprod0 : Tendsto (fun z : ℂ => riordanSqrtPlus z * riordanSqrtOneSub z) l
        (𝓝 0) := by
      convert hprod using 1
      simp
    have hcont : ContinuousAt
        (fun w : ℂ => riordanSingularCoeff * riordanAℂ * w) 0 := by
      fun_prop
    convert hcont.tendsto.comp hprod0 using 1
    · ext z
      simp [mul_assoc]
    · simp
  have hnum : Tendsto
      (fun z : ℂ =>
        (2 / 3 : ℂ) * riordanSqrtOneSub z -
          2 * riordanSqrtPlus z -
          riordanSingularCoeff * riordanAℂ * (1 + z / 3) -
          riordanSingularCoeff * riordanAℂ * riordanSqrtPlus z * riordanSqrtOneSub z) l
      (𝓝 0) := by
    have h12 := hterm1.add hterm2
    have h123 := h12.sub hterm3
    have h1230 : Tendsto
        (fun x : ℂ =>
          (2 / 3 : ℂ) * riordanSqrtOneSub x +
            (-2 * riordanSqrtPlus x -
              riordanSingularCoeff * riordanAℂ * (1 + x / 3)) -
            riordanSingularCoeff * riordanAℂ *
              riordanSqrtPlus x * riordanSqrtOneSub x) l (𝓝 0) := by
      simpa using h123
    convert h1230 using 1
    ext z
    ring
  have hden : Tendsto (fun z : ℂ => riordanAℂ * riordanRescaledDenominator z) l
      (𝓝 (riordanAℂ * riordanAℂ)) := by
    exact tendsto_const_nhds.mul tendsto_riordanRescaledDenominator
  have hden_ne : riordanAℂ * riordanAℂ ≠ 0 := by
    norm_num [riordanAℂ]
  have hquot := hnum.div hden hden_ne
  convert hquot using 1
  ext z
  simp

lemma riordan_singularity_quotient_eq {z : ℂ} (hz : z ≠ 1) (hznorm : ‖z‖ < 3) :
    (riordanCenteredRescaledFun z -
        riordanSingularCoeff * riordanSqrtOneSub z) / riordanSqrtOneSub z =
      riordanSingularityQuotientModel z := by
  have ht : riordanSqrtOneSub z ≠ 0 := riordanSqrtOneSub_ne_zero_of_ne_one hz
  have hD : riordanRescaledDenominator z ≠ 0 :=
    riordanRescaledDenominator_ne_zero_of_norm_lt_three hznorm
  unfold riordanSingularityQuotientModel riordanCenteredRescaledFun riordanRescaledFun
    riordanRegularValueℂ riordanAℂ
  field_simp [ht, hD]
  unfold riordanRescaledDenominator
  ring_nf
  rw [riordanSqrtOneSub_sq]
  ring

lemma tendsto_riordanCenteredRescaledFun_singularity :
    Tendsto
      (fun z : ℂ =>
        ‖riordanCenteredRescaledFun z - riordanSingularCoeff * riordanSqrtOneSub z‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
      (𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)) (𝓝 0) := by
  let l := 𝓝[DeltaDomainArg (3 / 2) (Real.pi / 4)] (1 : ℂ)
  have hevq :
      (fun z : ℂ =>
        (riordanCenteredRescaledFun z -
          riordanSingularCoeff * riordanSqrtOneSub z) / riordanSqrtOneSub z)
        =ᶠ[l] riordanSingularityQuotientModel := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact riordan_singularity_quotient_eq hz.2.1 (by nlinarith [hz.1])
  have hquot : Tendsto
      (fun z : ℂ =>
        (riordanCenteredRescaledFun z -
          riordanSingularCoeff * riordanSqrtOneSub z) / riordanSqrtOneSub z)
      l (𝓝 0) :=
    tendsto_riordanSingularityQuotientModel.congr' hevq.symm
  have hnorm : Tendsto
      (fun z : ℂ =>
        ‖(riordanCenteredRescaledFun z -
          riordanSingularCoeff * riordanSqrtOneSub z) / riordanSqrtOneSub z‖)
      l (𝓝 0) := by
    simpa using hquot.norm
  have heq :
      (fun z : ℂ =>
        ‖riordanCenteredRescaledFun z - riordanSingularCoeff * riordanSqrtOneSub z‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
        =ᶠ[l]
      (fun z : ℂ =>
        ‖(riordanCenteredRescaledFun z -
          riordanSingularCoeff * riordanSqrtOneSub z) / riordanSqrtOneSub z‖) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz_ne : z ≠ 1 := hz.2.1
    have ht : riordanSqrtOneSub z ≠ 0 := riordanSqrtOneSub_ne_zero_of_ne_one hz_ne
    have hu_pos : 0 < ‖(1 : ℂ) - z‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz_ne))
    have hnormT : ‖riordanSqrtOneSub z‖ = ‖(1 : ℂ) - z‖ ^ (1 / 2 : ℝ) := by
      unfold riordanSqrtOneSub motzkinSqrtOneSub
      convert Complex.norm_cpow_real ((1 : ℂ) - z) (1 / 2 : ℝ) using 1
      norm_num
    calc
      ‖riordanCenteredRescaledFun z - riordanSingularCoeff * riordanSqrtOneSub z‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ))
          = ‖riordanCenteredRescaledFun z - riordanSingularCoeff * riordanSqrtOneSub z‖ /
              ‖(1 : ℂ) - z‖ ^ (1 / 2 : ℝ) := by
            rw [Real.rpow_neg hu_pos.le]
            rfl
      _ = ‖riordanCenteredRescaledFun z - riordanSingularCoeff * riordanSqrtOneSub z‖ /
              ‖riordanSqrtOneSub z‖ := by rw [hnormT]
      _ = ‖(riordanCenteredRescaledFun z -
              riordanSingularCoeff * riordanSqrtOneSub z) / riordanSqrtOneSub z‖ := by
            rw [norm_div]
  exact hnorm.congr' heq.symm

/-- The rescaled Riordan series with its regular value at the dominant
singularity subtracted. -/
def riordanCenteredRescaledSeriesℂ : PowerSeries ℂ :=
  riordanRescaledSeriesℂ - PowerSeries.C riordanRegularValueℂ

lemma coeff_riordanCenteredRescaledSeriesℂ_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff (R := ℂ) n riordanCenteredRescaledSeriesℂ =
      PowerSeries.coeff (R := ℂ) n riordanRescaledSeriesℂ := by
  simp [riordanCenteredRescaledSeriesℂ, PowerSeries.coeff_C, hn]

lemma coeff_riordanScaleX_mul_zero (P : PowerSeries ℂ) :
    PowerSeries.coeff (R := ℂ) 0 (riordanScaleX * P) = 0 := by
  simp [riordanScaleX]

lemma coeff_riordanScaleX_mul_succ (P : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 1) (riordanScaleX * P) =
      (3 : ℂ)⁻¹ * PowerSeries.coeff (R := ℂ) n P := by
  rw [riordanScaleX, mul_assoc, PowerSeries.coeff_C_mul]
  simp

lemma coeff_riordanScaleX_sq_mul_succ_succ (P : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) (n + 2) (riordanScaleX ^ 2 * P) =
      ((3 : ℂ)⁻¹) ^ 2 * PowerSeries.coeff (R := ℂ) n P := by
  rw [pow_two, mul_assoc, coeff_riordanScaleX_mul_succ, coeff_riordanScaleX_mul_succ]
  ring

lemma coeff_riordanScaleX_sq_mul_of_lt_two (P : PowerSeries ℂ) {n : ℕ} (hn : n < 2) :
    PowerSeries.coeff (R := ℂ) n (riordanScaleX ^ 2 * P) = 0 := by
  cases n with
  | zero =>
      simp [riordanScaleX]
  | succ n =>
      cases n with
      | zero =>
          rw [pow_two, mul_assoc, coeff_riordanScaleX_mul_succ,
            coeff_riordanScaleX_mul_zero]
          ring
      | succ n =>
          omega

lemma riordan_linear_solution_unique {P Q : PowerSeries ℂ}
    (hP : P = 1 + riordanScaleX ^ 2 * (motzkinRescaledSeriesℂ * P))
    (hQ : Q = 1 + riordanScaleX ^ 2 * (motzkinRescaledSeriesℂ * Q)) :
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
          simp [riordanScaleX] at hp hq
          simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, hq]
      | succ n =>
          cases n with
          | zero =>
              have hp := congrArg (fun S : PowerSeries ℂ =>
                PowerSeries.coeff (R := ℂ) 1 S) hP
              have hq := congrArg (fun S : PowerSeries ℂ =>
                PowerSeries.coeff (R := ℂ) 1 S) hQ
              simp only [map_add, PowerSeries.coeff_one, one_ne_zero, ↓reduceIte,
                zero_add] at hp hq
              rw [hp, hq]
              rw [coeff_riordanScaleX_sq_mul_of_lt_two _ (by norm_num : 1 < 2),
                coeff_riordanScaleX_sq_mul_of_lt_two _ (by norm_num : 1 < 2)]
          | succ n =>
              have hp := congrArg (fun S : PowerSeries ℂ =>
                PowerSeries.coeff (R := ℂ) (n + 2) S) hP
              have hq := congrArg (fun S : PowerSeries ℂ =>
                PowerSeries.coeff (R := ℂ) (n + 2) S) hQ
              simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte,
                zero_add] at hp hq
              rw [hp, hq]
              rw [coeff_riordanScaleX_sq_mul_succ_succ,
                coeff_riordanScaleX_sq_mul_succ_succ]
              congr 1
              rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
              apply Finset.sum_congr rfl
              intro kl hkl
              have hlt : kl.2 < n + 2 := by
                have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
                omega
              simp [ih kl.2 hlt]

theorem riordanRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt riordanRescaledFun
      (PowerSeries.toFMLS riordanRescaledSeriesℂ) (0 : ℂ) := by
  have han : AnalyticAt ℂ riordanRescaledFun (0 : ℂ) :=
    analyticOnNhd_riordanRescaledFun 0
      (zero_mem_deltaDomainArg (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
        (by norm_num) (by nlinarith [Real.pi_pos]))
  rcases han with ⟨p, hp⟩
  let P : PowerSeries ℂ := powerSeriesOfFMLSℂ p
  have hPto : PowerSeries.toFMLS P = p := by
    simpa [P] using toFMLS_powerSeriesOfFMLSℂ p
  have hpP : HasFPowerSeriesAt riordanRescaledFun
      (PowerSeries.toFMLS P) (0 : ℂ) := by
    simpa [hPto] using hp
  have hconstScale : HasFPowerSeriesAt (fun _ : ℂ => ((3 : ℂ)⁻¹))
      (PowerSeries.toFMLS (PowerSeries.C ((3 : ℂ)⁻¹))) (0 : ℂ) :=
    hasFPowerSeriesAt_const_toFMLS_C ((3 : ℂ)⁻¹)
  have hscale0 := hasFPowerSeriesAt_mul_toFMLS hconstScale
    hasFPowerSeriesAt_id_toFMLS_X
  have hscale : HasFPowerSeriesAt (fun z : ℂ => z / 3)
      (PowerSeries.toFMLS riordanScaleX) (0 : ℂ) := by
    refine hscale0.congr (Eventually.of_forall ?_)
    intro z
    ring
  have hscaleSq := hasFPowerSeriesAt_mul_toFMLS hscale hscale
  have hMF := hasFPowerSeriesAt_mul_toFMLS
    motzkinRescaledFun_hasFPowerSeriesAt_zero hpP
  have hterm := hasFPowerSeriesAt_mul_toFMLS hscaleSq hMF
  have hconstOne : HasFPowerSeriesAt (fun _ : ℂ => (1 : ℂ))
      (PowerSeries.toFMLS (1 : PowerSeries ℂ)) (0 : ℂ) := by
    simpa using hasFPowerSeriesAt_const_toFMLS_C (1 : ℂ)
  have hrhs0 := hconstOne.add hterm
  have hrhs : HasFPowerSeriesAt
      (fun z : ℂ =>
        1 + (z / 3) ^ 2 * motzkinRescaledFun z * riordanRescaledFun z)
      (PowerSeries.toFMLS
        (1 + riordanScaleX ^ 2 * (motzkinRescaledSeriesℂ * P))) (0 : ℂ) := by
    simpa [toFMLS_add, pow_two, mul_assoc] using hrhs0
  have hevent :
      (fun z : ℂ =>
        riordanRescaledFun z) =ᶠ[𝓝 (0 : ℂ)]
      (fun z : ℂ =>
        1 + (z / 3) ^ 2 * motzkinRescaledFun z * riordanRescaledFun z) := by
    refine eventually_of_mem
      (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)) ?_
    intro z hz
    have hnorm1 : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact riordanRescaledFun_functional_of_norm_lt_three (by nlinarith)
  have hFMLS :
      PowerSeries.toFMLS P =
        PowerSeries.toFMLS
          (1 + riordanScaleX ^ 2 * (motzkinRescaledSeriesℂ * P)) :=
    hpP.eq_formalMultilinearSeries_of_eventually hrhs hevent
  have hPquad :
      P = 1 + riordanScaleX ^ 2 * (motzkinRescaledSeriesℂ * P) :=
    PowerSeries_toFMLS_injective hFMLS
  have hP_eq : P = riordanRescaledSeriesℂ :=
    riordan_linear_solution_unique hPquad riordanRescaledSeriesℂ_functional
  simpa [hP_eq] using hpP

theorem riordanCenteredRescaledFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt riordanCenteredRescaledFun
      (PowerSeries.toFMLS riordanCenteredRescaledSeriesℂ) (0 : ℂ) := by
  have hsub := riordanRescaledFun_hasFPowerSeriesAt_zero.sub
    (hasFPowerSeriesAt_const_toFMLS_C riordanRegularValueℂ)
  simpa [riordanCenteredRescaledFun, riordanCenteredRescaledSeriesℂ, toFMLS_sub] using hsub

/-- The real transfer constant in the form `C * 3^n * n^(-3/2)`. -/
def riordanAsymptoticConstant : ℝ :=
  3 * Real.sqrt 3 / (8 * Real.sqrt Real.pi)

lemma riordan_transfer_constant_complex :
    riordanSingularCoeff / Complex.Gamma (-1 / 2 : ℂ) =
      ((riordanAsymptoticConstant : ℝ) : ℂ) := by
  rw [riordanSingularCoeff, riordanAsymptoticConstant, Complex_Gamma_neg_half]
  have hsqrtπ_ne : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hleft :
      -(((3 * Real.sqrt 3 / 4 : ℝ) : ℂ)) /
          (-2 * ((Real.sqrt Real.pi : ℝ) : ℂ)) =
        (((-(3 * Real.sqrt 3 / 4)) / (-(2 * Real.sqrt Real.pi)) : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg]
  rw [hleft]
  congr 1
  ring_nf

lemma riordan_rescale_back (n : ℕ) :
    ((riordan n : ℂ) * ((3 : ℂ)⁻¹) ^ n) * (3 : ℂ) ^ n =
      (riordan n : ℂ) := by
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ h3, one_pow, mul_one]

lemma transfer_target_to_riordan_complex_eventuallyEq :
    (fun n : ℕ =>
        (riordanSingularCoeff * (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) /
            Complex.Gamma (-1 / 2 : ℂ)) *
          (3 : ℂ) ^ n) =ᶠ[atTop]
      (fun n : ℕ =>
        ((riordanAsymptoticConstant * (3 : ℝ) ^ n *
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
  calc
    (riordanSingularCoeff * (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) /
          Complex.Gamma (-1 / 2 : ℂ)) * (3 : ℂ) ^ n
        = (riordanSingularCoeff / Complex.Gamma (-1 / 2 : ℂ)) *
            (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) * (3 : ℂ) ^ n := by ring
    _ = (riordanAsymptoticConstant : ℂ) *
            (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((3 : ℝ) ^ n : ℂ) := by
          rw [riordan_transfer_constant_complex, hcpow]
          norm_num [Complex.ofReal_pow]
    _ = ((riordanAsymptoticConstant * (3 : ℝ) ^ n *
            (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
          norm_num [Complex.ofReal_mul, Complex.ofReal_pow]
          ring

/--
Coefficient asymptotic from the square-root transfer theorem for the centered
rescaled Riordan OGF.
-/
theorem riordan_isEquivalent_complex_of_centered_rescaled_transfer
    {R φ : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f (PowerSeries.toFMLS riordanCenteredRescaledSeriesℂ) 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖f z - riordanSingularCoeff * (1 - z) ^ (1 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => (riordan n : ℂ)) ~[atTop]
    (fun n : ℕ =>
        ((riordanAsymptoticConstant * (3 : ℝ) ^ n *
            (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have hsing_transfer : Tendsto
      (fun z : ℂ =>
        ‖f z - riordanSingularCoeff * (1 - z) ^ (-(-1 / 2 : ℂ))‖ *
          ‖(1 : ℂ) - z‖ ^ ((-1 / 2 : ℂ).re))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    convert hsing using 1
    ext z
    norm_num
  have hC : riordanSingularCoeff ≠ 0 := by
    rw [riordanSingularCoeff]
    norm_num
  have htransfer :=
    transfer_theorem (α := (-1 / 2 : ℂ)) (C := riordanSingularCoeff)
      (R := R) (φ := φ) (f := f) (p := PowerSeries.toFMLS riordanCenteredRescaledSeriesℂ)
      neg_half_not_neg_nat hC hR hφ0 hφ2 hp hΔ hsing_transfer
  have hmul :
      (fun n : ℕ =>
        (PowerSeries.toFMLS riordanCenteredRescaledSeriesℂ).coeff n * (3 : ℂ) ^ n)
        ~[atTop]
      (fun n : ℕ =>
        (riordanSingularCoeff * (n : ℂ) ^ ((-1 / 2 : ℂ) - 1) /
            Complex.Gamma (-1 / 2 : ℂ)) *
          (3 : ℂ) ^ n) := by
      simpa only [Pi.mul_apply] using
        htransfer.mul
          (Asymptotics.IsEquivalent.refl (l := atTop) (u := fun n : ℕ => (3 : ℂ) ^ n))
  have hcoeff :
      (fun n : ℕ =>
        (PowerSeries.toFMLS riordanCenteredRescaledSeriesℂ).coeff n * (3 : ℂ) ^ n) =ᶠ[atTop]
        (fun n : ℕ => (riordan n : ℂ)) := by
    refine (eventually_ne_atTop 0).mono ?_
    intro n hn
    change (PowerSeries.toFMLS riordanCenteredRescaledSeriesℂ).coeff n * (3 : ℂ) ^ n =
      (riordan n : ℂ)
    rw [PowerSeries.coeff_toFMLS, coeff_riordanCenteredRescaledSeriesℂ_of_ne_zero hn,
      coeff_riordanRescaledSeriesℂ]
    exact riordan_rescale_back n
  exact hcoeff.symm.trans_isEquivalent
    (hmul.trans_eventuallyEq transfer_target_to_riordan_complex_eventuallyEq)

/-- Real-valued form of the Riordan transfer theorem. -/
theorem riordan_isEquivalent_real_of_centered_rescaled_transfer
    {R φ : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f (PowerSeries.toFMLS riordanCenteredRescaledSeriesℂ) 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖f z - riordanSingularCoeff * (1 - z) ^ (1 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(1 / 2 : ℝ)))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => (riordan n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        riordanAsymptoticConstant * (3 : ℝ) ^ n *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  rw [← ofReal_isEquivalent_iff]
  exact riordan_isEquivalent_complex_of_centered_rescaled_transfer hR hφ0 hφ2 hp hΔ hsing

theorem riordan_isEquivalent_of_centered_explicit_hasFPowerSeries
    (hp : HasFPowerSeriesAt riordanCenteredRescaledFun
      (PowerSeries.toFMLS riordanCenteredRescaledSeriesℂ) 0) :
    (fun n : ℕ => (riordan n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        riordanAsymptoticConstant * (3 : ℝ) ^ n *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  refine riordan_isEquivalent_real_of_centered_rescaled_transfer
    (R := (3 / 2 : ℝ)) (φ := Real.pi / 4)
    (f := riordanCenteredRescaledFun) ?_ ?_ ?_ hp
    analyticOnNhd_riordanCenteredRescaledFun ?_
  · norm_num
  · positivity
  · nlinarith [Real.pi_pos]
  · simpa [riordanSqrtOneSub, motzkinSqrtOneSub] using
      tendsto_riordanCenteredRescaledFun_singularity

theorem riordan_isEquivalent :
    (fun n : ℕ => (riordan n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        riordanAsymptoticConstant * (3 : ℝ) ^ n *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
  riordan_isEquivalent_of_centered_explicit_hasFPowerSeries
    riordanCenteredRescaledFun_hasFPowerSeriesAt_zero

def riordanAsymptoticRatio (n : ℕ) : Float :=
  (riordan n).toFloat /
    ((3.0 * Float.sqrt 3.0) / (8.0 * Float.sqrt 3.141592653589793) *
      3.0 ^ n.toFloat * n.toFloat ^ (-1.5))

#eval (riordan 4, riordan 5, riordan 6, riordan 7, riordan 10)
#eval [4, 5, 6, 7, 10].map riordanAsymptoticRatio
