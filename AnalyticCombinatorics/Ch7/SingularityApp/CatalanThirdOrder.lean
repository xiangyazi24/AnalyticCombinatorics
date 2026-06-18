import AnalyticCombinatorics.Ch4.Analytic.CentralBinomial
import AnalyticCombinatorics.Ch4.Analytic.ModelCoeffThirdOrder
import AnalyticCombinatorics.Ch7.SingularityApp.CatalanSecondOrder

/-!
# Third-order Catalan asymptotics

This file proves the three-term Catalan asymptotic by combining the committed
third-order model coefficient estimate with the exact central-binomial bridge.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

def catalanRelativeThirdConstant : ℝ :=
  145 / 128

def catalanThirdAsymptoticConstant : ℝ :=
  145 / (128 * Real.sqrt Real.pi)

private def centralBinomSecondConstant : ℝ :=
  -(1 / (8 * Real.sqrt Real.pi))

private def centralBinomThirdConstant : ℝ :=
  1 / (128 * Real.sqrt Real.pi)

private lemma ofReal_isLittleO {u v : ℕ → ℝ}
    (h : u =o[atTop] v) :
    (fun n : ℕ => ((u n : ℝ) : ℂ)) =o[atTop] v := by
  exact Asymptotics.IsLittleO.of_norm_left (by
    simpa [Complex.norm_real] using h.norm_left)

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

private lemma inv_succ_sub_inv_isBigO :
    (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹) =
        -(1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
  have habs :
      |(((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹)| =
        1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [hdiff, abs_neg, abs_of_nonneg]
    positivity
  have hden_le : (n : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg (n : ℝ), hnpos.le]
  have htail_le :
      1 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ 1 / (n : ℝ) ^ 2 := by
    exact one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) ^ 2) hden_le
  have htarget : (n : ℝ) ^ (-(2 : ℝ)) = 1 / (n : ℝ) ^ 2 := by
    rw [Real.rpow_neg hnpos.le]
    norm_num
  calc
    ‖(((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹)‖
        = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
          simpa [Real.norm_eq_abs] using habs
    _ ≤ 1 / (n : ℝ) ^ 2 := htail_le
    _ = 1 * ‖(n : ℝ) ^ (-(2 : ℝ))‖ := by
          rw [htarget, Real.norm_of_nonneg (by positivity)]
          ring

private lemma inv_succ_sub_inv_add_inv_sq_isBigO :
    (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 2) =
        1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
  have habs :
      |(((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 2)| =
        1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
    rw [hdiff, abs_of_nonneg]
    positivity
  have hden_le : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg (n : ℝ), hnpos.le]
  have htail_le :
      1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) ≤ 1 / (n : ℝ) ^ 3 := by
    exact one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) ^ 3) hden_le
  have htarget : (n : ℝ) ^ (-(3 : ℝ)) = 1 / (n : ℝ) ^ 3 := by
    rw [Real.rpow_neg hnpos.le]
    norm_num
  calc
    ‖(((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 2)‖
        = 1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
          simpa [Real.norm_eq_abs] using habs
    _ ≤ 1 / (n : ℝ) ^ 3 := htail_le
    _ = 1 * ‖(n : ℝ) ^ (-(3 : ℝ))‖ := by
          rw [htarget, Real.norm_of_nonneg (by positivity)]
          ring

private lemma inv_succ_sub_inv_add_inv_sq_sub_inv_cube_isBigO :
    (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 2 -
        ((n : ℝ)⁻¹) ^ 3))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(4 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 2 -
          ((n : ℝ)⁻¹) ^ 3) =
        -(1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1))) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
  have habs :
      |(((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 2 -
          ((n : ℝ)⁻¹) ^ 3)| =
        1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1)) := by
    rw [hdiff, abs_neg, abs_of_nonneg]
    positivity
  have hden_le : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 3 * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ) ^ 2), hnpos.le]
  have htail_le :
      1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1)) ≤ 1 / (n : ℝ) ^ 4 := by
    exact one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) ^ 4) hden_le
  have htarget : (n : ℝ) ^ (-(4 : ℝ)) = 1 / (n : ℝ) ^ 4 := by
    rw [Real.rpow_neg hnpos.le]
    norm_num
  calc
    ‖(((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 2 -
        ((n : ℝ)⁻¹) ^ 3)‖
        = 1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1)) := by
          simpa [Real.norm_eq_abs] using habs
    _ ≤ 1 / (n : ℝ) ^ 4 := htail_le
    _ = 1 * ‖(n : ℝ) ^ (-(4 : ℝ))‖ := by
          rw [htarget, Real.norm_of_nonneg (by positivity)]
          ring

private lemma rpow_mul_inv_eventually (a : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ a * (n : ℝ)⁻¹) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 1)) := by
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  calc
    (n : ℝ) ^ a * (n : ℝ)⁻¹
        = (n : ℝ) ^ a * (n : ℝ) ^ (-(1 : ℝ)) := by
            rw [Real.rpow_neg hnpos.le, Real.rpow_one]
    _ = (n : ℝ) ^ (a + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
    _ = (n : ℝ) ^ (a - 1) := by ring_nf

private lemma rpow_mul_inv_sq_eventually (a : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ a * ((n : ℝ)⁻¹) ^ 2) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  calc
    (n : ℝ) ^ a * ((n : ℝ)⁻¹) ^ 2
        = (n : ℝ) ^ a * (n : ℝ) ^ (-(2 : ℝ)) := by
            rw [Real.rpow_neg hnpos.le]
            norm_num
    _ = (n : ℝ) ^ (a + (-(2 : ℝ))) := by rw [← Real.rpow_add hnpos]
    _ = (n : ℝ) ^ (a - 2) := by ring_nf

private lemma rpow_mul_inv_cube_eventually (a : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ a * ((n : ℝ)⁻¹) ^ 3) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 3)) := by
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  calc
    (n : ℝ) ^ a * ((n : ℝ)⁻¹) ^ 3
        = (n : ℝ) ^ a * (n : ℝ) ^ (-(3 : ℝ)) := by
            rw [Real.rpow_neg hnpos.le]
            norm_num
    _ = (n : ℝ) ^ (a + (-(3 : ℝ))) := by rw [← Real.rpow_add hnpos]
    _ = (n : ℝ) ^ (a - 3) := by ring_nf

private lemma rpow_mul_inv_succ_sub_inv_isBigO (a : ℝ) :
    (fun n : ℕ =>
      (n : ℝ) ^ a * ((((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹))
      )
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
  have hp : (fun n : ℕ => (n : ℝ) ^ a)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ a) := isBigO_refl _ _
  exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
    a (-(2 : ℝ)) (a - 2) hp inv_succ_sub_inv_isBigO (by linarith)

private lemma rpow_mul_inv_succ_sub_inv_add_inv_sq_isBigO (a : ℝ) :
    (fun n : ℕ =>
      (n : ℝ) ^ a *
        (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 3)) := by
  have hp : (fun n : ℕ => (n : ℝ) ^ a)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ a) := isBigO_refl _ _
  exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
    a (-(3 : ℝ)) (a - 3) hp inv_succ_sub_inv_add_inv_sq_isBigO (by linarith)

private lemma rpow_mul_inv_succ_three_tail_isBigO (a : ℝ) :
    (fun n : ℕ =>
      (n : ℝ) ^ a *
        (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ + ((n : ℝ)⁻¹) ^ 2 -
          ((n : ℝ)⁻¹) ^ 3))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 4)) := by
  have hp : (fun n : ℕ => (n : ℝ) ^ a)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ a) := isBigO_refl _ _
  exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
    a (-(4 : ℝ)) (a - 4) hp inv_succ_sub_inv_add_inv_sq_sub_inv_cube_isBigO (by linarith)

private lemma centralBinom_eq_four_pow_mul_half_choose_real (n : ℕ) :
    ((n.centralBinom : ℝ) =
      (4 : ℝ) ^ n * Ring.choose ((1 / 2 : ℝ) + (n : ℕ) - 1) n) := by
  apply Complex.ofReal_injective
  simpa [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_choose] using
    centralBinom_eq_four_pow_mul_half_choose n

lemma catalan_rescaled_eq_inv_succ_mul_half_choose (n : ℕ) :
    (catalan n : ℝ) * ((4 : ℝ)⁻¹) ^ n =
      (((n + 1 : ℕ) : ℝ)⁻¹ *
        Ring.choose ((1 / 2 : ℝ) + (n : ℕ) - 1) n) := by
  have hcat : (((n + 1 : ℕ) : ℝ) * (catalan n : ℝ)) = (n.centralBinom : ℝ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom n
  have hcentral := centralBinom_eq_four_pow_mul_half_choose_real n
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)
  calc
    (catalan n : ℝ) * ((4 : ℝ)⁻¹) ^ n
        = (((n + 1 : ℕ) : ℝ)⁻¹ *
            (((n + 1 : ℕ) : ℝ) * (catalan n : ℝ))) * ((4 : ℝ)⁻¹) ^ n := by
          field_simp [hn1]
    _ = (((n + 1 : ℕ) : ℝ)⁻¹ * (n.centralBinom : ℝ)) * ((4 : ℝ)⁻¹) ^ n := by
          rw [hcat]
    _ = (((n + 1 : ℕ) : ℝ)⁻¹ *
          ((4 : ℝ) ^ n * Ring.choose ((1 / 2 : ℝ) + (n : ℕ) - 1) n)) *
          ((4 : ℝ)⁻¹) ^ n := by
          rw [hcentral]
    _ = (((n + 1 : ℕ) : ℝ)⁻¹ *
        Ring.choose ((1 / 2 : ℝ) + (n : ℕ) - 1) n) := by
          have hpow_cancel : (4 : ℝ) ^ n * ((4 : ℝ)⁻¹) ^ n = 1 := by
            rw [← mul_pow]
            norm_num
          rw [show (((n + 1 : ℕ) : ℝ)⁻¹ *
              ((4 : ℝ) ^ n * Ring.choose ((1 / 2 : ℝ) + (n : ℕ) - 1) n)) *
              ((4 : ℝ)⁻¹) ^ n =
              (((n + 1 : ℕ) : ℝ)⁻¹ *
                Ring.choose ((1 / 2 : ℝ) + (n : ℕ) - 1) n) *
                ((4 : ℝ) ^ n * ((4 : ℝ)⁻¹) ^ n) by ring]
          rw [hpow_cancel, mul_one]

private lemma Real.Gamma_one_half_eq_sqrt_pi :
    Real.Gamma (1 / 2 : ℝ) = Real.sqrt Real.pi := by
  simpa using Real.Gamma_one_half_eq

private def centralBinomThirdModel (n : ℕ) : ℝ :=
  catalanAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
    centralBinomSecondConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
    centralBinomThirdConstant * (n : ℝ) ^ (-(5 / 2 : ℝ))

private def catalanThirdModel (n : ℕ) : ℝ :=
  catalanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
    catalanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
    catalanThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ))

private lemma modelCoeff_half_thirdOrder :
    (fun n : ℕ =>
      Ring.choose ((1 / 2 : ℝ) + (n : ℕ) - 1) n - centralBinomThirdModel n)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have h := modelCoeff_thirdOrder (α := (1 / 2 : ℝ)) (by norm_num)
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
    have hpow1 : (n : ℝ) ^ ((1 / 2 : ℝ) - 1) =
        (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      congr 1
      ring
    have hpow2 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹ =
        (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      have hinv : (n : ℝ)⁻¹ = (n : ℝ) ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg hnpos.le, Real.rpow_one]
      calc
        (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹
            = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ)) := by rw [hinv]
        _ = (n : ℝ) ^ (-(1 / 2 : ℝ) + -(1 : ℝ)) := by
                rw [← Real.rpow_add hnpos]
        _ = (n : ℝ) ^ (-(3 / 2 : ℝ)) := by ring_nf
    have hpow3 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ)⁻¹) ^ 2 =
        (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
      have hinv2 : ((n : ℝ)⁻¹) ^ 2 = (n : ℝ) ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg hnpos.le]
        norm_num
      calc
        (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ)⁻¹) ^ 2
            = (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(2 : ℝ)) := by rw [hinv2]
        _ = (n : ℝ) ^ (-(1 / 2 : ℝ) + -(2 : ℝ)) := by
                rw [← Real.rpow_add hnpos]
        _ = (n : ℝ) ^ (-(5 / 2 : ℝ)) := by ring_nf
    unfold centralBinomThirdModel catalanAsymptoticConstant centralBinomSecondConstant
      centralBinomThirdConstant
    rw [hpow1, Real.Gamma_one_half_eq_sqrt_pi]
    norm_num
    ring_nf
    have hterm2 :
        (n : ℝ) ^ (-1 / 2 : ℝ) * (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ *
            (-1 / 8 : ℝ) =
          (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-3 / 2 : ℝ) * (-1 / 8 : ℝ) := by
      rw [show (n : ℝ) ^ (-1 / 2 : ℝ) * (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ =
          (Real.sqrt Real.pi)⁻¹ * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹) by ring_nf,
        hpow2]
      ring_nf
    have hterm3 :
        (n : ℝ) ^ (-1 / 2 : ℝ) * (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ ^ 2 *
            (1 / 128 : ℝ) =
          (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-5 / 2 : ℝ) * (1 / 128 : ℝ) := by
      rw [show (n : ℝ) ^ (-1 / 2 : ℝ) * (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ ^ 2 =
          (Real.sqrt Real.pi)⁻¹ * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹ ^ 2) by ring_nf,
        hpow3]
      ring_nf
    rw [hterm2, hterm3]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    congr 1
    ring_nf

private lemma inv_succ_mul_model_error :
    (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ)⁻¹ *
        (Ring.choose ((1 / 2 : ℝ) + (n : ℕ) - 1) n - centralBinomThirdModel n)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hinv : (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
    refine IsBigO.of_bound 1 ?_
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ (n : ℝ)⁻¹ := by
      exact inv_anti₀ hnpos (by exact_mod_cast Nat.le_succ n)
    have htarget : (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ)⁻¹ := by
      rw [Real.rpow_neg hnpos.le, Real.rpow_one]
    calc
      ‖(((n + 1 : ℕ) : ℝ)⁻¹)‖ = (((n + 1 : ℕ) : ℝ)⁻¹) := by
        rw [Real.norm_of_nonneg (inv_nonneg.mpr hn1pos.le)]
      _ ≤ (n : ℝ)⁻¹ := hle
      _ = 1 * ‖(n : ℝ) ^ (-(1 : ℝ))‖ := by
        rw [htarget, Real.norm_of_nonneg (by positivity)]
        ring
  have hmul := IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
    (-(1 : ℝ)) (-(7 / 2 : ℝ)) (-(9 / 2 : ℝ))
    hinv modelCoeff_half_thirdOrder (by linarith)
  have hsmall : (fun n : ℕ => (n : ℝ) ^ (-(9 / 2 : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert rpow_sub_one_isLittleO (-(7 / 2 : ℝ)) using 1
    ext n
    congr 1
    ring
  exact hmul.trans_isLittleO hsmall

private lemma inv_succ_mul_central_model :
    (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ)⁻¹ * centralBinomThirdModel n - catalanThirdModel n))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have h0O := rpow_mul_inv_succ_three_tail_isBigO (a := (-(1 / 2 : ℝ)))
  have h0small : (fun n : ℕ => (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 4))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert rpow_sub_one_isLittleO (-(7 / 2 : ℝ)) using 1
    ext n
    congr 1
    ring
  have h0 := (h0O.trans_isLittleO h0small).const_mul_left catalanAsymptoticConstant
  have h1O := rpow_mul_inv_succ_sub_inv_add_inv_sq_isBigO (a := (-(3 / 2 : ℝ)))
  have h1small : (fun n : ℕ => (n : ℝ) ^ ((-(3 / 2 : ℝ)) - 3))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert rpow_sub_one_isLittleO (-(7 / 2 : ℝ)) using 1
    ext n
    congr 1
    ring
  have h1 := (h1O.trans_isLittleO h1small).const_mul_left centralBinomSecondConstant
  have h2O := rpow_mul_inv_succ_sub_inv_isBigO (a := (-(5 / 2 : ℝ)))
  have h2small : (fun n : ℕ => (n : ℝ) ^ ((-(5 / 2 : ℝ)) - 2))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert rpow_sub_one_isLittleO (-(7 / 2 : ℝ)) using 1
    ext n
    congr 1
    ring
  have h2 := (h2O.trans_isLittleO h2small).const_mul_left centralBinomThirdConstant
  have hsum := (h0.add h1).add h2
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hmul_inv (a : ℝ) :
      (n : ℝ) ^ a * (n : ℝ)⁻¹ = (n : ℝ) ^ (a - 1) := by
    calc
      (n : ℝ) ^ a * (n : ℝ)⁻¹ =
          (n : ℝ) ^ a * (n : ℝ) ^ (-(1 : ℝ)) := by
            rw [Real.rpow_neg hnpos.le, Real.rpow_one]
      _ = (n : ℝ) ^ (a + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (a - 1) := by ring_nf
  have hmul_inv_sq (a : ℝ) :
      (n : ℝ) ^ a * ((n : ℝ)⁻¹) ^ 2 = (n : ℝ) ^ (a - 2) := by
    calc
      (n : ℝ) ^ a * ((n : ℝ)⁻¹) ^ 2 =
          (n : ℝ) ^ a * (n : ℝ) ^ (-(2 : ℝ)) := by
            rw [Real.rpow_neg hnpos.le]
            norm_num
      _ = (n : ℝ) ^ (a + (-(2 : ℝ))) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (a - 2) := by ring_nf
  have hmul_inv_cube (a : ℝ) :
      (n : ℝ) ^ a * ((n : ℝ)⁻¹) ^ 3 = (n : ℝ) ^ (a - 3) := by
    calc
      (n : ℝ) ^ a * ((n : ℝ)⁻¹) ^ 3 =
          (n : ℝ) ^ a * (n : ℝ) ^ (-(3 : ℝ)) := by
            rw [Real.rpow_neg hnpos.le]
            norm_num
      _ = (n : ℝ) ^ (a + (-(3 : ℝ))) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (a - 3) := by ring_nf
  unfold centralBinomThirdModel catalanThirdModel catalanAsymptoticConstant
    catalanSecondAsymptoticConstant catalanThirdAsymptoticConstant
    centralBinomSecondConstant centralBinomThirdConstant
  ring_nf
  have h01 :
      (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ)⁻¹ =
        (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-3 / 2 : ℝ) := by
    rw [show (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ)⁻¹ =
        (Real.sqrt Real.pi)⁻¹ * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹) by ring_nf,
      hmul_inv (-(1 / 2 : ℝ))]
    ring_nf
  have h02 :
      (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ)⁻¹ ^ 2 =
        (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-5 / 2 : ℝ) := by
    rw [show (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ)⁻¹ ^ 2 =
        (Real.sqrt Real.pi)⁻¹ * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹ ^ 2) by ring_nf,
      hmul_inv_sq (-(1 / 2 : ℝ))]
    ring_nf
  have h03 :
      (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ)⁻¹ ^ 3 =
        (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-7 / 2 : ℝ) := by
    rw [show (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ)⁻¹ ^ 3 =
        (Real.sqrt Real.pi)⁻¹ * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹ ^ 3) by ring_nf,
      hmul_inv_cube (-(1 / 2 : ℝ))]
    ring_nf
  have h11 :
      (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ * (n : ℝ) ^ (-3 / 2 : ℝ) =
        (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-5 / 2 : ℝ) := by
    rw [show (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ * (n : ℝ) ^ (-3 / 2 : ℝ) =
        (Real.sqrt Real.pi)⁻¹ * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ)⁻¹) by ring_nf,
      hmul_inv (-(3 / 2 : ℝ))]
    ring_nf
  have h12 :
      (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ ^ 2 * (n : ℝ) ^ (-3 / 2 : ℝ) =
        (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-7 / 2 : ℝ) := by
    rw [show (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ ^ 2 * (n : ℝ) ^ (-3 / 2 : ℝ) =
        (Real.sqrt Real.pi)⁻¹ * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ)⁻¹ ^ 2) by ring_nf,
      hmul_inv_sq (-(3 / 2 : ℝ))]
    ring_nf
  have h21 :
      (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ * (n : ℝ) ^ (-5 / 2 : ℝ) =
        (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-7 / 2 : ℝ) := by
    rw [show (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ * (n : ℝ) ^ (-5 / 2 : ℝ) =
        (Real.sqrt Real.pi)⁻¹ * ((n : ℝ) ^ (-(5 / 2 : ℝ)) * (n : ℝ)⁻¹) by ring_nf,
      hmul_inv (-(5 / 2 : ℝ))]
    ring_nf
  rw [h01, h02, h03, h11, h12, h21]
  ring_nf

theorem catalanRescaled_real_thirdOrder :
    (fun n : ℕ =>
      (catalan n : ℝ) * ((4 : ℝ)⁻¹) ^ n - catalanThirdModel n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have h := inv_succ_mul_model_error.add inv_succ_mul_central_model
  refine h.congr_left ?_
  intro n
  rw [catalan_rescaled_eq_inv_succ_mul_half_choose n]
  ring

theorem catalanRescaled_complex_thirdOrder :
    (fun n : ℕ =>
      (catalan n : ℂ) * ((4 : ℂ)⁻¹) ^ n -
        (((catalanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
            catalanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
            catalanThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have h := ofReal_isLittleO catalanRescaled_real_thirdOrder
  refine h.congr_left ?_
  intro n
  unfold catalanThirdModel
  norm_num [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]

theorem catalan_complex_thirdOrder :
    (fun n : ℕ =>
      (catalan n : ℂ) -
        (4 : ℂ) ^ n *
          (((catalanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
              catalanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
              catalanThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop]
        (fun n : ℕ =>
          ‖(4 : ℂ) ^ n *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)‖) := by
  have hrescaled := catalanRescaled_complex_thirdOrder
  rw [Asymptotics.isLittleO_iff] at hrescaled ⊢
  intro c hc
  have hbound := hrescaled hc
  filter_upwards [hbound] with n hn
  let model : ℂ :=
    (((catalanAsymptoticConstant * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
        catalanSecondAsymptoticConstant * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
        catalanThirdAsymptoticConstant * (n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))
  let r : ℂ := (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)
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
    _ ≤ ‖(4 : ℂ) ^ n‖ * (c * ‖(n : ℝ) ^ (-(7 / 2 : ℝ))‖) :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = c * ‖‖(4 : ℂ) ^ n * r‖‖ := by
        rw [hnorm_target]
        simp [r, Complex.norm_real]
        ring

end
