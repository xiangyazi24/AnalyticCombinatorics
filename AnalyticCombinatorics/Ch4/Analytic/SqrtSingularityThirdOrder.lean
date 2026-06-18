import AnalyticCombinatorics.Ch4.Analytic.SqrtSingularitySecondOrder
import AnalyticCombinatorics.Ch4.Analytic.ModelCoeffThirdOrder

/-!
# Third-order square-root singularity applicator

This file extends `SqrtSingularitySecondOrder` by keeping the third
half-integer contribution.  The constants are obtained from
`modelCoeff_thirdOrder` through the positive half-model and the exact
coefficient recurrences for `(1 - z)^(1/2)`, `(1 - z)^(3/2)`, and
`(1 - z)^(5/2)`.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

def sqrtSingularityC2Rescaled (B0 B1 B2 : ℂ) : ℂ :=
  -(25 : ℂ) * B0 / (((256 * Real.sqrt Real.pi : ℝ) : ℂ)) -
    (45 : ℂ) * B1 / (((32 * Real.sqrt Real.pi : ℝ) : ℂ)) -
      (15 : ℂ) * B2 / (((16 * Real.sqrt Real.pi : ℝ) : ℂ))

def sqrtSingularityC2 (ρ : ℝ) (Bρ Bderivρ Bsecondρ : ℂ) : ℂ :=
  sqrtSingularityC2Rescaled Bρ (((ρ : ℝ) : ℂ) * Bderivρ)
    ((((ρ : ℝ) : ℂ) ^ 2) * Bsecondρ)

def sqrtSingularityRelativeC2 (B0 B1 B2 : ℂ) : ℂ :=
  (25 / 128 : ℂ) + (45 / 16 : ℂ) * B1 / B0 +
    (15 / 8 : ℂ) * B2 / B0

private def sqrtHalfModel0 : ℝ :=
  1 / Real.sqrt Real.pi

private def sqrtHalfModel1 : ℝ :=
  -(1 / (8 * Real.sqrt Real.pi))

private def sqrtHalfModel2 : ℝ :=
  1 / (128 * Real.sqrt Real.pi)

private def sqrtHalfThirdModel (n : ℕ) : ℝ :=
  sqrtHalfModel0 * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
    sqrtHalfModel1 * (n : ℝ) ^ (-(3 / 2 : ℝ)) +
      sqrtHalfModel2 * (n : ℝ) ^ (-(5 / 2 : ℝ))

private def sqrtModel0Third (n : ℕ) : ℝ :=
  -(1 / (2 * Real.sqrt Real.pi)) * (n : ℝ) ^ (-(3 / 2 : ℝ)) -
    (3 / (16 * Real.sqrt Real.pi)) * (n : ℝ) ^ (-(5 / 2 : ℝ)) -
      (25 / (256 * Real.sqrt Real.pi)) * (n : ℝ) ^ (-(7 / 2 : ℝ))

private def sqrtModel1Third (n : ℕ) : ℝ :=
  (3 / (4 * Real.sqrt Real.pi)) * (n : ℝ) ^ (-(5 / 2 : ℝ)) +
    (45 / (32 * Real.sqrt Real.pi)) * (n : ℝ) ^ (-(7 / 2 : ℝ))

private def sqrtModel2Third (n : ℕ) : ℝ :=
  -(15 / (8 * Real.sqrt Real.pi)) * (n : ℝ) ^ (-(7 / 2 : ℝ))

private lemma ofReal_isLittleO {u v : ℕ → ℝ}
    (h : u =o[atTop] v) :
    (fun n : ℕ => ((u n : ℝ) : ℂ)) =o[atTop] v := by
  exact Asymptotics.IsLittleO.of_norm_left (by
    simpa [Complex.norm_real] using h.norm_left)

private lemma ofReal_isBigO {u v : ℕ → ℝ}
    (h : u =O[atTop] v) :
    (fun n : ℕ => ((u n : ℝ) : ℂ)) =O[atTop] v := by
  exact Asymptotics.IsBigO.of_norm_left (by
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

private lemma sqrt_half_modelCoeff_thirdOrder :
    (fun n : ℕ =>
      Ring.choose ((1 / 2 : ℝ) + (n : ℕ) - 1) n - sqrtHalfThirdModel n)
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
    unfold sqrtHalfThirdModel sqrtHalfModel0 sqrtHalfModel1 sqrtHalfModel2
    rw [hpow1, Real.Gamma_one_half_eq]
    norm_num
    ring_nf
    have hterm2 :
        (n : ℝ) ^ (-1 / 2 : ℝ) * (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ *
            (-1 / 8 : ℝ) =
          (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-3 / 2 : ℝ) * (-1 / 8 : ℝ) := by
      rw [show (n : ℝ) ^ (-1 / 2 : ℝ) * (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ =
          (Real.sqrt Real.pi)⁻¹ * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹) by
            ring_nf,
        hpow2]
      ring_nf
    have hterm3 :
        (n : ℝ) ^ (-1 / 2 : ℝ) * (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ ^ 2 *
            (1 / 128 : ℝ) =
          (Real.sqrt Real.pi)⁻¹ * (n : ℝ) ^ (-5 / 2 : ℝ) * (1 / 128 : ℝ) := by
      rw [show (n : ℝ) ^ (-1 / 2 : ℝ) * (Real.sqrt Real.pi)⁻¹ * (n : ℝ)⁻¹ ^ 2 =
          (Real.sqrt Real.pi)⁻¹ * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹ ^ 2) by
            ring_nf,
        hpow3]
      ring_nf
    rw [hterm2, hterm3]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    congr 1
    ring_nf

private lemma prod_neg_half_shift (m : ℕ) :
    (∏ j ∈ Finset.range (m + 1), (-(1 / 2 : ℝ) + (j : ℝ))) =
      (-(1 / 2 : ℝ)) *
        (∏ j ∈ Finset.range m, ((1 / 2 : ℝ) + (j : ℝ))) := by
  induction m with
  | zero =>
      norm_num
  | succ m ih =>
      rw [Finset.prod_range_succ, ih, Finset.prod_range_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

private lemma prod_neg_three_halves_shift (m : ℕ) :
    (∏ j ∈ Finset.range (m + 2), (-(3 / 2 : ℝ) + (j : ℝ))) =
      (3 / 4 : ℝ) *
        (∏ j ∈ Finset.range m, ((1 / 2 : ℝ) + (j : ℝ))) := by
  induction m with
  | zero =>
      norm_num [Finset.prod_range_succ]
  | succ m ih =>
      rw [show m + 1 + 2 = m + 2 + 1 by omega, Finset.prod_range_succ,
        ih, Finset.prod_range_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

private lemma prod_neg_five_halves_shift (m : ℕ) :
    (∏ j ∈ Finset.range (m + 3), (-(5 / 2 : ℝ) + (j : ℝ))) =
      (-(15 / 8 : ℝ)) *
        (∏ j ∈ Finset.range m, ((1 / 2 : ℝ) + (j : ℝ))) := by
  induction m with
  | zero =>
      norm_num [Finset.prod_range_succ]
  | succ m ih =>
      rw [show m + 1 + 3 = m + 3 + 1 by omega, Finset.prod_range_succ,
        ih, Finset.prod_range_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

private lemma sqrt_coeff0_eq_shifted_half {n : ℕ} (hn : 1 ≤ n) :
    Ring.choose ((-(1 / 2 : ℝ)) + (n : ℕ) - 1) n =
      (-(1 : ℝ) / (2 * (n : ℝ))) *
        Ring.choose ((1 / 2 : ℝ) + ((n - 1 : ℕ) : ℝ) - 1) (n - 1) := by
  rcases n with _ | m
  · cases hn
  · have hfac : (((m + 1).factorial : ℕ) : ℝ) =
        ((m + 1 : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ) := by
      norm_num [Nat.factorial_succ]
    have hmfac_ne : ((m.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero m
    have hm1_ne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [choose_eq_prod_range_real, choose_eq_prod_range_real,
      show (m + 1 - 1 : ℕ) = m by omega]
    rw [prod_neg_half_shift, hfac]
    field_simp [hmfac_ne, hm1_ne]

private lemma sqrt_coeff1_eq_shifted_half {n : ℕ} (hn : 2 ≤ n) :
    Ring.choose ((-(3 / 2 : ℝ)) + (n : ℕ) - 1) n =
      (3 : ℝ) / (4 * (n : ℝ) * ((n - 1 : ℕ) : ℝ)) *
        Ring.choose ((1 / 2 : ℝ) + ((n - 2 : ℕ) : ℝ) - 1) (n - 2) := by
  rcases n with _ | n
  · cases hn
  rcases n with _ | m
  · omega
  · have hfac : (((m + 2).factorial : ℕ) : ℝ) =
        ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) *
          ((m.factorial : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]
      norm_num [Nat.cast_mul]
      ring
    have hmfac_ne : ((m.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero m
    have hm1_ne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hm2_ne : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [choose_eq_prod_range_real, choose_eq_prod_range_real,
      show (m + 2 - 2 : ℕ) = m by omega,
      show (m + 2 - 1 : ℕ) = m + 1 by omega]
    rw [prod_neg_three_halves_shift, hfac]
    field_simp [hmfac_ne, hm1_ne, hm2_ne]

private lemma sqrt_coeff2_eq_shifted_half {n : ℕ} (hn : 3 ≤ n) :
    Ring.choose ((-(5 / 2 : ℝ)) + (n : ℕ) - 1) n =
      (-(15 : ℝ)) / (8 * (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
          ((n - 2 : ℕ) : ℝ)) *
        Ring.choose ((1 / 2 : ℝ) + ((n - 3 : ℕ) : ℝ) - 1) (n - 3) := by
  rcases n with _ | n
  · cases hn
  rcases n with _ | n
  · omega
  rcases n with _ | m
  · omega
  · have hfac : (((m + 3).factorial : ℕ) : ℝ) =
        ((m + 3 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
          ((m + 1 : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
      norm_num [Nat.cast_mul]
      ring
    have hmfac_ne : ((m.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero m
    have hm1_ne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hm2_ne : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have hm3_ne : ((m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [choose_eq_prod_range_real, choose_eq_prod_range_real,
      show (m + 3 - 3 : ℕ) = m by omega,
      show (m + 3 - 2 : ℕ) = m + 1 by omega,
      show (m + 3 - 1 : ℕ) = m + 2 by omega]
    rw [prod_neg_five_halves_shift, hfac]
    field_simp [hmfac_ne, hm1_ne, hm2_ne, hm3_ne]

private lemma choose_two_real (a : ℝ) :
    Ring.choose a 2 = a * (a - 1) / 2 := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose a 2
  norm_num [descPochhammer, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_C, Polynomial.smeval_natCast] at h
  nlinarith

private lemma binomial_partialSum_three_real (a x : ℝ) :
    (binomialSeries ℝ a).partialSum 3 x =
      1 + a * x + (a * (a - 1) / 2) * x ^ 2 := by
  simp [FormalMultilinearSeries.partialSum, binomialSeries, Finset.sum_range_succ,
    choose_two_real]
  ring_nf

private lemma one_sub_rpow_sub_quadratic_isBigO (a : ℝ) :
    (fun x : ℝ =>
      (1 - x) ^ a - (1 - a * x + (a * (a - 1) / 2) * x ^ 2))
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := a)).isBigO_sub_partialSum_pow 3
  have hneg : Tendsto (fun x : ℝ => -x) (𝓝 0) (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.sub tendsto_id :
        Tendsto (fun x : ℝ => (0 : ℝ) - x) (𝓝 0) (𝓝 ((0 : ℝ) - 0)))
  have hcomp := h.comp_tendsto hneg
  refine hcomp.congr_left ?_ |>.congr_right ?_
  · intro x
    dsimp
    rw [binomial_partialSum_three_real]
    ring_nf
  · intro x
    dsimp
    rw [abs_neg]

private lemma one_sub_rpow_sub_linear_isLittleO (a : ℝ) :
    (fun x : ℝ => (1 - x) ^ a - 1 + a * x) =o[𝓝 0]
      (fun x : ℝ => x) := by
  have hlin : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
    simpa using
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))
  have hpow : HasDerivAt (fun x : ℝ => (1 - x) ^ a) (-a) 0 := by
    have h := hlin.rpow_const (p := a)
      (Or.inl (by norm_num : (1 : ℝ) - 0 ≠ 0))
    simpa using h
  have ho := hpow.isLittleO
  simpa [mul_comm, mul_left_comm, mul_assoc] using ho

private lemma inv_norm_sq_eq (n : ℕ) :
    ‖((n : ℝ)⁻¹)‖ ^ 2 = ((n : ℝ)⁻¹) ^ 2 := by
  rw [Real.norm_of_nonneg]
  positivity

private lemma inv_norm_cube_eq (n : ℕ) :
    ‖((n : ℝ)⁻¹)‖ ^ 3 = ((n : ℝ)⁻¹) ^ 3 := by
  rw [Real.norm_of_nonneg]
  positivity

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

private lemma pred_rpow_div_quadratic_isBigO (a : ℝ) :
    (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ a / (n : ℝ) -
        ((n : ℝ) ^ (a - 1) - a * (n : ℝ) ^ (a - 2) +
          (a * (a - 1) / 2) * (n : ℝ) ^ (a - 3)))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 4)) := by
  let H : ℝ → ℝ := fun x =>
    (1 - x) ^ a - (1 - a * x + (a * (a - 1) / 2) * x ^ 2)
  have hH : H =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
    simpa [H] using one_sub_rpow_sub_quadratic_isBigO a
  have hHinv : (fun n : ℕ => H ((n : ℝ)⁻¹)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) := by
    have hcomp := hH.comp_tendsto (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
    refine hcomp.congr_right ?_
    intro n
    change ‖((n : ℝ)⁻¹)‖ ^ 3 = (n : ℝ) ^ (-(3 : ℝ))
    rw [inv_norm_cube_eq n, Real.rpow_neg (Nat.cast_nonneg n)]
    norm_num
  have hp : (fun n : ℕ => (n : ℝ) ^ (a - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 1)) := isBigO_refl _ _
  have hprod := IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
    (a - 1) (-(3 : ℝ)) (a - 4) hp hHinv (by linarith)
  have heq : (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ a / (n : ℝ) -
        ((n : ℝ) ^ (a - 1) - a * (n : ℝ) ^ (a - 2) +
          (a * (a - 1) / 2) * (n : ℝ) ^ (a - 3))) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 1) * H ((n : ℝ)⁻¹)) := by
    refine eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
    let x : ℝ := n
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hn
    have hpred_pos_nat : 0 < n - 1 := by omega
    have hnpos : 0 < x := by dsimp [x]; exact_mod_cast hnpos_nat
    have hn1 : (1 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hn)
    have hcast_sub : ((n - 1 : ℕ) : ℝ) = x - 1 := by
      dsimp [x]
      norm_num [Nat.cast_sub (Nat.succ_le_of_lt hnpos_nat)]
    have hy_nonneg : 0 ≤ 1 - x⁻¹ := by
      have hinv_le : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      linarith
    have hmulbase : x * (1 - x⁻¹) = x - 1 := by
      field_simp [hnpos.ne']
    have hpowsub : ((n - 1 : ℕ) : ℝ) ^ a =
        x ^ a * (1 - x⁻¹) ^ a := by
      rw [hcast_sub, ← hmulbase]
      exact Real.mul_rpow hnpos.le hy_nonneg
    have hdivpow : ((n - 1 : ℕ) : ℝ) ^ a / x =
        x ^ (a - 1) * (1 - x⁻¹) ^ a := by
      rw [hpowsub]
      have hxpow : x ^ a / x = x ^ (a - 1) := by
        calc
          x ^ a / x = x ^ a * x⁻¹ := by rw [div_eq_mul_inv]
          _ = x ^ a * x ^ (-(1 : ℝ)) := by
                rw [Real.rpow_neg hnpos.le, Real.rpow_one]
          _ = x ^ (a + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
          _ = x ^ (a - 1) := by ring_nf
      rw [show x ^ a * (1 - x⁻¹) ^ a / x =
          (x ^ a / x) * (1 - x⁻¹) ^ a by ring]
      rw [hxpow]
    have hmul_inv : x ^ (a - 1) * x⁻¹ = x ^ (a - 2) := by
      calc
        x ^ (a - 1) * x⁻¹ =
            x ^ (a - 1) * x ^ (-(1 : ℝ)) := by
              rw [Real.rpow_neg hnpos.le, Real.rpow_one]
        _ = x ^ ((a - 1) + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
        _ = x ^ (a - 2) := by ring_nf
    have hmul_inv_sq : x ^ (a - 1) * x⁻¹ ^ 2 = x ^ (a - 3) := by
      calc
        x ^ (a - 1) * x⁻¹ ^ 2 =
            x ^ (a - 1) * x ^ (-(2 : ℝ)) := by
              rw [Real.rpow_neg hnpos.le]
              norm_num
        _ = x ^ ((a - 1) + (-(2 : ℝ))) := by rw [← Real.rpow_add hnpos]
        _ = x ^ (a - 3) := by ring_nf
    dsimp [H]
    change ((n - 1 : ℕ) : ℝ) ^ a / x -
        (x ^ (a - 1) - a * x ^ (a - 2) +
          (a * (a - 1) / 2) * x ^ (a - 3)) =
      x ^ (a - 1) *
        ((1 - x⁻¹) ^ a - (1 - a * x⁻¹ + (a * (a - 1) / 2) * x⁻¹ ^ 2))
    rw [hdivpow, ← hmul_inv, ← hmul_inv_sq]
    ring
  exact heq.trans_isBigO hprod

private lemma pred_rpow_div_linear_isLittleO (a : ℝ) :
    (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ a / (n : ℝ) -
        ((n : ℝ) ^ (a - 1) - a * (n : ℝ) ^ (a - 2)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
  let H : ℝ → ℝ := fun x => (1 - x) ^ a - 1 + a * x
  have hH : H =o[𝓝 0] (fun x : ℝ => x) := by
    simpa [H] using one_sub_rpow_sub_linear_isLittleO a
  have hHinv : (fun n : ℕ => H ((n : ℝ)⁻¹)) =o[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
    simpa using hH.comp_tendsto (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hprod :=
    (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (a - 1)) atTop).mul_isLittleO hHinv
  have hprod' : (fun n : ℕ => (n : ℝ) ^ (a - 1) * H ((n : ℝ)⁻¹))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
    refine hprod.trans_eventuallyEq ?_
    refine (rpow_mul_inv_eventually (a - 1)).trans ?_
    exact Eventually.of_forall fun n => by
      congr 1
      ring
  have heq : (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ a / (n : ℝ) -
        ((n : ℝ) ^ (a - 1) - a * (n : ℝ) ^ (a - 2))) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 1) * H ((n : ℝ)⁻¹)) := by
    refine eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
    let x : ℝ := n
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hn
    have hnpos : 0 < x := by dsimp [x]; exact_mod_cast hnpos_nat
    have hn1 : (1 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hn)
    have hcast_sub : ((n - 1 : ℕ) : ℝ) = x - 1 := by
      dsimp [x]
      norm_num [Nat.cast_sub (Nat.succ_le_of_lt hnpos_nat)]
    have hy_nonneg : 0 ≤ 1 - x⁻¹ := by
      have hinv_le : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      linarith
    have hmulbase : x * (1 - x⁻¹) = x - 1 := by
      field_simp [hnpos.ne']
    have hpowsub : ((n - 1 : ℕ) : ℝ) ^ a =
        x ^ a * (1 - x⁻¹) ^ a := by
      rw [hcast_sub, ← hmulbase]
      exact Real.mul_rpow hnpos.le hy_nonneg
    have hdivpow : ((n - 1 : ℕ) : ℝ) ^ a / x =
        x ^ (a - 1) * (1 - x⁻¹) ^ a := by
      rw [hpowsub]
      have hxpow : x ^ a / x = x ^ (a - 1) := by
        calc
          x ^ a / x = x ^ a * x⁻¹ := by rw [div_eq_mul_inv]
          _ = x ^ a * x ^ (-(1 : ℝ)) := by
                rw [Real.rpow_neg hnpos.le, Real.rpow_one]
          _ = x ^ (a + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
          _ = x ^ (a - 1) := by ring_nf
      rw [show x ^ a * (1 - x⁻¹) ^ a / x =
          (x ^ a / x) * (1 - x⁻¹) ^ a by ring]
      rw [hxpow]
    have hpowinv : x ^ (a - 1) * x⁻¹ = x ^ (a - 2) := by
      calc
        x ^ (a - 1) * x⁻¹ =
            x ^ (a - 1) * x ^ (-(1 : ℝ)) := by
              rw [Real.rpow_neg hnpos.le, Real.rpow_one]
        _ = x ^ ((a - 1) + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
        _ = x ^ (a - 2) := by ring_nf
    dsimp [H]
    change ((n - 1 : ℕ) : ℝ) ^ a / x - (x ^ (a - 1) - a * x ^ (a - 2)) =
      x ^ (a - 1) * ((1 - x⁻¹) ^ a - 1 + a * x⁻¹)
    rw [hdivpow, ← hpowinv]
    ring
  exact heq.trans_isLittleO hprod'

private lemma pred_rpow_div_leading_isLittleO (a : ℝ) :
    (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ a / (n : ℝ) - (n : ℝ) ^ (a - 1))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 1)) := by
  let K : ℕ → ℝ := fun n => (1 - (n : ℝ)⁻¹) ^ a - 1
  have hK : K =o[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    have hbase : Tendsto (fun n : ℕ => 1 - (n : ℝ)⁻¹) atTop
        (𝓝 (1 : ℝ)) := by simpa using hconst.sub hinv
    have hpow_raw : Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) ^ a) atTop
        (𝓝 ((1 : ℝ) ^ a)) :=
      hbase.rpow tendsto_const_nhds (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
    have hzero : Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) ^ a - 1) atTop
        (𝓝 0) := by simpa using hpow_raw.sub hconst
    exact (isLittleO_one_iff ℝ).mpr hzero
  have hprod :=
    (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (a - 1)) atTop).mul_isLittleO hK
  have heq : (fun n : ℕ =>
      ((n - 1 : ℕ) : ℝ) ^ a / (n : ℝ) - (n : ℝ) ^ (a - 1))
      =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 1) * K n) := by
    refine eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
    let x : ℝ := n
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hn
    have hnpos : 0 < x := by dsimp [x]; exact_mod_cast hnpos_nat
    have hn1 : (1 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hn)
    have hcast_sub : ((n - 1 : ℕ) : ℝ) = x - 1 := by
      dsimp [x]
      norm_num [Nat.cast_sub (Nat.succ_le_of_lt hnpos_nat)]
    have hy_nonneg : 0 ≤ 1 - x⁻¹ := by
      have hinv_le : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      linarith
    have hmulbase : x * (1 - x⁻¹) = x - 1 := by
      field_simp [hnpos.ne']
    have hpowsub : ((n - 1 : ℕ) : ℝ) ^ a =
        x ^ a * (1 - x⁻¹) ^ a := by
      rw [hcast_sub, ← hmulbase]
      exact Real.mul_rpow hnpos.le hy_nonneg
    have hdivpow : ((n - 1 : ℕ) : ℝ) ^ a / x =
        x ^ (a - 1) * (1 - x⁻¹) ^ a := by
      rw [hpowsub]
      have hxpow : x ^ a / x = x ^ (a - 1) := by
        calc
          x ^ a / x = x ^ a * x⁻¹ := by rw [div_eq_mul_inv]
          _ = x ^ a * x ^ (-(1 : ℝ)) := by
                rw [Real.rpow_neg hnpos.le, Real.rpow_one]
          _ = x ^ (a + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
          _ = x ^ (a - 1) := by ring_nf
      rw [show x ^ a * (1 - x⁻¹) ^ a / x =
          (x ^ a / x) * (1 - x⁻¹) ^ a by ring]
      rw [hxpow]
    dsimp [K]
    change ((n - 1 : ℕ) : ℝ) ^ a / x - x ^ (a - 1) =
      x ^ (a - 1) * ((1 - x⁻¹) ^ a - 1)
    rw [hdivpow]
    ring
  have hprod' : (fun n : ℕ => (n : ℝ) ^ (a - 1) * K n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 1)) := by
    simpa using hprod
  exact heq.trans_isLittleO hprod'

private lemma two_shift_kernel_linear_isLittleO (a : ℝ) :
    (fun x : ℝ =>
      (1 - 2 * x) ^ a * (1 - x) ^ (-(1 : ℝ)) -
        (1 + (1 - 2 * a) * x)) =o[𝓝 0] (fun x : ℝ => x) := by
  let u : ℝ → ℝ := fun x => (1 - 2 * x) ^ a
  let v : ℝ → ℝ := fun x => (1 - x) ^ (-(1 : ℝ))
  have hu_base : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) 0 := by
    simpa using
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
        ((hasDerivAt_id (0 : ℝ)).const_mul 2)
  have hu : HasDerivAt u (-2 * a) 0 := by
    have h := hu_base.rpow_const (p := a)
      (Or.inl (by norm_num : (1 : ℝ) - 2 * 0 ≠ 0))
    simpa [u, mul_comm, mul_left_comm, mul_assoc] using h
  have hv_base : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
    simpa using
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))
  have hv : HasDerivAt v 1 0 := by
    have h := hv_base.rpow_const (p := (-(1 : ℝ)))
      (Or.inl (by norm_num : (1 : ℝ) - 0 ≠ 0))
    simpa [v] using h
  have hprod : HasDerivAt (fun x : ℝ => u x * v x) (1 - 2 * a) 0 := by
    convert hu.mul hv using 1 <;> simp [u, v]
    ring
  have ho := hprod.isLittleO
  refine (ho.congr_left ?_).congr_right ?_
  · intro x
    simp [u, v]
    ring_nf
  · intro x
    ring

private lemma pred2_rpow_div_linear_isLittleO (a : ℝ) :
    (fun n : ℕ =>
      ((n - 2 : ℕ) : ℝ) ^ a / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) -
        ((n : ℝ) ^ (a - 2) + (1 - 2 * a) * (n : ℝ) ^ (a - 3)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 3)) := by
  let K : ℝ → ℝ := fun x =>
    (1 - 2 * x) ^ a * (1 - x) ^ (-(1 : ℝ)) - (1 + (1 - 2 * a) * x)
  have hK : K =o[𝓝 0] (fun x : ℝ => x) := by
    simpa [K] using two_shift_kernel_linear_isLittleO a
  have hKinv : (fun n : ℕ => K ((n : ℝ)⁻¹)) =o[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
    simpa using hK.comp_tendsto (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hprod :=
    (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (a - 2)) atTop).mul_isLittleO hKinv
  have hprod' : (fun n : ℕ => (n : ℝ) ^ (a - 2) * K ((n : ℝ)⁻¹))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 3)) := by
    refine hprod.trans_eventuallyEq ?_
    refine (rpow_mul_inv_eventually (a - 2)).trans ?_
    exact Eventually.of_forall fun n => by
      congr 1
      ring
  have heq : (fun n : ℕ =>
      ((n - 2 : ℕ) : ℝ) ^ a / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) -
        ((n : ℝ) ^ (a - 2) + (1 - 2 * a) * (n : ℝ) ^ (a - 3))) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 2) * K ((n : ℝ)⁻¹)) := by
    refine eventually_atTop.mpr ⟨3, fun n hn => ?_⟩
    let x : ℝ := n
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (3 : ℕ)) hn
    have hnpos : 0 < x := by dsimp [x]; exact_mod_cast hnpos_nat
    have hn1pos_nat : 0 < n - 1 := by omega
    have hn2pos_nat : 0 < n - 2 := by omega
    have hcast1 : ((n - 1 : ℕ) : ℝ) = x - 1 := by
      dsimp [x]
      norm_num [Nat.cast_sub (Nat.succ_le_of_lt hnpos_nat)]
    have hcast2 : ((n - 2 : ℕ) : ℝ) = x - 2 := by
      dsimp [x]
      norm_num [Nat.cast_sub (by omega : 2 ≤ n)]
    have hy1_nonneg : 0 ≤ 1 - x⁻¹ := by
      have hn1 : (1 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) hn)
      have hinv_le : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      linarith
    have hy2_nonneg : 0 ≤ 1 - 2 * x⁻¹ := by
      have hn2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast (le_trans (by norm_num : 2 ≤ 3) hn)
      have hle : 2 * x⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact div_le_one_of_le₀ hn2 (by positivity)
      linarith
    have hmul1 : x * (1 - x⁻¹) = x - 1 := by field_simp [hnpos.ne']
    have hmul2 : x * (1 - 2 * x⁻¹) = x - 2 := by field_simp [hnpos.ne']
    have hpowsub : ((n - 2 : ℕ) : ℝ) ^ a =
        x ^ a * (1 - 2 * x⁻¹) ^ a := by
      rw [hcast2, ← hmul2]
      exact Real.mul_rpow hnpos.le hy2_nonneg
    have hden : x * ((n - 1 : ℕ) : ℝ) =
        x ^ 2 * (1 - x⁻¹) := by
      rw [hcast1, ← hmul1]
      ring
    have hdivpow : ((n - 2 : ℕ) : ℝ) ^ a / (x * ((n - 1 : ℕ) : ℝ)) =
        x ^ (a - 2) * ((1 - 2 * x⁻¹) ^ a * (1 - x⁻¹) ^ (-(1 : ℝ))) := by
      rw [hpowsub, hden]
      have hx2pos : 0 < x ^ 2 := by positivity
      have hy1pos : 0 < 1 - x⁻¹ := by
        have hn2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast (le_trans (by norm_num : 2 ≤ 3) hn)
        have hlt : x⁻¹ < 1 := by
          exact inv_lt_one_of_one_lt₀ (by linarith : (1 : ℝ) < x)
        linarith
      have hxpow : x ^ a / x ^ 2 = x ^ (a - 2) := by
        calc
          x ^ a / x ^ 2 = x ^ a * (x ^ 2)⁻¹ := by rw [div_eq_mul_inv]
          _ = x ^ a * x ^ (-(2 : ℝ)) := by
                rw [Real.rpow_neg (le_of_lt hnpos)]
                norm_num
          _ = x ^ (a + (-(2 : ℝ))) := by rw [← Real.rpow_add hnpos]
          _ = x ^ (a - 2) := by ring_nf
      rw [show x ^ a * (1 - 2 * x⁻¹) ^ a / (x ^ 2 * (1 - x⁻¹)) =
          (x ^ a / x ^ 2) * ((1 - 2 * x⁻¹) ^ a * (1 - x⁻¹)⁻¹) by
            field_simp [ne_of_gt hx2pos, ne_of_gt hy1pos]
            ]
      rw [hxpow, Real.rpow_neg hy1_nonneg, Real.rpow_one]
    have hpowinv : x ^ (a - 2) * x⁻¹ = x ^ (a - 3) := by
      calc
        x ^ (a - 2) * x⁻¹ =
            x ^ (a - 2) * x ^ (-(1 : ℝ)) := by
              rw [Real.rpow_neg hnpos.le, Real.rpow_one]
        _ = x ^ ((a - 2) + (-(1 : ℝ))) := by rw [← Real.rpow_add hnpos]
        _ = x ^ (a - 3) := by ring_nf
    dsimp [K]
    change ((n - 2 : ℕ) : ℝ) ^ a / (x * ((n - 1 : ℕ) : ℝ)) -
        (x ^ (a - 2) + (1 - 2 * a) * x ^ (a - 3)) =
      x ^ (a - 2) *
        ((1 - 2 * x⁻¹) ^ a * (1 - x⁻¹) ^ (-(1 : ℝ)) -
          (1 + (1 - 2 * a) * x⁻¹))
    rw [hdivpow, ← hpowinv]
    ring
  exact heq.trans_isLittleO hprod'

private lemma pred2_rpow_div_leading_isLittleO (a : ℝ) :
    (fun n : ℕ =>
      ((n - 2 : ℕ) : ℝ) ^ a / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) -
        (n : ℝ) ^ (a - 2))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
  have hlin := pred2_rpow_div_linear_isLittleO a
  have hsmall : (fun n : ℕ => (1 - 2 * a) * (n : ℝ) ^ (a - 3))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
    convert (rpow_sub_one_isLittleO (a - 2)).const_mul_left (1 - 2 * a) using 1
    ext n
    congr 2
    ring
  have hpow_small : (fun n : ℕ => (n : ℝ) ^ (a - 3))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) := by
    convert rpow_sub_one_isLittleO (a - 2) using 1
    ext n
    congr 1
    ring
  have hlin' : (fun n : ℕ =>
      ((n - 2 : ℕ) : ℝ) ^ a / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) -
        ((n : ℝ) ^ (a - 2) + (1 - 2 * a) * (n : ℝ) ^ (a - 3)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 2)) :=
    hlin.trans hpow_small
  have hsum := hlin'.add hsmall
  refine hsum.congr_left ?_
  intro n
  ring

private lemma pred3_rpow_div_leading_isLittleO (a : ℝ) :
    (fun n : ℕ =>
      ((n - 3 : ℕ) : ℝ) ^ a /
          ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)) -
        (n : ℝ) ^ (a - 3))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 3)) := by
  let K : ℕ → ℝ := fun n =>
    (1 - 3 * (n : ℝ)⁻¹) ^ a *
        (1 - (n : ℝ)⁻¹) ^ (-(1 : ℝ)) *
          (1 - 2 * (n : ℝ)⁻¹) ^ (-(1 : ℝ)) - 1
  have hK : K =o[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hbase3 : Tendsto (fun n : ℕ => 1 - 3 * (n : ℝ)⁻¹) atTop
        (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
    have hbase1 : Tendsto (fun n : ℕ => 1 - (n : ℝ)⁻¹) atTop
        (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub hinv
    have hbase2 : Tendsto (fun n : ℕ => 1 - 2 * (n : ℝ)⁻¹) atTop
        (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
    have hpow3 : Tendsto (fun n : ℕ => (1 - 3 * (n : ℝ)⁻¹) ^ a) atTop
        (𝓝 ((1 : ℝ) ^ a)) :=
      hbase3.rpow (tendsto_const_nhds (x := a))
        (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
    have hpow1 : Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) ^ (-(1 : ℝ))) atTop
        (𝓝 ((1 : ℝ) ^ (-(1 : ℝ)))) :=
      hbase1.rpow (tendsto_const_nhds (x := (-(1 : ℝ))))
        (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
    have hpow2 : Tendsto (fun n : ℕ => (1 - 2 * (n : ℝ)⁻¹) ^ (-(1 : ℝ))) atTop
        (𝓝 ((1 : ℝ) ^ (-(1 : ℝ)))) :=
      hbase2.rpow (tendsto_const_nhds (x := (-(1 : ℝ))))
        (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
    have hprod : Tendsto
        (fun n : ℕ =>
          (1 - 3 * (n : ℝ)⁻¹) ^ a *
              (1 - (n : ℝ)⁻¹) ^ (-(1 : ℝ)) *
                (1 - 2 * (n : ℝ)⁻¹) ^ (-(1 : ℝ))) atTop
        (𝓝 (1 : ℝ)) := by
      simpa using (hpow3.mul hpow1).mul hpow2
    have hzero : Tendsto K atTop (𝓝 0) := by
      have hsub : Tendsto
          (fun n : ℕ =>
            (1 - 3 * (n : ℝ)⁻¹) ^ a *
                (1 - (n : ℝ)⁻¹) ^ (-(1 : ℝ)) *
                  (1 - 2 * (n : ℝ)⁻¹) ^ (-(1 : ℝ)) - (1 : ℝ))
          atTop (𝓝 (1 - (1 : ℝ))) :=
        hprod.sub (tendsto_const_nhds (x := (1 : ℝ)))
      simpa [K] using hsub
    exact (isLittleO_one_iff ℝ).mpr hzero
  have hprod :=
    (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (a - 3)) atTop).mul_isLittleO hK
  have heq : (fun n : ℕ =>
      ((n - 3 : ℕ) : ℝ) ^ a /
          ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)) -
        (n : ℝ) ^ (a - 3))
      =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 3) * K n) := by
    refine eventually_atTop.mpr ⟨4, fun n hn => ?_⟩
    let x : ℝ := n
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (4 : ℕ)) hn
    have hnpos : 0 < x := by dsimp [x]; exact_mod_cast hnpos_nat
    have hcast1 : ((n - 1 : ℕ) : ℝ) = x - 1 := by
      dsimp [x]
      norm_num [Nat.cast_sub (Nat.succ_le_of_lt hnpos_nat)]
    have hcast2 : ((n - 2 : ℕ) : ℝ) = x - 2 := by
      dsimp [x]
      norm_num [Nat.cast_sub (by omega : 2 ≤ n)]
    have hcast3 : ((n - 3 : ℕ) : ℝ) = x - 3 := by
      dsimp [x]
      norm_num [Nat.cast_sub (by omega : 3 ≤ n)]
    have hy1pos : 0 < 1 - x⁻¹ := by
      have hlt : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by dsimp [x]; exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < (4 : ℕ)) hn))
      linarith
    have hy2pos : 0 < 1 - 2 * x⁻¹ := by
      have hn2 : (2 : ℝ) < x := by dsimp [x]; exact_mod_cast (lt_of_lt_of_le (by norm_num : 2 < (4 : ℕ)) hn)
      have hlt : 2 * x⁻¹ < 1 := by
        rw [← div_eq_mul_inv]
        exact (div_lt_one (by positivity : 0 < x)).mpr hn2
      linarith
    have hy3_nonneg : 0 ≤ 1 - 3 * x⁻¹ := by
      have hn3 : (3 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast (le_trans (by norm_num : 3 ≤ 4) hn)
      have hle : 3 * x⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact div_le_one_of_le₀ hn3 (by positivity)
      linarith
    have hmul1 : x * (1 - x⁻¹) = x - 1 := by field_simp [hnpos.ne']
    have hmul2 : x * (1 - 2 * x⁻¹) = x - 2 := by field_simp [hnpos.ne']
    have hmul3 : x * (1 - 3 * x⁻¹) = x - 3 := by field_simp [hnpos.ne']
    have hpowsub : ((n - 3 : ℕ) : ℝ) ^ a =
        x ^ a * (1 - 3 * x⁻¹) ^ a := by
      rw [hcast3, ← hmul3]
      exact Real.mul_rpow hnpos.le hy3_nonneg
    have hden :
        x * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) =
          x ^ 3 * ((1 - x⁻¹) * (1 - 2 * x⁻¹)) := by
      rw [hcast1, hcast2, ← hmul1, ← hmul2]
      ring
    have hdivpow :
        ((n - 3 : ℕ) : ℝ) ^ a /
            (x * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)) =
          x ^ (a - 3) *
            ((1 - 3 * x⁻¹) ^ a *
              (1 - x⁻¹) ^ (-(1 : ℝ)) *
                (1 - 2 * x⁻¹) ^ (-(1 : ℝ))) := by
      rw [hpowsub, hden]
      have hx3pos : 0 < x ^ 3 := by positivity
      have hxpow : x ^ a / x ^ 3 = x ^ (a - 3) := by
        calc
          x ^ a / x ^ 3 = x ^ a * (x ^ 3)⁻¹ := by rw [div_eq_mul_inv]
          _ = x ^ a * x ^ (-(3 : ℝ)) := by
                rw [Real.rpow_neg (le_of_lt hnpos)]
                norm_num
          _ = x ^ (a + (-(3 : ℝ))) := by rw [← Real.rpow_add hnpos]
          _ = x ^ (a - 3) := by ring_nf
      rw [show x ^ a * (1 - 3 * x⁻¹) ^ a /
            (x ^ 3 * ((1 - x⁻¹) * (1 - 2 * x⁻¹))) =
          (x ^ a / x ^ 3) *
            ((1 - 3 * x⁻¹) ^ a * (1 - x⁻¹)⁻¹ * (1 - 2 * x⁻¹)⁻¹) by
            field_simp [ne_of_gt hx3pos, ne_of_gt hy1pos, ne_of_gt hy2pos]
            ]
      rw [hxpow, Real.rpow_neg hy1pos.le, Real.rpow_one,
        Real.rpow_neg hy2pos.le, Real.rpow_one]
    dsimp [K]
    change ((n - 3 : ℕ) : ℝ) ^ a /
          (x * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)) -
        x ^ (a - 3) =
      x ^ (a - 3) *
        ((1 - 3 * x⁻¹) ^ a * (1 - x⁻¹) ^ (-(1 : ℝ)) *
            (1 - 2 * x⁻¹) ^ (-(1 : ℝ)) - 1)
    rw [hdivpow]
    ring
  have hprod' : (fun n : ℕ => (n : ℝ) ^ (a - 3) * K n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (a - 3)) := by
    simpa using hprod
  exact heq.trans_isLittleO hprod'

private lemma rpow_sub_two_isLittleO (a : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ (a - 2)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) := by
  have h1raw := rpow_sub_one_isLittleO (a - 1)
  have h1 : (fun n : ℕ => (n : ℝ) ^ (a - 2)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - 1)) := by
    convert h1raw using 1
    ext n
    congr 1
    ring
  have h2 := rpow_sub_one_isLittleO a
  exact h1.trans h2

private lemma inv_nat_isBigO_rpow_neg_one :
    (fun n : ℕ => (n : ℝ)⁻¹) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  have heq : (fun n : ℕ => (n : ℝ)⁻¹) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
    symm
    change (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ)⁻¹
    rw [Real.rpow_neg hnpos.le, Real.rpow_one]
  exact heq.trans_isBigO (isBigO_refl _ _)

private lemma inv_nat_sub_isBigO_rpow_neg_one (k : ℕ) :
    (fun n : ℕ => ((n - k : ℕ) : ℝ)⁻¹) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  have hsub := nat_sub_const_rpow_isBigO k (-(1 : ℝ))
  have heq : (fun n : ℕ => ((n - k : ℕ) : ℝ)⁻¹) =ᶠ[atTop]
      (fun n : ℕ => ((n - k : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
    refine eventually_atTop.mpr ⟨k + 1, fun n hn => ?_⟩
    have hpos_nat : 0 < n - k := by omega
    have hpos : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast hpos_nat
    symm
    change ((n - k : ℕ) : ℝ) ^ (-(1 : ℝ)) = ((n - k : ℕ) : ℝ)⁻¹
    rw [Real.rpow_neg hpos.le, Real.rpow_one]
  exact heq.trans_isBigO hsub

private lemma half_error_shift_isBigO (k : ℕ) :
    (fun n : ℕ =>
      Ring.choose ((1 / 2 : ℝ) + ((n - k : ℕ) : ℝ) - 1) (n - k) -
        sqrtHalfThirdModel (n - k))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hcomp := sqrt_half_modelCoeff_thirdOrder.comp_tendsto
    (Filter.tendsto_sub_atTop_nat k)
  have hsub := nat_sub_const_rpow_isBigO k (-(7 / 2 : ℝ))
  exact hcomp.trans hsub

private lemma sqrt_coeff0_error_isLittleO :
    (fun n : ℕ =>
      (-(1 : ℝ) / (2 * (n : ℝ))) *
        (Ring.choose ((1 / 2 : ℝ) + ((n - 1 : ℕ) : ℝ) - 1) (n - 1) -
          sqrtHalfThirdModel (n - 1)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hfac : (fun n : ℕ => (-(1 : ℝ) / (2 * (n : ℝ))))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
    have h := inv_nat_isBigO_rpow_neg_one.const_mul_left (-(1 / 2 : ℝ))
    have heq : (fun n : ℕ => (-(1 : ℝ) / (2 * (n : ℝ)))) =ᶠ[atTop]
        (fun n : ℕ => -(1 / 2 : ℝ) * (n : ℝ)⁻¹) := by
      refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
      have hnne : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn))
      field_simp [hnne]
    exact heq.trans_isBigO h
  have herr := half_error_shift_isBigO 1
  have hmul := IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
    (-(1 : ℝ)) (-(7 / 2 : ℝ)) (-(9 / 2 : ℝ)) hfac herr (by norm_num)
  have hsmall : (fun n : ℕ => (n : ℝ) ^ (-(9 / 2 : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert rpow_sub_one_isLittleO (-(7 / 2 : ℝ)) using 1
    ext n
    congr 1
    ring
  exact hmul.trans_isLittleO hsmall

private lemma sqrt_coeff0_model_shift :
    (fun n : ℕ =>
      (-(1 : ℝ) / (2 * (n : ℝ))) * sqrtHalfThirdModel (n - 1) -
        sqrtModel0Third n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have h0O := pred_rpow_div_quadratic_isBigO (-(1 / 2 : ℝ))
  have h0small : (fun n : ℕ => (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 4))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert rpow_sub_one_isLittleO (-(7 / 2 : ℝ)) using 1
    ext n
    congr 1
    ring
  have h0 := (h0O.trans_isLittleO h0small).const_mul_left
    (-(1 / 2 : ℝ) * sqrtHalfModel0)
  have h1raw := (pred_rpow_div_linear_isLittleO (-(3 / 2 : ℝ))).const_mul_left
    (-(1 / 2 : ℝ) * sqrtHalfModel1)
  have h1 : (fun x : ℕ =>
      (-(1 / 2 : ℝ) * sqrtHalfModel1) *
        (((x - 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) / (x : ℝ) -
          ((x : ℝ) ^ (-(5 / 2 : ℝ)) +
            (3 / 2 : ℝ) * (x : ℝ) ^ (-(7 / 2 : ℝ)))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert h1raw using 1
    · ext n
      congr 3 <;> ring
    · ext n
      congr 1
      ring
  have h2raw := (pred_rpow_div_leading_isLittleO (-(5 / 2 : ℝ))).const_mul_left
    (-(1 / 2 : ℝ) * sqrtHalfModel2)
  have h2 : (fun x : ℕ =>
      (-(1 / 2 : ℝ) * sqrtHalfModel2) *
        (((x - 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) / (x : ℝ) -
          (x : ℝ) ^ (-(7 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert h2raw using 1
    · ext n
      congr 2
      ring
    · ext n
      congr 1
      ring
  have hsum := (h0.add h1).add h2
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 2] with n hn
  unfold sqrtHalfThirdModel sqrtHalfModel0 sqrtHalfModel1 sqrtHalfModel2 sqrtModel0Third
  norm_num
  ring_nf

private lemma sqrt_modelCoeff0_thirdOrder :
    (fun n : ℕ =>
      Ring.choose ((-(1 / 2 : ℝ)) + (n : ℕ) - 1) n - sqrtModel0Third n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hsum := sqrt_coeff0_error_isLittleO.add sqrt_coeff0_model_shift
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [sqrt_coeff0_eq_shifted_half hn]
  ring

private lemma inv_nat_mul_pred_isBigO_rpow_neg_two :
    (fun n : ℕ => ((n : ℝ)⁻¹ * ((n - 1 : ℕ) : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := by
  exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
    (-(1 : ℝ)) (-(1 : ℝ)) (-(2 : ℝ))
    inv_nat_isBigO_rpow_neg_one (inv_nat_sub_isBigO_rpow_neg_one 1) (by norm_num)

private lemma inv_nat_mul_pred_two_isBigO_rpow_neg_three :
    (fun n : ℕ =>
      (n : ℝ)⁻¹ * ((n - 1 : ℕ) : ℝ)⁻¹ * ((n - 2 : ℕ) : ℝ)⁻¹)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) := by
  have h12 := inv_nat_mul_pred_isBigO_rpow_neg_two
  exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
    (-(2 : ℝ)) (-(1 : ℝ)) (-(3 : ℝ))
    h12 (inv_nat_sub_isBigO_rpow_neg_one 2) (by norm_num)

private lemma sqrt_coeff1_factor_isBigO :
    (fun n : ℕ => (3 : ℝ) / (4 * (n : ℝ) * ((n - 1 : ℕ) : ℝ)))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := by
  have h := inv_nat_mul_pred_isBigO_rpow_neg_two.const_mul_left (3 / 4 : ℝ)
  have heq : (fun n : ℕ => (3 : ℝ) / (4 * (n : ℝ) * ((n - 1 : ℕ) : ℝ))) =ᶠ[atTop]
      (fun n : ℕ => (3 / 4 : ℝ) * ((n : ℝ)⁻¹ * ((n - 1 : ℕ) : ℝ)⁻¹)) := by
    refine eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
    have hnne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hn))
    have hpred_ne : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      have hpos : 0 < n - 1 := by omega
      exact_mod_cast Nat.ne_of_gt hpos
    field_simp [hnne, hpred_ne]
  exact heq.trans_isBigO h

private lemma sqrt_coeff2_factor_isBigO :
    (fun n : ℕ =>
      (-(15 : ℝ)) / (8 * (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
        ((n - 2 : ℕ) : ℝ)))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) := by
  have h := inv_nat_mul_pred_two_isBigO_rpow_neg_three.const_mul_left (-(15 / 8 : ℝ))
  have heq : (fun n : ℕ =>
      (-(15 : ℝ)) / (8 * (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
        ((n - 2 : ℕ) : ℝ))) =ᶠ[atTop]
      (fun n : ℕ =>
        (-(15 / 8 : ℝ)) *
          ((n : ℝ)⁻¹ * ((n - 1 : ℕ) : ℝ)⁻¹ * ((n - 2 : ℕ) : ℝ)⁻¹)) := by
    refine eventually_atTop.mpr ⟨3, fun n hn => ?_⟩
    have hnne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < (3 : ℕ)) hn))
    have hpred1_ne : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      have hpos : 0 < n - 1 := by omega
      exact_mod_cast Nat.ne_of_gt hpos
    have hpred2_ne : ((n - 2 : ℕ) : ℝ) ≠ 0 := by
      have hpos : 0 < n - 2 := by omega
      exact_mod_cast Nat.ne_of_gt hpos
    field_simp [hnne, hpred1_ne, hpred2_ne]
  exact heq.trans_isBigO h

private lemma sqrt_coeff1_error_isLittleO :
    (fun n : ℕ =>
      ((3 : ℝ) / (4 * (n : ℝ) * ((n - 1 : ℕ) : ℝ))) *
        (Ring.choose ((1 / 2 : ℝ) + ((n - 2 : ℕ) : ℝ) - 1) (n - 2) -
          sqrtHalfThirdModel (n - 2)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have herr := half_error_shift_isBigO 2
  have hmul := IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
    (-(2 : ℝ)) (-(7 / 2 : ℝ)) (-(11 / 2 : ℝ))
    sqrt_coeff1_factor_isBigO herr (by norm_num)
  have hsmall : (fun n : ℕ => (n : ℝ) ^ (-(11 / 2 : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    have h1 := rpow_sub_two_isLittleO (-(7 / 2 : ℝ))
    convert h1 using 1
    ext n
    congr 1
    ring
  exact hmul.trans_isLittleO hsmall

private lemma pred2_value_neg_five_halves_isLittleO :
    (fun n : ℕ =>
      ((n - 2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) /
        ((n : ℝ) * ((n - 1 : ℕ) : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hdiffraw := pred2_rpow_div_leading_isLittleO (-(5 / 2 : ℝ))
  have hpow_small : (fun n : ℕ => (n : ℝ) ^ (-(9 / 2 : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert rpow_sub_one_isLittleO (-(7 / 2 : ℝ)) using 1
    ext n
    congr 1
    ring
  have hdiff : (fun n : ℕ =>
      ((n - 2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) /
          ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) -
        (n : ℝ) ^ (-(9 / 2 : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    have hdiffraw' : (fun n : ℕ =>
        ((n - 2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) /
            ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) -
          (n : ℝ) ^ (-(9 / 2 : ℝ)))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(9 / 2 : ℝ))) := by
      convert hdiffraw using 1
      · ext n
        congr 2
        ring
      · ext n
        congr 1
        ring
    exact hdiffraw'.trans hpow_small
  have hsum := hdiff.add hpow_small
  refine hsum.congr_left ?_
  intro n
  ring

private lemma sqrt_coeff1_model_shift :
    (fun n : ℕ =>
      ((3 : ℝ) / (4 * (n : ℝ) * ((n - 1 : ℕ) : ℝ))) *
          sqrtHalfThirdModel (n - 2) -
        sqrtModel1Third n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have h0raw := (pred2_rpow_div_linear_isLittleO (-(1 / 2 : ℝ))).const_mul_left
    ((3 / 4 : ℝ) * sqrtHalfModel0)
  have h0 : (fun x : ℕ =>
      ((3 / 4 : ℝ) * sqrtHalfModel0) *
        ((((x - 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) /
            ((x : ℝ) * ((x - 1 : ℕ) : ℝ))) -
          ((x : ℝ) ^ (-(5 / 2 : ℝ)) +
            (2 : ℝ) * (x : ℝ) ^ (-(7 / 2 : ℝ)))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert h0raw using 1
    · ext n
      congr 3 <;> ring
    · ext n
      congr 1
      ring
  have h1raw := (pred2_rpow_div_leading_isLittleO (-(3 / 2 : ℝ))).const_mul_left
    ((3 / 4 : ℝ) * sqrtHalfModel1)
  have h1 : (fun x : ℕ =>
      ((3 / 4 : ℝ) * sqrtHalfModel1) *
        ((((x - 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) /
            ((x : ℝ) * ((x - 1 : ℕ) : ℝ))) -
          (x : ℝ) ^ (-(7 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert h1raw using 1
    · ext n
      congr 2
      ring
    · ext n
      congr 1
      ring
  have h2 := pred2_value_neg_five_halves_isLittleO.const_mul_left
    ((3 / 4 : ℝ) * sqrtHalfModel2)
  have hsum := (h0.add h1).add h2
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 3] with n hn
  unfold sqrtHalfThirdModel sqrtHalfModel0 sqrtHalfModel1 sqrtHalfModel2 sqrtModel1Third
  norm_num
  ring_nf

private lemma sqrt_modelCoeff1_thirdOrder :
    (fun n : ℕ =>
      Ring.choose ((-(3 / 2 : ℝ)) + (n : ℕ) - 1) n - sqrtModel1Third n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hsum := sqrt_coeff1_error_isLittleO.add sqrt_coeff1_model_shift
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [sqrt_coeff1_eq_shifted_half hn]
  ring

private lemma sqrt_coeff2_error_isLittleO :
    (fun n : ℕ =>
      ((-(15 : ℝ)) / (8 * (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
          ((n - 2 : ℕ) : ℝ))) *
        (Ring.choose ((1 / 2 : ℝ) + ((n - 3 : ℕ) : ℝ) - 1) (n - 3) -
          sqrtHalfThirdModel (n - 3)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have herr := half_error_shift_isBigO 3
  have hmul := IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
    (-(3 : ℝ)) (-(7 / 2 : ℝ)) (-(13 / 2 : ℝ))
    sqrt_coeff2_factor_isBigO herr (by norm_num)
  have hsmall : (fun n : ℕ => (n : ℝ) ^ (-(13 / 2 : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    have h1 : (fun n : ℕ => (n : ℝ) ^ (-(13 / 2 : ℝ)))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(9 / 2 : ℝ))) := by
      convert rpow_sub_two_isLittleO (-(9 / 2 : ℝ)) using 1
      ext n
      congr 1
      ring
    have h2 : (fun n : ℕ => (n : ℝ) ^ (-(9 / 2 : ℝ)))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
      convert rpow_sub_one_isLittleO (-(7 / 2 : ℝ)) using 1
      ext n
      congr 1
      ring
    exact h1.trans h2
  exact hmul.trans_isLittleO hsmall

private lemma pred3_value_neg_three_halves_isLittleO :
    (fun n : ℕ =>
      ((n - 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) /
        ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hdiffraw := pred3_rpow_div_leading_isLittleO (-(3 / 2 : ℝ))
  have hpow_small : (fun n : ℕ => (n : ℝ) ^ (-(9 / 2 : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert rpow_sub_one_isLittleO (-(7 / 2 : ℝ)) using 1
    ext n
    congr 1
    ring
  have hdiff : (fun n : ℕ =>
      ((n - 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) /
          ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)) -
        (n : ℝ) ^ (-(9 / 2 : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    have hdiffraw' : (fun n : ℕ =>
        ((n - 3 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) /
            ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)) -
          (n : ℝ) ^ (-(9 / 2 : ℝ)))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(9 / 2 : ℝ))) := by
      convert hdiffraw using 1
      · ext n
        congr 2
        ring
      · ext n
        congr 1
        ring
    exact hdiffraw'.trans hpow_small
  have hsum := hdiff.add hpow_small
  refine hsum.congr_left ?_
  intro n
  ring

private lemma pred3_value_neg_five_halves_isLittleO :
    (fun n : ℕ =>
      ((n - 3 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) /
        ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hdiffraw := pred3_rpow_div_leading_isLittleO (-(5 / 2 : ℝ))
  have hpow_small : (fun n : ℕ => (n : ℝ) ^ (-(11 / 2 : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    have h := rpow_sub_two_isLittleO (-(7 / 2 : ℝ))
    convert h using 1
    ext n
    congr 1
    ring
  have hdiff : (fun n : ℕ =>
      ((n - 3 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) /
          ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)) -
        (n : ℝ) ^ (-(11 / 2 : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    have hdiffraw' : (fun n : ℕ =>
        ((n - 3 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) /
            ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ)) -
          (n : ℝ) ^ (-(11 / 2 : ℝ)))
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(11 / 2 : ℝ))) := by
      convert hdiffraw using 1
      · ext n
        congr 2
        ring
      · ext n
        congr 1
        ring
    exact hdiffraw'.trans hpow_small
  have hsum := hdiff.add hpow_small
  refine hsum.congr_left ?_
  intro n
  ring

private lemma sqrt_coeff2_model_shift :
    (fun n : ℕ =>
      ((-(15 : ℝ)) / (8 * (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
          ((n - 2 : ℕ) : ℝ))) *
          sqrtHalfThirdModel (n - 3) -
        sqrtModel2Third n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have h0raw := (pred3_rpow_div_leading_isLittleO (-(1 / 2 : ℝ))).const_mul_left
    (-(15 / 8 : ℝ) * sqrtHalfModel0)
  have h0 : (fun x : ℕ =>
      (-(15 / 8 : ℝ) * sqrtHalfModel0) *
        ((((x - 3 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) /
            ((x : ℝ) * ((x - 1 : ℕ) : ℝ) * ((x - 2 : ℕ) : ℝ))) -
          (x : ℝ) ^ (-(7 / 2 : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert h0raw using 1
    · ext n
      congr 2
      ring
    · ext n
      congr 1
      ring
  have h1 := pred3_value_neg_three_halves_isLittleO.const_mul_left
    (-(15 / 8 : ℝ) * sqrtHalfModel1)
  have h2 := pred3_value_neg_five_halves_isLittleO.const_mul_left
    (-(15 / 8 : ℝ) * sqrtHalfModel2)
  have hsum := (h0.add h1).add h2
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 4] with n hn
  unfold sqrtHalfThirdModel sqrtHalfModel0 sqrtHalfModel1 sqrtHalfModel2 sqrtModel2Third
  norm_num
  ring_nf

private lemma sqrt_modelCoeff2_thirdOrder :
    (fun n : ℕ =>
      Ring.choose ((-(5 / 2 : ℝ)) + (n : ℕ) - 1) n - sqrtModel2Third n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have hsum := sqrt_coeff2_error_isLittleO.add sqrt_coeff2_model_shift
  refine hsum.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [sqrt_coeff2_eq_shifted_half hn]
  ring

lemma sqrt_Real_Gamma_neg_five_halves :
    Real.Gamma (-(5 / 2 : ℝ)) = -8 * Real.sqrt Real.pi / 15 := by
  have h := Real.Gamma_add_one (s := (-(5 / 2 : ℝ)))
    (by norm_num : (-(5 / 2 : ℝ)) ≠ 0)
  norm_num at h
  rw [sqrt_Real_Gamma_neg_three_halves] at h
  nlinarith

private lemma coeff_sub_const_smul (C : ℂ)
    (p q : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (p - C • q).coeff n = p.coeff n - C * q.coeff n := by
  change (p n - (C • q) n) 1 = p n 1 - C * q.coeff n
  rw [FormalMultilinearSeries.smul_apply]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
  change p.coeff n - C • q.coeff n = p.coeff n - C * q.coeff n
  simp [smul_eq_mul]

private lemma coeff_sub_three_const_smul (C0 C1 C2 : ℂ)
    (p q0 q1 q2 : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (p - C0 • q0 - C1 • q1 - C2 • q2).coeff n =
      p.coeff n - C0 * q0.coeff n - C1 * q1.coeff n - C2 * q2.coeff n := by
  rw [coeff_sub_const_smul, coeff_sub_const_smul, coeff_sub_const_smul]

private lemma sqrt_thirdOrder_model_complex_eq (B0 B1 B2 : ℂ) (n : ℕ) :
    B0 * ((sqrtModel0Third n : ℝ) : ℂ) +
        (-B1) * ((sqrtModel1Third n : ℝ) : ℂ) +
          (B2 / 2) * ((sqrtModel2Third n : ℝ) : ℂ) =
      sqrtSingularityC0 B0 *
          (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
        sqrtSingularityC1Rescaled B0 B1 *
          (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
        sqrtSingularityC2Rescaled B0 B1 B2 *
          (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ) := by
  unfold sqrtModel0Third sqrtModel1Third sqrtModel2Third sqrtSingularityC0
    sqrtSingularityC1Rescaled sqrtSingularityC2Rescaled
  norm_num [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_neg]
  ring

theorem sqrt_singularity_thirdOrder_rescaled_of_singularity
    {R φ : ℝ} {f : ℂ → ℂ} {P : PowerSeries ℂ}
    {A0 A1 B0 B1 B2 : ℂ}
    (hB0 : B0 ≠ 0)
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f (PowerSeries.toFMLS P) (0 : ℂ))
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ =>
        ‖sqrtAdjustedFun f A0 A1 z -
            B0 * (1 - z) ^ (1 / 2 : ℂ) -
            (-B1) * (1 - z) ^ (3 / 2 : ℂ) -
            (B2 / 2) * (1 - z) ^ (5 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(5 / 2 : ℝ)))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n P -
        (sqrtSingularityC0 B0 *
            (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
          sqrtSingularityC1Rescaled B0 B1 *
            (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
          sqrtSingularityC2Rescaled B0 B1 B2 *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
  have _ := hB0
  let pAdj : FormalMultilinearSeries ℂ ℂ ℂ :=
    PowerSeries.toFMLS (sqrtAdjustedSeries P A0 A1)
  let h0 : ℂ → ℂ := fun z => (1 - z) ^ (1 / 2 : ℂ)
  let h1 : ℂ → ℂ := fun z => (1 - z) ^ (3 / 2 : ℂ)
  let h2 : ℂ → ℂ := fun z => (1 - z) ^ (5 / 2 : ℂ)
  let q0 : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ
      (fun n : ℕ => Ring.choose (((-(1 / 2 : ℝ) : ℂ) + n - 1)) n)
  let q1 : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ
      (fun n : ℕ => Ring.choose (((-(3 / 2 : ℝ) : ℂ) + n - 1)) n)
  let q2 : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ
      (fun n : ℕ => Ring.choose (((-(5 / 2 : ℝ) : ℂ) + n - 1)) n)
  have hp_adj := sqrtAdjustedFun_hasFPowerSeriesAt_zero
    (f := f) (P := P) (A0 := A0) (A1 := A1) hp
  have hΔ_adj := analyticOnNhd_sqrtAdjustedFun
    (R := R) (φ := φ) (f := f) (A0 := A0) (A1 := A1) hΔ
  have hφπ : φ < Real.pi := by linarith [hφ2, Real.pi_pos]
  have hp0 : HasFPowerSeriesAt h0 q0 0 := by
    have hraw :=
      (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero
        ((-(1 / 2 : ℝ) : ℂ))).hasFPowerSeriesAt
    convert hraw using 1
    ext z
    dsimp [h0]
    rw [Complex.cpow_neg]
    simp
  have hp1 : HasFPowerSeriesAt h1 q1 0 := by
    have hraw :=
      (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero
        ((-(3 / 2 : ℝ) : ℂ))).hasFPowerSeriesAt
    convert hraw using 1
    ext z
    dsimp [h1]
    rw [Complex.cpow_neg]
    simp
  have hp2 : HasFPowerSeriesAt h2 q2 0 := by
    have hraw :=
      (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero
        ((-(5 / 2 : ℝ) : ℂ))).hasFPowerSeriesAt
    convert hraw using 1
    ext z
    dsimp [h2]
    rw [Complex.cpow_neg]
    simp
  have hΔ0 : AnalyticOnNhd ℂ h0 (DeltaDomainArg R φ) := by
    simpa [h0] using
      (analyticOnNhd_one_sub_cpow_deltaDomain
        (α := ((-(1 / 2 : ℝ) : ℂ))) (R := R) (φ := φ) hφ0 hφπ)
  have hΔ1 : AnalyticOnNhd ℂ h1 (DeltaDomainArg R φ) := by
    simpa [h1] using
      (analyticOnNhd_one_sub_cpow_deltaDomain
        (α := ((-(3 / 2 : ℝ) : ℂ))) (R := R) (φ := φ) hφ0 hφπ)
  have hΔ2 : AnalyticOnNhd ℂ h2 (DeltaDomainArg R φ) := by
    simpa [h2] using
      (analyticOnNhd_one_sub_cpow_deltaDomain
        (α := ((-(5 / 2 : ℝ) : ℂ))) (R := R) (φ := φ) hφ0 hφπ)
  let C2 : ℂ := B2 / 2
  have hpR : HasFPowerSeriesAt
      (fun z : ℂ =>
        sqrtAdjustedFun f A0 A1 z - B0 • h0 z - (-B1) • h1 z - C2 • h2 z)
      (pAdj - B0 • q0 - (-B1) • q1 - C2 • q2) 0 :=
    ((hp_adj.sub (hp0.const_smul (c := B0))).sub
      (hp1.const_smul (c := -B1))).sub (hp2.const_smul (c := C2))
  have hΔR : AnalyticOnNhd ℂ
      (fun z : ℂ =>
        sqrtAdjustedFun f A0 A1 z - B0 • h0 z - (-B1) • h1 z - C2 • h2 z)
      (DeltaDomainArg R φ) :=
    ((hΔ_adj.sub (hΔ0.const_smul (c := B0))).sub
      (hΔ1.const_smul (c := -B1))).sub (hΔ2.const_smul (c := C2))
  have hres_norm :
      (fun n : ℕ => ‖(pAdj - B0 • q0 - (-B1) • q1 - C2 • q2).coeff n‖)
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    convert coeff_norm_isLittleO_atTop_of_delta_littleO
      (R := R) (φ := φ) (β := (-(5 / 2 : ℝ)))
      (f := fun z : ℂ =>
        sqrtAdjustedFun f A0 A1 z - B0 • h0 z - (-B1) • h1 z - C2 • h2 z)
      (p := pAdj - B0 • q0 - (-B1) • q1 - C2 • q2)
      hR hφ0 hφ2 hpR hΔR ?_ using 1
    · ext n
      congr 1
      norm_num
    · simpa [h0, h1, h2, C2, smul_eq_mul] using hsing
  have hres : (fun n : ℕ => (pAdj - B0 • q0 - (-B1) • q1 - C2 • q2).coeff n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) :=
    Asymptotics.IsLittleO.of_norm_left hres_norm
  have h0c := ofReal_isLittleO sqrt_modelCoeff0_thirdOrder
  have h0term : (fun n : ℕ => B0 * q0.coeff n - B0 * ((sqrtModel0Third n : ℝ) : ℂ))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    have h := h0c.const_mul_left B0
    have hEq : (fun n : ℕ => B0 * q0.coeff n - B0 * ((sqrtModel0Third n : ℝ) : ℂ))
        =ᶠ[atTop]
        (fun n : ℕ =>
          B0 * ((Ring.choose ((-(1 / 2 : ℝ)) + (n : ℕ) - 1) n -
            sqrtModel0Third n : ℝ) : ℂ)) := by
      refine Eventually.of_forall fun n => ?_
      dsimp [q0]
      rw [FormalMultilinearSeries.coeff_ofScalars]
      have hchoose :
          Ring.choose (((-(1 / 2 : ℝ) : ℂ) + (n : ℕ) - 1)) n =
            ((Ring.choose ((-(1 / 2 : ℝ)) + (n : ℕ) - 1) n : ℝ) : ℂ) := by
        simpa [Complex.ofReal_neg] using choose_ofReal_model (-(1 / 2 : ℝ)) n
      rw [hchoose]
      rw [Complex.ofReal_sub]
      ring
    exact hEq.trans_isLittleO h
  have h1c := ofReal_isLittleO sqrt_modelCoeff1_thirdOrder
  have h1term :
      (fun n : ℕ => (-B1) * q1.coeff n - (-B1) * ((sqrtModel1Third n : ℝ) : ℂ))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    have h := h1c.const_mul_left (-B1)
    have hEq : (fun n : ℕ => (-B1) * q1.coeff n - (-B1) * ((sqrtModel1Third n : ℝ) : ℂ))
        =ᶠ[atTop]
        (fun n : ℕ =>
          (-B1) * ((Ring.choose ((-(3 / 2 : ℝ)) + (n : ℕ) - 1) n -
            sqrtModel1Third n : ℝ) : ℂ)) := by
      refine Eventually.of_forall fun n => ?_
      dsimp [q1]
      rw [FormalMultilinearSeries.coeff_ofScalars]
      have hchoose :
          Ring.choose (((-(3 / 2 : ℝ) : ℂ) + (n : ℕ) - 1)) n =
            ((Ring.choose ((-(3 / 2 : ℝ)) + (n : ℕ) - 1) n : ℝ) : ℂ) := by
        simpa [Complex.ofReal_neg] using choose_ofReal_model (-(3 / 2 : ℝ)) n
      rw [hchoose]
      rw [Complex.ofReal_sub]
      ring
    exact hEq.trans_isLittleO h
  have h2c := ofReal_isLittleO sqrt_modelCoeff2_thirdOrder
  have h2term :
      (fun n : ℕ => C2 * q2.coeff n - C2 * ((sqrtModel2Third n : ℝ) : ℂ))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    have h := h2c.const_mul_left C2
    have hEq : (fun n : ℕ => C2 * q2.coeff n - C2 * ((sqrtModel2Third n : ℝ) : ℂ))
        =ᶠ[atTop]
        (fun n : ℕ =>
          C2 * ((Ring.choose ((-(5 / 2 : ℝ)) + (n : ℕ) - 1) n -
            sqrtModel2Third n : ℝ) : ℂ)) := by
      refine Eventually.of_forall fun n => ?_
      dsimp [q2]
      rw [FormalMultilinearSeries.coeff_ofScalars]
      have hchoose :
          Ring.choose (((-(5 / 2 : ℝ) : ℂ) + (n : ℕ) - 1)) n =
            ((Ring.choose ((-(5 / 2 : ℝ)) + (n : ℕ) - 1) n : ℝ) : ℂ) := by
        simpa [Complex.ofReal_neg] using choose_ofReal_model (-(5 / 2 : ℝ)) n
      rw [hchoose]
      rw [Complex.ofReal_sub]
      ring
    exact hEq.trans_isLittleO h
  have hsum : (fun n : ℕ =>
      (B0 * q0.coeff n - B0 * ((sqrtModel0Third n : ℝ) : ℂ)) +
        ((-B1) * q1.coeff n - (-B1) * ((sqrtModel1Third n : ℝ) : ℂ)) +
          (C2 * q2.coeff n - C2 * ((sqrtModel2Third n : ℝ) : ℂ)) +
            (pAdj - B0 • q0 - (-B1) • q1 - C2 • q2).coeff n)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) :=
    ((h0term.add h1term).add h2term).add hres
  have hAdj : (fun n : ℕ =>
      pAdj.coeff n -
        (sqrtSingularityC0 B0 *
            (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
          sqrtSingularityC1Rescaled B0 B1 *
            (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
          sqrtSingularityC2Rescaled B0 B1 B2 *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-(7 / 2 : ℝ))) := by
    refine hsum.congr_left ?_
    intro n
    rw [coeff_sub_three_const_smul]
    dsimp [C2]
    calc
      B0 * q0.coeff n - B0 * ((sqrtModel0Third n : ℝ) : ℂ) +
              ((-B1) * q1.coeff n - (-B1) * ((sqrtModel1Third n : ℝ) : ℂ)) +
            (B2 / 2 * q2.coeff n - B2 / 2 * ((sqrtModel2Third n : ℝ) : ℂ)) +
          (pAdj.coeff n - B0 * q0.coeff n - (-B1) * q1.coeff n - B2 / 2 * q2.coeff n)
          =
        pAdj.coeff n -
          (B0 * ((sqrtModel0Third n : ℝ) : ℂ) +
            (-B1) * ((sqrtModel1Third n : ℝ) : ℂ) +
              (B2 / 2) * ((sqrtModel2Third n : ℝ) : ℂ)) := by
            ring
      _ = pAdj.coeff n -
          (sqrtSingularityC0 B0 *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1Rescaled B0 B1 *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC2Rescaled B0 B1 B2 *
              (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)) := by
            rw [sqrt_thirdOrder_model_complex_eq B0 B1 B2 n]
  refine hAdj.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 2] with n hn
  dsimp [pAdj]
  rw [coeff_sqrtAdjustedSeries_of_two_le hn]

theorem sqrt_singularity_thirdOrder_original_of_rescaled_singularity
    {ρ R φ : ℝ} {F : ℂ → ℂ} {P : PowerSeries ℂ}
    {A0 A1 Bρ Bderivρ Bsecondρ : ℂ}
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
            (-(((ρ : ℝ) : ℂ) * Bderivρ)) * (1 - z) ^ (3 / 2 : ℂ) -
            ((((ρ : ℝ) : ℂ) ^ 2 * Bsecondρ) / 2) * (1 - z) ^ (5 / 2 : ℂ)‖ *
          ‖(1 : ℂ) - z‖ ^ (-(5 / 2 : ℝ)))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n P -
        (((((ρ : ℝ) : ℂ)⁻¹) ^ n) *
          (sqrtSingularityC0 Bρ *
              (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC1 ρ Bρ Bderivρ *
              (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
            sqrtSingularityC2 ρ Bρ Bderivρ Bsecondρ *
              (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))))
      =o[atTop]
        (fun n : ℕ =>
          ‖(((((ρ : ℝ) : ℂ)⁻¹) ^ n) *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖) := by
  let ρc : ℂ := ((ρ : ℝ) : ℂ)
  let B1 : ℂ := ρc * Bderivρ
  let B2 : ℂ := ρc ^ 2 * Bsecondρ
  have hρc : ρc ≠ 0 := by
    dsimp [ρc]
    exact_mod_cast (ne_of_gt hρ)
  have hrescaled := sqrt_singularity_thirdOrder_rescaled_of_singularity
    (R := R) (φ := φ)
    (f := fun z : ℂ => F (ρc * z))
    (P := PowerSeries.rescale ρc P)
    (A0 := A0) (A1 := A1) (B0 := Bρ) (B1 := B1) (B2 := B2)
    hBρ hR hφ0 hφ2 ?_ ?_ ?_
  · rw [Asymptotics.isLittleO_iff] at hrescaled ⊢
    intro c hc
    have hbound := hrescaled hc
    filter_upwards [hbound] with n hn
    let model : ℂ :=
      sqrtSingularityC0 Bρ *
          (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
        sqrtSingularityC1 ρ Bρ Bderivρ *
          (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
        sqrtSingularityC2 ρ Bρ Bderivρ Bsecondρ *
          (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)
    let r : ℂ := (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)
    have hC1 : sqrtSingularityC1 ρ Bρ Bderivρ =
        sqrtSingularityC1Rescaled Bρ B1 := by
      simp [sqrtSingularityC1, B1, ρc]
    have hC2 : sqrtSingularityC2 ρ Bρ Bderivρ Bsecondρ =
        sqrtSingularityC2Rescaled Bρ B1 B2 := by
      simp [sqrtSingularityC2, B1, B2, ρc]
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
                  (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
                sqrtSingularityC2Rescaled Bρ B1 B2 *
                  (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))) := by
      rw [hcoeff_rescale, ← hC1, ← hC2]
      dsimp [model]
      calc
        PowerSeries.coeff (R := ℂ) n P - ρc⁻¹ ^ n *
            (sqrtSingularityC0 Bρ *
                (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
              sqrtSingularityC1 ρ Bρ Bderivρ *
                (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
              sqrtSingularityC2 ρ Bρ Bderivρ Bsecondρ *
                (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))
            =
            ρc⁻¹ ^ n *
              (PowerSeries.coeff (R := ℂ) n P * ρc ^ n -
                (sqrtSingularityC0 Bρ *
                    (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
                  sqrtSingularityC1 ρ Bρ Bderivρ *
                    (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
                  sqrtSingularityC2 ρ Bρ Bderivρ Bsecondρ *
                    (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))) := by
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
                    (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
                  sqrtSingularityC2 ρ Bρ Bderivρ Bsecondρ *
                    (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))) := rfl
    have hnorm_target :
        ‖‖ρc⁻¹ ^ n * r‖‖ = ‖ρc⁻¹ ^ n‖ *
            ‖(((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)‖ := by
      simp [r, norm_mul]
    calc
      ‖PowerSeries.coeff (R := ℂ) n P - ρc⁻¹ ^ n * model‖
          = ‖ρc⁻¹ ^ n *
              (PowerSeries.coeff (R := ℂ) n (PowerSeries.rescale ρc P) -
                (sqrtSingularityC0 Bρ *
                    (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
                  sqrtSingularityC1Rescaled Bρ B1 *
                    (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
                  sqrtSingularityC2Rescaled Bρ B1 B2 *
                    (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ)))‖ := by
              rw [hleft]
      _ = ‖ρc⁻¹ ^ n‖ *
            ‖PowerSeries.coeff (R := ℂ) n (PowerSeries.rescale ρc P) -
              (sqrtSingularityC0 Bρ *
                  (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) +
                sqrtSingularityC1Rescaled Bρ B1 *
                  (((n : ℝ) ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) +
                sqrtSingularityC2Rescaled Bρ B1 B2 *
                  (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖ := by
              rw [norm_mul]
      _ ≤ ‖ρc⁻¹ ^ n‖ * (c * ‖(n : ℝ) ^ (-(7 / 2 : ℝ))‖) := by
              exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = c * ‖‖ρc⁻¹ ^ n * r‖‖ := by
              rw [hnorm_target, Complex.norm_real]
              ring
      _ = c * ‖‖(((((ρ : ℝ) : ℂ)⁻¹) ^ n) *
            (((n : ℝ) ^ (-(7 / 2 : ℝ)) : ℝ) : ℂ))‖‖ := by
              simp [ρc, r]
  · simpa [ρc] using hp
  · simpa [ρc] using hΔ
  · simpa [ρc, B1, B2] using hsing

end
