import AnalyticCombinatorics.Ch4.Analytic.ModelCoeffExplicit
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries

/-!
# Third-order model coefficient estimate

This file proves the third coefficient in the Gamma-ratio/model-coefficient
expansion by the recurrence bootstrap route.  It does not use Stirling or
digamma asymptotics.
-/

set_option maxHeartbeats 1200000

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

private def gammaRatioNorm (α : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) /
    ((n : ℝ) ^ (α - 1))

private def gammaStep (α : ℝ) (n : ℕ) : ℝ :=
  (1 + α * (n : ℝ)⁻¹) * (1 + (n : ℝ)⁻¹) ^ (-α)

private def c1 (α : ℝ) : ℝ :=
  α * (α - 1) / 2

private def c2 (α : ℝ) : ℝ :=
  α * (α - 1) * (α - 2) * (3 * α - 1) / 24

private def d3 (α : ℝ) : ℝ :=
  α * (α - 1) * (α + 1) / 3

private def gammaSecondError (α : ℝ) (n : ℕ) : ℝ :=
  gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹

private def gammaThirdError (α : ℝ) (n : ℕ) : ℝ :=
  gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹ -
    c2 α * ((n : ℝ)⁻¹) ^ 2

private lemma choose_neg_two (α : ℝ) :
    Ring.choose (-α) 2 = α * (α + 1) / 2 := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (-α : ℝ) 2
  norm_num [descPochhammer, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_C, Polynomial.smeval_natCast] at h
  nlinarith

private lemma choose_neg_three (α : ℝ) :
    Ring.choose (-α) 3 = -α * (α + 1) * (α + 2) / 6 := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (-α : ℝ) 3
  norm_num [descPochhammer, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_C, Polynomial.smeval_natCast] at h
  nlinarith

private lemma binomial_partialSum_three (α x : ℝ) :
    (binomialSeries ℝ (-α)).partialSum 3 x =
      1 - α * x + (α * (α + 1) / 2) * x ^ 2 := by
  simp [FormalMultilinearSeries.partialSum, binomialSeries, Finset.sum_range_succ,
    choose_neg_two]
  ring_nf

private lemma binomial_partialSum_four (α x : ℝ) :
    (binomialSeries ℝ (-α)).partialSum 4 x =
      1 - α * x + (α * (α + 1) / 2) * x ^ 2 -
        (α * (α + 1) * (α + 2) / 6) * x ^ 3 := by
  simp [FormalMultilinearSeries.partialSum, binomialSeries, Finset.sum_range_succ,
    choose_neg_two, choose_neg_three]
  ring_nf

private lemma rpow_neg_sub_quadratic_isBigO (α : ℝ) :
    (fun x : ℝ =>
      (1 + x) ^ (-α) - (1 - α * x + (α * (α + 1) / 2) * x ^ 2))
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := -α)).isBigO_sub_partialSum_pow 3
  exact h.congr_left fun x => by
    rw [binomial_partialSum_three]
    simp

private lemma rpow_neg_sub_cubic_isBigO (α : ℝ) :
    (fun x : ℝ =>
      (1 + x) ^ (-α) -
        (1 - α * x + (α * (α + 1) / 2) * x ^ 2 -
          (α * (α + 1) * (α + 2) / 6) * x ^ 3))
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := -α)).isBigO_sub_partialSum_pow 4
  exact h.congr_left fun x => by
    rw [binomial_partialSum_four]
    simp

private lemma linear_near_zero_isBigO_one (α : ℝ) :
    (fun x : ℝ => 1 + α * x) =O[𝓝 0] (fun _x : ℝ => (1 : ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 1 + α * x) (𝓝 0) (𝓝 ((fun x : ℝ => 1 + α * x) 0)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
  simpa using ht.isBigO_one ℝ

private lemma const_mul_cubic_isBigO_norm_cubic (a : ℝ) :
    (fun x : ℝ => a * x ^ 3) =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  refine IsBigO.of_bound ‖a‖ ?_
  filter_upwards with x
  calc
    ‖a * x ^ 3‖ = ‖a‖ * ‖x‖ ^ 3 := by
      rw [norm_mul, norm_pow]
    _ ≤ ‖a‖ * ‖‖x‖ ^ 3‖ := by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ 3)]

private lemma const_mul_quartic_isBigO_norm_quartic (a : ℝ) :
    (fun x : ℝ => a * x ^ 4) =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
  refine IsBigO.of_bound ‖a‖ ?_
  filter_upwards with x
  calc
    ‖a * x ^ 4‖ = ‖a‖ * ‖x‖ ^ 4 := by
      rw [norm_mul, norm_pow]
    _ ≤ ‖a‖ * ‖‖x‖ ^ 4‖ := by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ 4)]

private lemma gammaStep_local_at_zero (α : ℝ) :
    (fun x : ℝ =>
      (1 + α * x) * (1 + x) ^ (-α) - 1 + c1 α * x ^ 2)
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  let q : ℝ → ℝ := fun x => 1 - α * x + (α * (α + 1) / 2) * x ^ 2
  have hrem :
      (fun x : ℝ => (1 + x) ^ (-α) - q x)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
    simpa [q] using rpow_neg_sub_quadratic_isBigO α
  have hlin := linear_near_zero_isBigO_one α
  have hprod0 := hlin.mul hrem
  have hprod :
      (fun x : ℝ => (1 + α * x) * ((1 + x) ^ (-α) - q x))
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
    refine hprod0.congr_left ?_ |>.congr_right ?_
    · intro x
      ring_nf
    · intro x
      simp
  have hcubic :
      (fun x : ℝ => (α ^ 2 * (α + 1) / 2) * x ^ 3)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) :=
    const_mul_cubic_isBigO_norm_cubic _
  have hsum := hprod.add hcubic
  exact hsum.congr_left fun x => by
    dsimp [q, c1]
    ring_nf

private lemma gammaStep_local_third (α : ℝ) :
    (fun x : ℝ =>
      (1 + α * x) * (1 + x) ^ (-α) -
        (1 - c1 α * x ^ 2 + d3 α * x ^ 3))
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
  let q : ℝ → ℝ := fun x =>
    1 - α * x + (α * (α + 1) / 2) * x ^ 2 -
      (α * (α + 1) * (α + 2) / 6) * x ^ 3
  have hrem :
      (fun x : ℝ => (1 + x) ^ (-α) - q x)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
    simpa [q] using rpow_neg_sub_cubic_isBigO α
  have hlin := linear_near_zero_isBigO_one α
  have hprod0 := hlin.mul hrem
  have hprod :
      (fun x : ℝ => (1 + α * x) * ((1 + x) ^ (-α) - q x))
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
    refine hprod0.congr_left ?_ |>.congr_right ?_
    · intro x
      ring_nf
    · intro x
      simp
  have hquartic :
      (fun x : ℝ => (-(α ^ 2 * (α + 1) * (α + 2) / 6)) * x ^ 4)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) :=
    const_mul_quartic_isBigO_norm_quartic _
  have hsum := hprod.add hquartic
  exact hsum.congr_left fun x => by
    dsimp [q, c1, d3]
    ring_nf

private lemma inv_norm_cube_eq (n : ℕ) :
    ‖((n : ℝ)⁻¹)‖ ^ 3 = ((n : ℝ)⁻¹) ^ 3 := by
  rw [Real.norm_of_nonneg]
  positivity

private lemma inv_norm_four_eq (n : ℕ) :
    ‖((n : ℝ)⁻¹)‖ ^ 4 = ((n : ℝ)⁻¹) ^ 4 := by
  rw [Real.norm_of_nonneg]
  positivity

private lemma inv_four_isBigO_inv_cube :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hinv_le_one : (n : ℝ)⁻¹ ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_le_one_of_one_le₀ hn1
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 4),
    Real.norm_of_nonneg (pow_nonneg hinv_nonneg 3)]
  nlinarith [mul_le_mul_of_nonneg_right hinv_le_one (pow_nonneg hinv_nonneg 3)]

private lemma inv_cube_isBigO_inv_sq :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hinv_le_one : (n : ℝ)⁻¹ ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_le_one_of_one_le₀ hn1
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 3),
    Real.norm_of_nonneg (pow_nonneg hinv_nonneg 2)]
  nlinarith [mul_le_mul_of_nonneg_right hinv_le_one (pow_nonneg hinv_nonneg 2)]

private lemma inv_sq_isBigO_inv :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hinv_le_one : (n : ℝ)⁻¹ ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_le_one_of_one_le₀ hn1
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 2),
    Real.norm_of_nonneg hinv_nonneg]
  nlinarith

private lemma gammaStep_sub_isBigO_inv_cube (α : ℝ) :
    (fun n : ℕ =>
      gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have hcomp :=
    (gammaStep_local_at_zero α).comp_tendsto
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine hcomp.congr_left ?_ |>.congr_right ?_
  · intro n
    simp [gammaStep]
  · intro n
    exact inv_norm_cube_eq n

private lemma gammaStep_sub_third_isBigO_inv_four (α : ℝ) :
    (fun n : ℕ =>
      gammaStep α n -
        (1 - c1 α * ((n : ℝ)⁻¹) ^ 2 +
          d3 α * ((n : ℝ)⁻¹) ^ 3))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
  have hcomp :=
    (gammaStep_local_third α).comp_tendsto
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine hcomp.congr_left ?_ |>.congr_right ?_
  · intro n
    simp [gammaStep]
  · intro n
    exact inv_norm_four_eq n

private lemma const_mul_inv_sq_isBigO_inv_sq (a : ℝ) :
    (fun n : ℕ => a * ((n : ℝ)⁻¹) ^ 2)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  exact (isBigO_refl (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop).const_mul_left a

private lemma gammaStep_sub_one_isBigO_inv_sq (α : ℝ) :
    (fun n : ℕ => gammaStep α n - 1)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  have h3 := (gammaStep_sub_isBigO_inv_cube α).trans inv_cube_isBigO_inv_sq
  have hc := const_mul_inv_sq_isBigO_inv_sq (-(c1 α))
  have hsum := h3.add hc
  refine hsum.congr_left ?_
  intro n
  ring_nf

private lemma gammaRatioNorm_succ
    {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop,
      gammaRatioNorm α (n + 1) = gammaRatioNorm α n * gammaStep α n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hbase_pos : 0 < 1 + (n : ℝ)⁻¹ := by positivity
  have hs_pos : 0 < (n : ℝ) + α := by positivity
  have hΓnum : Real.Gamma (((n + 1 : ℕ) : ℝ) + α) =
      ((n : ℝ) + α) * Real.Gamma ((n : ℝ) + α) := by
    calc
      Real.Gamma (((n + 1 : ℕ) : ℝ) + α)
          = Real.Gamma (((n : ℝ) + α) + 1) := by
              congr 1
              norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      _ = ((n : ℝ) + α) * Real.Gamma ((n : ℝ) + α) :=
          Real.Gamma_add_one hs_pos.ne'
  have hΓden : Real.Gamma (((n + 1 : ℕ) : ℝ) + 1) =
      ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) := by
    calc
      Real.Gamma (((n + 1 : ℕ) : ℝ) + 1)
          = Real.Gamma (((n : ℝ) + 1) + 1) := by
              congr 1
              norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      _ = ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) := by
          exact Real.Gamma_add_one (by positivity : (n : ℝ) + 1 ≠ 0)
  have hnadd : (n : ℝ) + 1 = (n : ℝ) * (1 + (n : ℝ)⁻¹) := by
    field_simp [hnne]
  have hn1eq : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) * (1 + (n : ℝ)⁻¹) := by
    rw [Nat.cast_add, Nat.cast_one, hnadd]
  have hpow : (((n + 1 : ℕ) : ℝ)) ^ (α - 1) =
      ((n : ℝ) ^ (α - 1)) * (1 + (n : ℝ)⁻¹) ^ (α - 1) := by
    rw [hn1eq]
    rw [Real.mul_rpow (le_of_lt hnpos) (le_of_lt hbase_pos)]
  have hbase_alpha : (1 + (n : ℝ)⁻¹) ^ α =
      (1 + (n : ℝ)⁻¹) ^ (α - 1) * (1 + (n : ℝ)⁻¹) := by
    calc
      (1 + (n : ℝ)⁻¹) ^ α
          = (1 + (n : ℝ)⁻¹) ^ ((α - 1) + 1) := by ring_nf
      _ = (1 + (n : ℝ)⁻¹) ^ (α - 1) *
            (1 + (n : ℝ)⁻¹) ^ (1 : ℝ) := by
          rw [Real.rpow_add hbase_pos]
      _ = (1 + (n : ℝ)⁻¹) ^ (α - 1) * (1 + (n : ℝ)⁻¹) := by
          rw [Real.rpow_one]
  have hΓnum_ne : Real.Gamma ((n : ℝ) + α) ≠ 0 :=
    (Real.Gamma_pos_of_pos hs_pos).ne'
  have hΓden_ne : Real.Gamma ((n : ℝ) + 1) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 1)).ne'
  have hpow_n_ne : ((n : ℝ) ^ (α - 1)) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hbase_pow_ne : (1 + (n : ℝ)⁻¹) ^ (α - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hbase_pos _).ne'
  have hbase_alpha_ne : (1 + (n : ℝ)⁻¹) ^ α ≠ 0 :=
    (Real.rpow_pos_of_pos hbase_pos _).ne'
  unfold gammaRatioNorm gammaStep
  rw [hΓnum, hΓden, hpow, hnadd, Real.rpow_neg (le_of_lt hbase_pos), hbase_alpha]
  field_simp [hΓnum_ne, hΓden_ne, hpow_n_ne, hbase_pow_ne, hbase_alpha_ne,
    hnne, hbase_pos.ne']

private lemma rpow_neg_one_eq_inv_nat (n : ℕ) :
    (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_one]

private lemma rpow_neg_two_eq_inv_sq_nat (n : ℕ) :
    (n : ℝ) ^ (-(2 : ℝ)) = ((n : ℝ)⁻¹) ^ 2 := by
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num

private lemma rpow_neg_three_eq_inv_cube_nat (n : ℕ) :
    (n : ℝ) ^ (-(3 : ℝ)) = ((n : ℝ)⁻¹) ^ 3 := by
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num

private lemma rpow_neg_four_eq_inv_four_nat (n : ℕ) :
    (n : ℝ) ^ (-(4 : ℝ)) = ((n : ℝ)⁻¹) ^ 4 := by
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num

private lemma gammaRatioNorm_sub_one_isBigO_inv
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNorm α n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  have hA1 := gamma_ratio_first_order hα
  have hp : (fun n : ℕ => (n : ℝ) ^ (1 - α))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 - α)) := isBigO_refl _ _
  have hmul :
      (fun n : ℕ =>
        (Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
          (n : ℝ) ^ (α - 1)) * (n : ℝ) ^ (1 - α))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
    exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := α - 2) (b := 1 - α) (c := -(1 : ℝ)) hA1 hp (by linarith)
  have heq : (fun n : ℕ => gammaRatioNorm α n - 1) =ᶠ[atTop]
      (fun n : ℕ =>
        (Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
          (n : ℝ) ^ (α - 1)) * (n : ℝ) ^ (1 - α)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hpow_ne : (n : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hnpos _).ne'
    have hpow_inv : (n : ℝ) ^ (1 - α) = ((n : ℝ) ^ (α - 1))⁻¹ := by
      rw [← Real.rpow_neg (le_of_lt hnpos)]
      congr 1
      ring_nf
    unfold gammaRatioNorm
    rw [hpow_inv]
    field_simp [hpow_ne]
  exact (heq.trans_isBigO hmul).congr_right fun n => by
    rw [rpow_neg_one_eq_inv_nat]

private lemma tail_inv_sq_shift (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) ≤
      2 / ((N : ℝ) + 1) := by
  apply Real.tsum_le_of_sum_range_le (fun i => by positivity)
  intro n
  have hreindex : (∑ i ∈ Finset.range n,
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)
      = ∑ k ∈ Finset.Ico (N + 1) (N + 1 + n), 1 / ((k : ℝ)) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hsub : N + 1 + n - (N + 1) = n := by omega
    rw [hsub]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [show i + N + 1 = N + 1 + i from by omega]
  rw [hreindex]
  have hIco : Finset.Ico (N + 1) (N + 1 + n) = Finset.Ioo N (N + 1 + n) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hIco]
  have hbound := sum_Ioo_inv_sq_le (α := ℝ) N (N + 1 + n)
  simp only [one_div]
  exact hbound

private lemma tail_inv_cube_shift (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) ≤
      2 / ((N : ℝ) + 1) ^ 2 := by
  have hcube_summ : Summable
      (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
    have hshift := (summable_nat_add_iff (N + 1)).mpr h
    refine hshift.congr fun i => ?_
    have he : i + (N + 1) = i + N + 1 := by omega
    rw [he]
  have hsquare_summ : Summable
      (fun i : ℕ => (1 / ((N : ℝ) + 1)) *
        (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)) := by
    have h : Summable (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
      have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
      have hshift := (summable_nat_add_iff (N + 1)).mpr hbase
      refine hshift.congr fun i => ?_
      have he : i + (N + 1) = i + N + 1 := by omega
      rw [he]
    exact h.mul_left _
  have hterm : ∀ i : ℕ,
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3 ≤
        (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
    intro i
    have hNpos : 0 < (N : ℝ) + 1 := by positivity
    have hkpos : 0 < (((i + N + 1 : ℕ)) : ℝ) := by positivity
    have hle_nat : N + 1 ≤ i + N + 1 := by omega
    have hle : (N : ℝ) + 1 ≤ ((i + N + 1 : ℕ) : ℝ) := by exact_mod_cast hle_nat
    have hinv_le : 1 / (((i + N + 1 : ℕ)) : ℝ) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hNpos hle
    have hsquare_nonneg : 0 ≤ 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2 := by positivity
    calc
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3
          = (1 / (((i + N + 1 : ℕ)) : ℝ)) *
              (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
              field_simp [hkpos.ne']
      _ ≤ (1 / ((N : ℝ) + 1)) *
            (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hinv_le hsquare_nonneg
  have hle := hcube_summ.tsum_le_tsum hterm hsquare_summ
  have hsquare_bound := tail_inv_sq_shift N
  calc
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3)
        ≤ ∑' i : ℕ, (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := hle
    _ = (1 / ((N : ℝ) + 1)) *
          (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
          rw [tsum_mul_left]
    _ ≤ (1 / ((N : ℝ) + 1)) * (2 / ((N : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left hsquare_bound (by positivity)
    _ = 2 / ((N : ℝ) + 1) ^ 2 := by
          field_simp [(by positivity : (N : ℝ) + 1 ≠ 0)]

private lemma tail_inv_four_shift (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4) ≤
      2 / ((N : ℝ) + 1) ^ 3 := by
  have hfour_summ : Summable
      (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 4) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)
    have hshift := (summable_nat_add_iff (N + 1)).mpr h
    refine hshift.congr fun i => ?_
    have he : i + (N + 1) = i + N + 1 := by omega
    rw [he]
  have hcube_summ : Summable
      (fun i : ℕ => (1 / ((N : ℝ) + 1)) *
        (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3)) := by
    have h : Summable (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
      have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      have hshift := (summable_nat_add_iff (N + 1)).mpr hbase
      refine hshift.congr fun i => ?_
      have he : i + (N + 1) = i + N + 1 := by omega
      rw [he]
    exact h.mul_left _
  have hterm : ∀ i : ℕ,
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4 ≤
        (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
    intro i
    have hNpos : 0 < (N : ℝ) + 1 := by positivity
    have hkpos : 0 < (((i + N + 1 : ℕ)) : ℝ) := by positivity
    have hle_nat : N + 1 ≤ i + N + 1 := by omega
    have hle : (N : ℝ) + 1 ≤ ((i + N + 1 : ℕ) : ℝ) := by exact_mod_cast hle_nat
    have hinv_le : 1 / (((i + N + 1 : ℕ)) : ℝ) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hNpos hle
    have hcube_nonneg : 0 ≤ 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3 := by positivity
    calc
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4
          = (1 / (((i + N + 1 : ℕ)) : ℝ)) *
              (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
              field_simp [hkpos.ne']
      _ ≤ (1 / ((N : ℝ) + 1)) *
            (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right hinv_le hcube_nonneg
  have hle := hfour_summ.tsum_le_tsum hterm hcube_summ
  have hcube_bound := tail_inv_cube_shift N
  calc
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4)
        ≤ ∑' i : ℕ, (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := hle
    _ = (1 / ((N : ℝ) + 1)) *
          (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
          rw [tsum_mul_left]
    _ ≤ (1 / ((N : ℝ) + 1)) * (2 / ((N : ℝ) + 1) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hcube_bound (by positivity)
    _ = 2 / ((N : ℝ) + 1) ^ 3 := by
          field_simp [(by positivity : (N : ℝ) + 1 ≠ 0)]

private lemma summable_of_isBigO_inv_cube {d : ℕ → ℝ}
    (hd : d =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)) :
    Summable d := by
  rcases hd.exists_pos with ⟨C, hCpos, hC⟩
  have hmajor : Summable (fun n : ℕ => C * (((n : ℝ)⁻¹) ^ 3)) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
      have h' : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      exact h'.congr fun n => by
        rw [one_div, inv_pow]
    exact h.mul_left C
  refine Summable.of_norm_bounded_eventually hmajor ?_
  have hb := hC.bound
  rw [eventually_atTop] at hb
  rcases hb with ⟨N, hN⟩
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 3 := by positivity
  have hnorm : ‖((n : ℝ)⁻¹) ^ 3‖ = ((n : ℝ)⁻¹) ^ 3 := by
    rw [Real.norm_of_nonneg hnonneg]
  calc
    ‖d n‖ ≤ C * ‖((n : ℝ)⁻¹) ^ 3‖ := hN n hnN
    _ = C * ((n : ℝ)⁻¹) ^ 3 := by rw [hnorm]

private lemma summable_of_isBigO_inv_four {d : ℕ → ℝ}
    (hd : d =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4)) :
    Summable d := by
  rcases hd.exists_pos with ⟨C, hCpos, hC⟩
  have hmajor : Summable (fun n : ℕ => C * (((n : ℝ)⁻¹) ^ 4)) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
      have h' : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 4) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)
      exact h'.congr fun n => by
        rw [one_div, inv_pow]
    exact h.mul_left C
  refine Summable.of_norm_bounded_eventually hmajor ?_
  have hb := hC.bound
  rw [eventually_atTop] at hb
  rcases hb with ⟨N, hN⟩
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 4 := by positivity
  have hnorm : ‖((n : ℝ)⁻¹) ^ 4‖ = ((n : ℝ)⁻¹) ^ 4 := by
    rw [Real.norm_of_nonneg hnonneg]
  calc
    ‖d n‖ ≤ C * ‖((n : ℝ)⁻¹) ^ 4‖ := hN n hnN
    _ = C * ((n : ℝ)⁻¹) ^ 4 := by rw [hnorm]

private lemma sum_range_succDiff (u : ℕ → ℝ) (n m : ℕ) :
    (∑ i ∈ Finset.range m, (u (i + n + 1) - u (i + n))) =
      u (n + m) - u n := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : m + n + 1 = n + (m + 1) := by omega
      rw [h1]
      ring_nf

private lemma eq_neg_tsum_succDiff {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hd_summ : Summable (fun n : ℕ => u (n + 1) - u n)) (n : ℕ) :
    u n = -∑' i : ℕ, (u (i + n + 1) - u (i + n)) := by
  let d : ℕ → ℝ := fun k => u (k + 1) - u k
  have htail_summ : Summable (fun i : ℕ => d (i + n)) :=
    (summable_nat_add_iff n).mpr hd_summ
  have hleft := htail_summ.tendsto_sum_tsum_nat
  have hleft' :
      Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (u (i + n + 1) - u (i + n)))
        atTop (𝓝 (∑' i : ℕ, (u (i + n + 1) - u (i + n)))) := by
    refine hleft.congr' ?_
    filter_upwards with m
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp [d]
  have hright :
      Tendsto (fun m : ℕ => u (n + m) - u n) atTop (𝓝 (0 - u n)) := by
    have hcomp : Tendsto (fun m : ℕ => u (m + n)) atTop (𝓝 0) :=
      hu.comp (tendsto_add_atTop_nat n)
    have hcomp' : Tendsto (fun m : ℕ => u (n + m)) atTop (𝓝 0) := by
      refine hcomp.congr' ?_
      filter_upwards with m
      rw [Nat.add_comm]
    exact hcomp'.sub tendsto_const_nhds
  have hleft'' :
      Tendsto (fun m : ℕ => u (n + m) - u n) atTop
        (𝓝 (∑' i : ℕ, (u (i + n + 1) - u (i + n)))) := by
    refine hleft'.congr' ?_
    filter_upwards with m
    exact sum_range_succDiff u n m
  have hlim := tendsto_nhds_unique hleft'' hright
  rw [hlim]
  ring_nf

private lemma tendsto_zero_of_succDiff_isBigO_inv_cube
    {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hdiff :
      (fun n : ℕ => u (n + 1) - u n)
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)) :
    u =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  let d : ℕ → ℝ := fun n => u (n + 1) - u n
  rcases hdiff.exists_pos with ⟨C, hCpos, hC⟩
  have hd_summ : Summable d := summable_of_isBigO_inv_cube hdiff
  refine IsBigO.of_bound (2 * C) ?_
  have hCbound := hC.bound
  rw [eventually_atTop] at hCbound
  rcases hCbound with ⟨N, hN⟩
  refine eventually_atTop.mpr ⟨max N 2, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have htail_eq := eq_neg_tsum_succDiff hu hd_summ n
  have htail_summ : Summable (fun i : ℕ => d (i + n)) :=
    (summable_nat_add_iff n).mpr hd_summ
  have htail_norm_summ : Summable (fun i : ℕ => ‖d (i + n)‖) := by
    rw [summable_norm_iff]
    exact htail_summ
  have hnorm_le := norm_tsum_le_tsum_norm htail_norm_summ
  have hterm_le : ∀ i : ℕ,
      ‖d (i + n)‖ ≤ C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
    intro i
    have hikN : N ≤ i + n := le_trans hnN (by omega)
    have hb := hN (i + n) hikN
    have hnonneg : 0 ≤ (((i + n : ℕ) : ℝ)⁻¹) ^ 3 := by positivity
    have hnorm : ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 3‖ =
        (((i + n : ℕ) : ℝ)⁻¹) ^ 3 := by
      rw [Real.norm_of_nonneg hnonneg]
    calc
      ‖d (i + n)‖ ≤ C * ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 3‖ := hb
      _ = C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
          rw [hnorm, one_div, inv_pow]
  have hmajor_summ : Summable (fun i : ℕ => C * (1 / (((i + n : ℕ)) : ℝ) ^ 3)) := by
    have hbase : Summable (fun i : ℕ => 1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
      have h : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 3) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      exact (summable_nat_add_iff n).mpr h
    exact hbase.mul_left C
  have htsum_le :
      (∑' i : ℕ, ‖d (i + n)‖) ≤
        ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
    exact htail_norm_summ.tsum_le_tsum hterm_le hmajor_summ
  have htail_cube :
      (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 3) ≤
        2 / (n : ℝ) ^ 2 := by
    have hn_pred : n - 1 + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hnpos_nat)
    have h := tail_inv_cube_shift (n - 1)
    have hleft :
        (∑' i : ℕ, 1 / (((i + (n - 1) + 1 : ℕ)) : ℝ) ^ 3) =
          (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
      apply tsum_congr
      intro i
      rw [show i + (n - 1) + 1 = i + n from by omega]
    have hright : 2 / (((n - 1 : ℕ) : ℝ) + 1) ^ 2 = 2 / (n : ℝ) ^ 2 := by
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast hn_pred
      rw [hcast]
    rwa [hleft, hright] at h
  have htail_bound :
      (∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 3)) ≤
        C * (2 / (n : ℝ) ^ 2) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left htail_cube hCpos.le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 2 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 2‖ = ((n : ℝ)⁻¹) ^ 2 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  have hpow_rw : 2 * C * ‖((n : ℝ)⁻¹) ^ 2‖ = C * (2 / (n : ℝ) ^ 2) := by
    rw [htarget_norm]
    field_simp [hnpos.ne']
  calc
    ‖u n‖ = ‖∑' i : ℕ, d (i + n)‖ := by
      rw [htail_eq, norm_neg]
    _ ≤ ∑' i : ℕ, ‖d (i + n)‖ := hnorm_le
    _ ≤ ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := htsum_le
    _ ≤ C * (2 / (n : ℝ) ^ 2) := htail_bound
    _ = 2 * C * ‖((n : ℝ)⁻¹) ^ 2‖ := hpow_rw.symm

private lemma tendsto_zero_of_succDiff_isBigO_inv_four
    {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hdiff :
      (fun n : ℕ => u (n + 1) - u n)
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4)) :
    u =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  let d : ℕ → ℝ := fun n => u (n + 1) - u n
  rcases hdiff.exists_pos with ⟨C, hCpos, hC⟩
  have hd_summ : Summable d := summable_of_isBigO_inv_four hdiff
  refine IsBigO.of_bound (2 * C) ?_
  have hCbound := hC.bound
  rw [eventually_atTop] at hCbound
  rcases hCbound with ⟨N, hN⟩
  refine eventually_atTop.mpr ⟨max N 2, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have htail_eq := eq_neg_tsum_succDiff hu hd_summ n
  have htail_summ : Summable (fun i : ℕ => d (i + n)) :=
    (summable_nat_add_iff n).mpr hd_summ
  have htail_norm_summ : Summable (fun i : ℕ => ‖d (i + n)‖) := by
    rw [summable_norm_iff]
    exact htail_summ
  have hnorm_le := norm_tsum_le_tsum_norm htail_norm_summ
  have hterm_le : ∀ i : ℕ,
      ‖d (i + n)‖ ≤ C * (1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
    intro i
    have hikN : N ≤ i + n := le_trans hnN (by omega)
    have hb := hN (i + n) hikN
    have hnonneg : 0 ≤ (((i + n : ℕ) : ℝ)⁻¹) ^ 4 := by positivity
    have hnorm : ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 4‖ =
        (((i + n : ℕ) : ℝ)⁻¹) ^ 4 := by
      rw [Real.norm_of_nonneg hnonneg]
    calc
      ‖d (i + n)‖ ≤ C * ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 4‖ := hb
      _ = C * (1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
          rw [hnorm, one_div, inv_pow]
  have hmajor_summ : Summable (fun i : ℕ => C * (1 / (((i + n : ℕ)) : ℝ) ^ 4)) := by
    have hbase : Summable (fun i : ℕ => 1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
      have h : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 4) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)
      exact (summable_nat_add_iff n).mpr h
    exact hbase.mul_left C
  have htsum_le :
      (∑' i : ℕ, ‖d (i + n)‖) ≤
        ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
    exact htail_norm_summ.tsum_le_tsum hterm_le hmajor_summ
  have htail_four :
      (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 4) ≤
        2 / (n : ℝ) ^ 3 := by
    have hn_pred : n - 1 + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hnpos_nat)
    have h := tail_inv_four_shift (n - 1)
    have hleft :
        (∑' i : ℕ, 1 / (((i + (n - 1) + 1 : ℕ)) : ℝ) ^ 4) =
          (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
      apply tsum_congr
      intro i
      rw [show i + (n - 1) + 1 = i + n from by omega]
    have hright : 2 / (((n - 1 : ℕ) : ℝ) + 1) ^ 3 = 2 / (n : ℝ) ^ 3 := by
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast hn_pred
      rw [hcast]
    rwa [hleft, hright] at h
  have htail_bound :
      (∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 4)) ≤
        C * (2 / (n : ℝ) ^ 3) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left htail_four hCpos.le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 3 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 3‖ = ((n : ℝ)⁻¹) ^ 3 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  have hpow_rw : 2 * C * ‖((n : ℝ)⁻¹) ^ 3‖ = C * (2 / (n : ℝ) ^ 3) := by
    rw [htarget_norm]
    field_simp [hnpos.ne']
  calc
    ‖u n‖ = ‖∑' i : ℕ, d (i + n)‖ := by
      rw [htail_eq, norm_neg]
    _ ≤ ∑' i : ℕ, ‖d (i + n)‖ := hnorm_le
    _ ≤ ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 4) := htsum_le
    _ ≤ C * (2 / (n : ℝ) ^ 3) := htail_bound
    _ = 2 * C * ‖((n : ℝ)⁻¹) ^ 3‖ := hpow_rw.symm

private lemma inv_sub_inv_succ_sub_inv_sq_isBigO_inv_cube (a : ℝ) :
    (fun n : ℕ =>
      a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine IsBigO.of_bound ‖a‖ ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      (n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2 =
        -(1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1))) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
  have hden_pos : 0 < (n : ℝ) ^ 2 * ((n : ℝ) + 1) := by positivity
  have habs :
      |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2| =
        1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
    rw [hdiff, abs_neg, abs_of_nonneg]
    positivity
  have hden_le : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg (n : ℝ), hnpos.le]
  have htail_le :
      1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) ≤ 1 / (n : ℝ) ^ 3 := by
    exact one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) ^ 3) hden_le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 3 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 3‖ = ((n : ℝ)⁻¹) ^ 3 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  calc
    ‖a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2)‖
        = ‖a‖ *
          |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2| := by
          rw [norm_mul]
          simp [Real.norm_eq_abs]
    _ = ‖a‖ * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1))) := by rw [habs]
    _ ≤ ‖a‖ * (1 / (n : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left htail_le (norm_nonneg a)
    _ = ‖a‖ * ‖((n : ℝ)⁻¹) ^ 3‖ := by
          rw [htarget_norm, one_div, inv_pow]

private lemma inv_sub_inv_succ_sub_inv_sq_add_inv_cube_isBigO_inv_four (a : ℝ) :
    (fun n : ℕ =>
      a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
        ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
  refine IsBigO.of_bound ‖a‖ ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      (n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
          ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3 =
        1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1)) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
  have hden_pos : 0 < (n : ℝ) ^ 3 * ((n : ℝ) + 1) := by positivity
  have habs :
      |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
          ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3| =
        1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1)) := by
    rw [hdiff, abs_of_nonneg]
    positivity
  have hden_le : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 3 * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ) ^ 2), hnpos.le]
  have htail_le :
      1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1)) ≤ 1 / (n : ℝ) ^ 4 := by
    exact one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) ^ 4) hden_le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 4 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 4‖ = ((n : ℝ)⁻¹) ^ 4 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  calc
    ‖a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
        ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3)‖
        = ‖a‖ *
          |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
            ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3| := by
          rw [norm_mul]
          simp [Real.norm_eq_abs]
    _ = ‖a‖ * (1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1))) := by rw [habs]
    _ ≤ ‖a‖ * (1 / (n : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left htail_le (norm_nonneg a)
    _ = ‖a‖ * ‖((n : ℝ)⁻¹) ^ 4‖ := by
          rw [htarget_norm, one_div, inv_pow]

private lemma inv_sq_sub_inv_succ_sq_sub_two_inv_cube_isBigO_inv_four (a : ℝ) :
    (fun n : ℕ =>
      a * (((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
        2 * ((n : ℝ)⁻¹) ^ 3))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
  refine IsBigO.of_bound (5 * ‖a‖) ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      ((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
          2 * ((n : ℝ)⁻¹) ^ 3 =
        -((3 * (n : ℝ) + 2) / ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2)) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
    ring_nf
  have hden_pos : 0 < (n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2 := by positivity
  have hnum_nonneg : 0 ≤ 3 * (n : ℝ) + 2 := by positivity
  have habs :
      |((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
          2 * ((n : ℝ)⁻¹) ^ 3| =
        (3 * (n : ℝ) + 2) / ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2) := by
    rw [hdiff, abs_neg, abs_of_nonneg]
    positivity
  have htail_le :
      (3 * (n : ℝ) + 2) / ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2) ≤
        5 / (n : ℝ) ^ 4 := by
    rw [div_le_div_iff₀ hden_pos (by positivity : 0 < (n : ℝ) ^ 4)]
    have hbasic :
        (3 * (n : ℝ) + 2) * (n : ℝ) ≤ 5 * ((n : ℝ) + 1) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    calc
      (3 * (n : ℝ) + 2) * (n : ℝ) ^ 4
          = ((3 * (n : ℝ) + 2) * (n : ℝ)) * (n : ℝ) ^ 3 := by ring
      _ ≤ (5 * ((n : ℝ) + 1) ^ 2) * (n : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hbasic (by positivity)
      _ = 5 * ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2) := by ring
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 4 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 4‖ = ((n : ℝ)⁻¹) ^ 4 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  calc
    ‖a * (((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
        2 * ((n : ℝ)⁻¹) ^ 3)‖
        = ‖a‖ *
          |((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
            2 * ((n : ℝ)⁻¹) ^ 3| := by
          rw [norm_mul]
          simp [Real.norm_eq_abs]
    _ = ‖a‖ * ((3 * (n : ℝ) + 2) /
          ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2)) := by rw [habs]
    _ ≤ ‖a‖ * (5 / (n : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left htail_le (norm_nonneg a)
    _ = 5 * ‖a‖ * ‖((n : ℝ)⁻¹) ^ 4‖ := by
          rw [htarget_norm]
          field_simp [hnpos.ne']

private lemma gammaSecondError_succDiff_isBigO_inv_cube
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaSecondError α (n + 1) - gammaSecondError α n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have hY1 := gammaRatioNorm_sub_one_isBigO_inv hα
  have hStep2 := gammaStep_sub_one_isBigO_inv_sq α
  have hStep3 := gammaStep_sub_isBigO_inv_cube α
  have hprod0 := hY1.mul hStep2
  have hprod :
      (fun n : ℕ => (gammaRatioNorm α n - 1) * (gammaStep α n - 1))
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    refine hprod0.congr_right ?_
    intro n
    ring_nf
  have htail := inv_sub_inv_succ_sub_inv_sq_isBigO_inv_cube (c1 α)
  have hsum := (hStep3.add hprod).add htail
  have heq :
      (fun n : ℕ => gammaSecondError α (n + 1) - gammaSecondError α n) =ᶠ[atTop]
        (fun n : ℕ =>
          (gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2) +
            (gammaRatioNorm α n - 1) * (gammaStep α n - 1) +
            c1 α * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2)) := by
    filter_upwards [gammaRatioNorm_succ hα] with n hrec
    unfold gammaSecondError
    rw [hrec]
    ring_nf
  exact heq.trans_isBigO hsum

private lemma gammaSecondError_tendsto_zero
    {α : ℝ} (hα : 0 < α) :
    Tendsto (gammaSecondError α) atTop (𝓝 0) := by
  have hY := gammaRatioNorm_sub_one_isBigO_inv hα
  have hYlim : Tendsto (fun n : ℕ => gammaRatioNorm α n - 1) atTop (𝓝 0) :=
    hY.trans_tendsto (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcorr :
      Tendsto (fun n : ℕ => c1 α * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (c1 α)
  simpa [gammaSecondError] using hYlim.sub hcorr

private theorem gammaRatioNorm_second_order
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNorm α n - (1 + c1 α * (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  have hdiff := gammaSecondError_succDiff_isBigO_inv_cube hα
  have hlim := gammaSecondError_tendsto_zero hα
  have h := tendsto_zero_of_succDiff_isBigO_inv_cube hlim hdiff
  exact h.congr_left fun n => by
    unfold gammaSecondError
    ring_nf

private theorem gamma_ratio_second_order_aux {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
        (n : ℝ) ^ (α - 1) * (1 + α * (α - 1) / (2 * (n : ℝ))))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 3)) := by
  have hnorm := gammaRatioNorm_second_order hα
  have hnorm_rpow :
      (fun n : ℕ => gammaRatioNorm α n - (1 + c1 α * (n : ℝ)⁻¹))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := by
    exact hnorm.congr_right fun n => (rpow_neg_two_eq_inv_sq_nat n).symm
  have hp : (fun n : ℕ => (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1)) := isBigO_refl _ _
  have hmul :
      (fun n : ℕ =>
        (n : ℝ) ^ (α - 1) *
          (gammaRatioNorm α n - (1 + c1 α * (n : ℝ)⁻¹)))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 3)) := by
    exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := α - 1) (b := -(2 : ℝ)) (c := α - 3) hp hnorm_rpow (by linarith)
  have heq :
      (fun n : ℕ =>
        Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
          (n : ℝ) ^ (α - 1) * (1 + α * (α - 1) / (2 * (n : ℝ)))) =ᶠ[atTop]
        (fun n : ℕ =>
          (n : ℝ) ^ (α - 1) *
            (gammaRatioNorm α n - (1 + c1 α * (n : ℝ)⁻¹))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hpow_ne : (n : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hnpos _).ne'
    unfold gammaRatioNorm c1
    field_simp [hpow_ne, hnpos.ne']
  exact heq.trans_isBigO hmul

private theorem modelCoeff_secondOrder_aux {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ =>
      Ring.choose (α + n - 1) n -
        ((n : ℝ) ^ (α - 1) / Real.Gamma α) *
          (1 + α * (α - 1) / (2 * (n : ℝ))))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 3)) := by
  have hΓ : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have h := (gamma_ratio_second_order_aux hα).const_mul_left (Real.Gamma α)⁻¹
  refine h.congr_left ?_
  intro n
  rw [modelCoeff_eq_gamma_ratio hα n]
  field_simp [hΓ]

private lemma gammaRatioNorm_second_order_sub_form
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  exact (gammaRatioNorm_second_order hα).congr_left fun n => by ring_nf

private lemma const_mul_inv_isBigO_inv (a : ℝ) :
    (fun n : ℕ => a * (n : ℝ)⁻¹)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  exact (isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop).const_mul_left a

private lemma const_mul_inv_sq_isBigO_inv_sq' (a : ℝ) :
    (fun n : ℕ => a * ((n : ℝ)⁻¹) ^ 2)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  exact (isBigO_refl (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop).const_mul_left a

private lemma gammaThirdError_succDiff_isBigO_inv_four
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaThirdError α (n + 1) - gammaThirdError α n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
  have hStep4 := gammaStep_sub_third_isBigO_inv_four α
  have hStep2 := gammaStep_sub_one_isBigO_inv_sq α
  have hStep3 := gammaStep_sub_isBigO_inv_cube α
  have hY2 := gammaRatioNorm_second_order_sub_form hα
  have hprodY0 := hY2.mul hStep2
  have hprodY :
      (fun n : ℕ =>
        (gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹) *
          (gammaStep α n - 1))
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
    refine hprodY0.congr_right ?_
    intro n
    ring_nf
  have hcx := const_mul_inv_isBigO_inv (c1 α)
  have hprodC0 := hcx.mul hStep3
  have hprodC :
      (fun n : ℕ =>
        c1 α * (n : ℝ)⁻¹ *
          (gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2))
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
    refine hprodC0.congr_right ?_
    intro n
    ring_nf
  have htail1 := inv_sub_inv_succ_sub_inv_sq_add_inv_cube_isBigO_inv_four (c1 α)
  have htail2 := inv_sq_sub_inv_succ_sq_sub_two_inv_cube_isBigO_inv_four (c2 α)
  have hsum := (((hStep4.add hprodY).add hprodC).add htail1).add htail2
  have heq :
      (fun n : ℕ => gammaThirdError α (n + 1) - gammaThirdError α n) =ᶠ[atTop]
        (fun n : ℕ =>
          (gammaStep α n -
            (1 - c1 α * ((n : ℝ)⁻¹) ^ 2 +
              d3 α * ((n : ℝ)⁻¹) ^ 3)) +
            (gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹) *
              (gammaStep α n - 1) +
            c1 α * (n : ℝ)⁻¹ *
              (gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2) +
            c1 α * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
              ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3) +
            c2 α * (((n : ℝ)⁻¹) ^ 2 -
              ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
              2 * ((n : ℝ)⁻¹) ^ 3)) := by
    filter_upwards [gammaRatioNorm_succ hα] with n hrec
    unfold gammaThirdError
    rw [hrec]
    dsimp [c1, c2, d3]
    ring_nf
  exact heq.trans_isBigO hsum

private lemma gammaThirdError_tendsto_zero
    {α : ℝ} (hα : 0 < α) :
    Tendsto (gammaThirdError α) atTop (𝓝 0) := by
  have hY := gammaRatioNorm_second_order_sub_form hα
  have htarget :
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  have hYlim :
      Tendsto (fun n : ℕ => gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹)
        atTop (𝓝 0) :=
    hY.trans_tendsto htarget
  have hc2 :
      Tendsto (fun n : ℕ => c2 α * ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using htarget.const_mul (c2 α)
  change Tendsto
    (fun n : ℕ =>
      gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹ -
        c2 α * ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0)
  simpa only [sub_zero] using hYlim.sub hc2

private theorem gammaRatioNorm_third_order
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ =>
      gammaRatioNorm α n -
        (1 + c1 α * (n : ℝ)⁻¹ + c2 α * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have hdiff := gammaThirdError_succDiff_isBigO_inv_four hα
  have hlim := gammaThirdError_tendsto_zero hα
  have h := tendsto_zero_of_succDiff_isBigO_inv_four hlim hdiff
  exact h.congr_left fun n => by
    unfold gammaThirdError
    ring_nf

theorem gamma_ratio_third_order {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
        (n : ℝ) ^ (α - 1) *
          (1 + (α * (α - 1) / 2) * (n : ℝ)⁻¹ +
            (α * (α - 1) * (α - 2) * (3 * α - 1) / 24) *
              ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 4)) := by
  have hnorm := gammaRatioNorm_third_order hα
  have hnorm_rpow :
      (fun n : ℕ =>
        gammaRatioNorm α n -
          (1 + c1 α * (n : ℝ)⁻¹ + c2 α * ((n : ℝ)⁻¹) ^ 2))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) := by
    exact hnorm.congr_right fun n => (rpow_neg_three_eq_inv_cube_nat n).symm
  have hp : (fun n : ℕ => (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1)) := isBigO_refl _ _
  have hmul :
      (fun n : ℕ =>
        (n : ℝ) ^ (α - 1) *
          (gammaRatioNorm α n -
            (1 + c1 α * (n : ℝ)⁻¹ + c2 α * ((n : ℝ)⁻¹) ^ 2)))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 4)) := by
    exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := α - 1) (b := -(3 : ℝ)) (c := α - 4) hp hnorm_rpow (by linarith)
  have heq :
      (fun n : ℕ =>
        Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
          (n : ℝ) ^ (α - 1) *
            (1 + (α * (α - 1) / 2) * (n : ℝ)⁻¹ +
              (α * (α - 1) * (α - 2) * (3 * α - 1) / 24) *
                ((n : ℝ)⁻¹) ^ 2)) =ᶠ[atTop]
        (fun n : ℕ =>
          (n : ℝ) ^ (α - 1) *
            (gammaRatioNorm α n -
              (1 + c1 α * (n : ℝ)⁻¹ + c2 α * ((n : ℝ)⁻¹) ^ 2))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hpow_ne : (n : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hnpos _).ne'
    unfold gammaRatioNorm c1 c2
    field_simp [hpow_ne]
  exact heq.trans_isBigO hmul

theorem modelCoeff_thirdOrder {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ =>
      Ring.choose (α + n - 1) n -
        ((n : ℝ) ^ (α - 1) / Real.Gamma α) *
          (1 + (α * (α - 1) / 2) * (n : ℝ)⁻¹ +
            (α * (α - 1) * (α - 2) * (3 * α - 1) / 24) *
              ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 4)) := by
  have hΓ : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have h := (gamma_ratio_third_order hα).const_mul_left (Real.Gamma α)⁻¹
  refine h.congr_left ?_
  intro n
  rw [modelCoeff_eq_gamma_ratio hα n]
  field_simp [hΓ]
