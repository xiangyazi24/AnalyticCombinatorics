import Mathlib

/-!
# Kernel integral estimates

This file proves the reusable real-variable kernel estimate used by the
circle-only transfer argument.
-/

open Complex
open MeasureTheory
open scoped Real

private lemma exp_real_mul_I (θ : ℝ) :
    Complex.exp (θ * Complex.I) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  have h := Complex.exp_mul_I (θ : ℂ)
  simpa [Complex.ofReal_cos, Complex.ofReal_sin] using h

lemma circleKernel_norm_sq (r θ : ℝ) :
    ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 =
      (1 - r) ^ 2 + 2 * r * (1 - Real.cos θ) := by
  rw [← Complex.normSq_eq_norm_sq]
  rw [exp_real_mul_I]
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, sub_zero,
    zero_sub, zero_mul, mul_zero]
  ring_nf
  rw [Real.sin_sq]
  ring

private lemma two_div_pi_sq_le_one : (2 : ℝ) / Real.pi ^ 2 ≤ 1 := by
  have hpi2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  have hsq : (2 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by
    exact pow_le_pow_left₀ (by norm_num) hpi2 2
  have htwo_le_sq : (2 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  exact (div_le_one (sq_pos_of_pos Real.pi_pos)).2 htwo_le_sq

lemma circleKernel_norm_sq_lower (r θ : ℝ) (hθ : |θ| ≤ Real.pi)
    (hr : (1 : ℝ) / 2 ≤ r) :
    (2 / Real.pi ^ 2) * ((1 - r) ^ 2 + θ ^ 2) ≤
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 := by
  rw [circleKernel_norm_sq]
  have hc_le_one : (2 : ℝ) / Real.pi ^ 2 ≤ 1 := two_div_pi_sq_le_one
  have hs1 : (2 / Real.pi ^ 2) * (1 - r) ^ 2 ≤ (1 - r) ^ 2 := by
    nlinarith [sq_nonneg (1 - r)]
  have hcos_le := Real.cos_le_one_sub_mul_cos_sq hθ
  have hcos : (2 / Real.pi ^ 2) * θ ^ 2 ≤ 1 - Real.cos θ := by
    linarith
  have hcos_nonneg : 0 ≤ 1 - Real.cos θ := by
    nlinarith [Real.cos_le_one θ]
  have htheta_nonneg : 0 ≤ (2 / Real.pi ^ 2) * θ ^ 2 := by positivity
  have hr2 : 1 ≤ 2 * r := by nlinarith
  have hs2 : (2 / Real.pi ^ 2) * θ ^ 2 ≤ 2 * r * (1 - Real.cos θ) := by
    nlinarith [hcos, hcos_nonneg, htheta_nonneg, hr2]
  nlinarith

private lemma rho_mul_rpow_neg_eq (ρ β : ℝ) (hρ : 0 < ρ) :
    ρ * ρ ^ (-β) = ρ ^ (1 - β) := by
  have h := Real.rpow_add hρ 1 (-β)
  rw [Real.rpow_one] at h
  calc
    ρ * ρ ^ (-β) = ρ ^ (1 + -β) := h.symm
    _ = ρ ^ (1 - β) := by ring_nf

private lemma modelContinuous (ρ β : ℝ) (hρ : 0 < ρ) :
    Continuous fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2) := by
  refine (continuous_const.add (continuous_id.pow 2)).rpow_const ?_
  intro θ
  left
  change ρ ^ 2 + θ ^ 2 ≠ 0
  nlinarith [sq_pos_of_pos hρ, sq_nonneg θ]

private lemma modelIntervalIntegrable (ρ β a b : ℝ) (hρ : 0 < ρ) :
    IntervalIntegrable (fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) volume a b := by
  exact (modelContinuous ρ β hρ).intervalIntegrable a b

private lemma rpow_sq (x a : ℝ) (hx : 0 ≤ x) :
    (x ^ 2) ^ a = x ^ (2 * a) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  norm_num

private lemma rpow_sq_neg_half (x β : ℝ) (hx : 0 ≤ x) :
    (x ^ 2) ^ (-β / 2) = x ^ (-β) := by
  rw [rpow_sq x (-β / 2) hx]
  congr 1
  ring

lemma circleKernel_rpow_le_model (r θ β : ℝ) (hθ : |θ| ≤ Real.pi)
    (hr : (1 : ℝ) / 2 ≤ r) (h1r : 0 < 1 - r) (hβ0 : 0 ≤ β) :
    ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) ≤
      ((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) *
        (((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2)) := by
  let z : ℂ := (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)
  let c : ℝ := (2 : ℝ) / Real.pi ^ 2
  let A : ℝ := (1 - r) ^ 2 + θ ^ 2
  have hcpos : 0 < c := by positivity
  have hApos : 0 < A := by
    dsimp [A]
    nlinarith [sq_pos_of_pos h1r, sq_nonneg θ]
  have hbase_pos : 0 < c * A := mul_pos hcpos hApos
  have hlow : c * A ≤ ‖z‖ ^ 2 := by
    dsimp [z, c, A]
    exact circleKernel_norm_sq_lower r θ hθ hr
  have hpow := Real.rpow_le_rpow_of_nonpos hbase_pos hlow (by nlinarith : -β / 2 ≤ 0)
  calc
    ‖z‖ ^ (-β) = (‖z‖ ^ 2) ^ (-β / 2) := by
      rw [rpow_sq_neg_half ‖z‖ β (norm_nonneg z)]
    _ ≤ (c * A) ^ (-β / 2) := hpow
    _ = c ^ (-β / 2) * A ^ (-β / 2) := by
      rw [Real.mul_rpow hcpos.le hApos.le]

private lemma model_le_rho_neg_beta {ρ β θ : ℝ} (hρ : 0 < ρ) (hβ0 : 0 ≤ β) :
    (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤ ρ ^ (-β) := by
  have hbase_pos : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hle : ρ ^ 2 ≤ ρ ^ 2 + θ ^ 2 := by nlinarith [sq_nonneg θ]
  have hpow := Real.rpow_le_rpow_of_nonpos hbase_pos hle (by nlinarith : -β / 2 ≤ 0)
  rwa [rpow_sq_neg_half ρ β hρ.le] at hpow

private lemma integral_model_zero_rho_le {ρ β : ℝ} (hρ : 0 < ρ) (hβ0 : 0 ≤ β) :
    ∫ θ in (0 : ℝ)..ρ, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤ ρ ^ (1 - β) := by
  have hmono := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := ρ)
    hρ.le (modelIntervalIntegrable ρ β 0 ρ hρ) intervalIntegrable_const
    (fun θ _ => model_le_rho_neg_beta (ρ := ρ) (β := β) (θ := θ) hρ hβ0)
  calc
    ∫ θ in (0 : ℝ)..ρ, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤
        ∫ _θ in (0 : ℝ)..ρ, ρ ^ (-β) := hmono
    _ = ρ ^ (1 - β) := by
      rw [intervalIntegral.integral_const]
      simp [rho_mul_rpow_neg_eq ρ β hρ]

private lemma model_le_theta_neg_beta {ρ β θ : ℝ} (hθ : 0 < θ) (hβ0 : 0 ≤ β) :
    (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤ θ ^ (-β) := by
  have hbase_pos : 0 < θ ^ 2 := sq_pos_of_pos hθ
  have hle : θ ^ 2 ≤ ρ ^ 2 + θ ^ 2 := by nlinarith [sq_nonneg ρ]
  have hpow := Real.rpow_le_rpow_of_nonpos hbase_pos hle (by nlinarith : -β / 2 ≤ 0)
  rwa [rpow_sq_neg_half θ β hθ.le] at hpow

private lemma rpowNegIntervalIntegrable {ρ b β : ℝ} (hρ : 0 < ρ) (hρb : ρ ≤ b) :
    IntervalIntegrable (fun θ : ℝ => θ ^ (-β)) volume ρ b := by
  refine (continuousOn_id.rpow_const ?_).intervalIntegrable
  intro θ hθ
  left
  rw [Set.uIcc_of_le hρb] at hθ
  have hθpos : 0 < θ := lt_of_lt_of_le hρ hθ.1
  exact hθpos.ne'

private lemma integral_rpow_neg_le {ρ β : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ Real.pi)
    (hβ : 1 < β) :
    ∫ θ in ρ..Real.pi, θ ^ (-β) ≤ (β - 1)⁻¹ * ρ ^ (1 - β) := by
  have hnot : (-β) ≠ -1 := by linarith
  have hznot : (0 : ℝ) ∉ Set.uIcc ρ Real.pi := by
    rw [Set.uIcc_of_le hρπ]
    intro hmem
    exact (not_lt_of_ge hmem.1) hρ
  rw [integral_rpow (a := ρ) (b := Real.pi) (r := -β) (Or.inr ⟨hnot, hznot⟩)]
  have hden_pos : 0 < β - 1 := by linarith
  have hpi_nonneg : 0 ≤ Real.pi ^ (1 - β) := by positivity
  calc
    (Real.pi ^ (-β + 1) - ρ ^ (-β + 1)) / (-β + 1)
        = (ρ ^ (1 - β) - Real.pi ^ (1 - β)) / (β - 1) := by
          have hden_ne : β - 1 ≠ 0 := by linarith
          have hden_ne' : 1 - β ≠ 0 := by linarith
          rw [show -β + 1 = 1 - β by ring]
          field_simp [hden_ne, hden_ne']
          ring
    _ ≤ ρ ^ (1 - β) / (β - 1) := by
      exact div_le_div_of_nonneg_right (by nlinarith) hden_pos.le
    _ = (β - 1)⁻¹ * ρ ^ (1 - β) := by field_simp

private lemma integral_model_rho_pi_le {ρ β : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ Real.pi)
    (hβ : 1 < β) :
    ∫ θ in ρ..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤
      (β - 1)⁻¹ * ρ ^ (1 - β) := by
  have hβ0 : 0 ≤ β := by linarith
  have hmono := intervalIntegral.integral_mono_on (a := ρ) (b := Real.pi)
    hρπ (modelIntervalIntegrable ρ β ρ Real.pi hρ)
    (rpowNegIntervalIntegrable (ρ := ρ) (b := Real.pi) (β := β) hρ hρπ)
    (fun θ hθ => model_le_theta_neg_beta (ρ := ρ) (β := β) (θ := θ)
      (lt_of_lt_of_le hρ hθ.1) hβ0)
  exact hmono.trans (integral_rpow_neg_le hρ hρπ hβ)

private lemma integral_model_zero_pi_le {ρ β : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ 1)
    (hβ : 1 < β) :
    ∫ θ in (0 : ℝ)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤
      (1 + (β - 1)⁻¹) * ρ ^ (1 - β) := by
  have hβ0 : 0 ≤ β := by linarith
  have hρπ : ρ ≤ Real.pi := by
    have h1π : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
    exact hρle.trans h1π
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (modelIntervalIntegrable ρ β 0 ρ hρ)
    (modelIntervalIntegrable ρ β ρ Real.pi hρ)
  calc
    ∫ θ in (0 : ℝ)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)
        = (∫ θ in (0 : ℝ)..ρ, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) +
          (∫ θ in ρ..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) := hsplit.symm
    _ ≤ ρ ^ (1 - β) + (β - 1)⁻¹ * ρ ^ (1 - β) := by
      exact add_le_add (integral_model_zero_rho_le hρ hβ0)
        (integral_model_rho_pi_le hρ hρπ hβ)
    _ = (1 + (β - 1)⁻¹) * ρ ^ (1 - β) := by ring

private lemma model_even (ρ β θ : ℝ) :
    (ρ ^ 2 + (-θ) ^ 2) ^ (-β / 2) = (ρ ^ 2 + θ ^ 2) ^ (-β / 2) := by
  congr 1
  ring

private lemma integral_model_neg_pi_zero_eq {ρ β : ℝ} :
    ∫ θ in (-Real.pi)..(0 : ℝ), (ρ ^ 2 + θ ^ 2) ^ (-β / 2) =
      ∫ θ in (0 : ℝ)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) := by
  calc
    ∫ θ in (-Real.pi)..(0 : ℝ), (ρ ^ 2 + θ ^ 2) ^ (-β / 2)
        = ∫ θ in (-Real.pi)..(0 : ℝ), (ρ ^ 2 + (-θ) ^ 2) ^ (-β / 2) := by
          apply intervalIntegral.integral_congr
          intro θ _
          exact (model_even ρ β θ).symm
    _ = ∫ θ in (0 : ℝ)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) := by
      simpa only [neg_zero, neg_neg] using
        (intervalIntegral.integral_comp_neg
          (f := fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2))
          (a := -Real.pi) (b := (0 : ℝ)))

lemma modelKernel_integral_bound {ρ β : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ 1)
    (hβ : 1 < β) :
    ∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) ≤
      (2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β) := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (modelIntervalIntegrable ρ β (-Real.pi) 0 hρ)
    (modelIntervalIntegrable ρ β 0 Real.pi hρ)
  calc
    ∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)
        = (∫ θ in (-Real.pi)..(0 : ℝ), (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) +
          (∫ θ in (0 : ℝ)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) := hsplit.symm
    _ = 2 * (∫ θ in (0 : ℝ)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) := by
      rw [integral_model_neg_pi_zero_eq]
      ring
    _ ≤ 2 * ((1 + (β - 1)⁻¹) * ρ ^ (1 - β)) := by
      exact mul_le_mul_of_nonneg_left (integral_model_zero_pi_le hρ hρle hβ) (by norm_num)
    _ = (2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β) := by ring

private lemma one_div_nat_rpow (β : ℝ) {n : ℕ} (hn : 0 < n) :
    ((1 : ℝ) / n) ^ (1 - β) = (n : ℝ) ^ (β - 1) := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  rw [one_div, Real.inv_rpow hn_nonneg]
  rw [show 1 - β = -(β - 1) by ring]
  rw [Real.rpow_neg hn_nonneg]
  simp

private lemma circleKernelIntervalIntegrable (r β : ℝ) (hr : (1 : ℝ) / 2 ≤ r)
    (h1r : 0 < 1 - r) :
    IntervalIntegrable
      (fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β))
      volume (-Real.pi) Real.pi := by
  refine ((by fun_prop :
      Continuous fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖)
    |>.continuousOn.rpow_const ?_).intervalIntegrable
  intro θ hθ
  left
  have hθIcc : θ ∈ Set.Icc (-Real.pi) Real.pi := by
    have hneg_le : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
    rw [Set.uIcc_of_le hneg_le] at hθ
    exact hθ
  have hθabs : |θ| ≤ Real.pi := by
    rw [abs_le]
    exact ⟨hθIcc.1, hθIcc.2⟩
  let z : ℂ := (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)
  have hcpos : 0 < (2 : ℝ) / Real.pi ^ 2 := by positivity
  have hApos : 0 < (1 - r) ^ 2 + θ ^ 2 := by
    nlinarith [sq_pos_of_pos h1r, sq_nonneg θ]
  have hlow : ((2 : ℝ) / Real.pi ^ 2) * ((1 - r) ^ 2 + θ ^ 2) ≤ ‖z‖ ^ 2 := by
    dsimp [z]
    exact circleKernel_norm_sq_lower r θ hθabs hr
  have hnormsq_pos : 0 < ‖z‖ ^ 2 := lt_of_lt_of_le (mul_pos hcpos hApos) hlow
  have hnorm_pos : 0 < ‖z‖ := by nlinarith [norm_nonneg z]
  exact hnorm_pos.ne'

private lemma circleKernel_integral_bound_nat_ge_two {β : ℝ} (hβ : 1 < β) :
    ∀ n : ℕ, 2 ≤ n →
      ∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - ((1 : ℝ) - (1 : ℝ) / n : ℂ) *
              Complex.exp (θ * Complex.I)‖ ^ (-β) ≤
        (((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) *
          (2 + 2 * (β - 1)⁻¹)) * (n : ℝ) ^ (β - 1) := by
  intro n hn2
  have hβ0 : 0 ≤ β := by linarith
  have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hρpos : 0 < (1 : ℝ) / n := div_pos zero_lt_one hnpos
  have hρle : (1 : ℝ) / n ≤ 1 := by
    rw [div_le_one hnpos]
    exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) hn2)
  let ρ : ℝ := (1 : ℝ) / n
  let r : ℝ := 1 - ρ
  have hr : (1 : ℝ) / 2 ≤ r := by
    dsimp [r, ρ]
    have htwo_le_n : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hdiv_le : (1 : ℝ) / n ≤ 1 / 2 := by
      rw [one_div_le_one_div hnpos (by norm_num : (0 : ℝ) < 2)]
      exact htwo_le_n
    linarith
  have h1r : 0 < 1 - r := by
    dsimp [r, ρ]
    simpa using hρpos
  have hconst_nonneg : 0 ≤ ((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) := by positivity
  have hmono := intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi)
    (by linarith [Real.pi_pos])
    (circleKernelIntervalIntegrable r β hr h1r)
    ((modelIntervalIntegrable ρ β (-Real.pi) Real.pi hρpos).const_mul
      (((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2)))
    (fun θ hθ => by
      have hθabs : |θ| ≤ Real.pi := by
        rw [abs_le]
        exact ⟨hθ.1, hθ.2⟩
      have hle := circleKernel_rpow_le_model r θ β hθabs hr h1r hβ0
      simpa [r, ρ, Complex.real_smul] using hle)
  calc
    ∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - ((1 : ℝ) - (1 : ℝ) / n : ℂ) *
            Complex.exp (θ * Complex.I)‖ ^ (-β)
        = ∫ θ in (-Real.pi)..Real.pi,
            ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) := by
          simp [r, ρ]
    _ ≤ ∫ θ in (-Real.pi)..Real.pi,
        ((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) *
          ((ρ ^ 2 + θ ^ 2) ^ (-β / 2)) := hmono
    _ = ((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) *
        (∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) := by
          rw [intervalIntegral.integral_const_mul]
    _ ≤ ((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) *
        ((2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β)) := by
          exact mul_le_mul_of_nonneg_left (modelKernel_integral_bound hρpos hρle hβ)
            hconst_nonneg
    _ = (((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) *
          (2 + 2 * (β - 1)⁻¹)) * (n : ℝ) ^ (β - 1) := by
          rw [one_div_nat_rpow β hnpos_nat]
          ring

lemma modelKernel_integral_bound_nat {β : ℝ} (hβ : 1 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ∫ θ in (-Real.pi)..Real.pi,
          (((1 : ℝ) / n) ^ 2 + θ ^ 2) ^ (-β / 2) ≤
        C * (n : ℝ) ^ (β - 1) := by
  refine ⟨2 + 2 * (β - 1)⁻¹, ?_, ?_⟩
  · have hpos : 0 < β - 1 := by linarith
    positivity
  · intro n hn
    have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hρpos : 0 < (1 : ℝ) / n := div_pos zero_lt_one hnpos
    have hρle : (1 : ℝ) / n ≤ 1 := by
      rw [div_le_one hnpos]
      exact_mod_cast hn
    calc
      ∫ θ in (-Real.pi)..Real.pi,
          (((1 : ℝ) / n) ^ 2 + θ ^ 2) ^ (-β / 2)
          ≤ (2 + 2 * (β - 1)⁻¹) * ((1 : ℝ) / n) ^ (1 - β) :=
            modelKernel_integral_bound hρpos hρle hβ
      _ = (2 + 2 * (β - 1)⁻¹) * (n : ℝ) ^ (β - 1) := by
        rw [one_div_nat_rpow β hnpos_nat]

lemma circleKernel_integral_bound_nat {β : ℝ} (hβ : 1 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - ((1 : ℝ) - (1 : ℝ) / n) •
              Complex.exp (θ * Complex.I)‖ ^ (-β) ≤
        C * (n : ℝ) ^ (β - 1) := by
  let C0 : ℝ :=
    ((2 : ℝ) / Real.pi ^ 2) ^ (-β / 2) * (2 + 2 * (β - 1)⁻¹)
  let C : ℝ := C0 + 2 * Real.pi
  have hden_pos : 0 < β - 1 := by linarith
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_nonneg, ?_⟩
  intro n hn
  by_cases hn2 : 2 ≤ n
  · have hbase := circleKernel_integral_bound_nat_ge_two hβ n hn2
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    calc
      ∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - ((1 : ℝ) - (1 : ℝ) / n) •
              Complex.exp (θ * Complex.I)‖ ^ (-β)
          = ∫ θ in (-Real.pi)..Real.pi,
              ‖(1 : ℂ) - ((1 : ℝ) - (1 : ℝ) / n : ℂ) *
                  Complex.exp (θ * Complex.I)‖ ^ (-β) := by
            apply intervalIntegral.integral_congr
            intro θ _
            simp [Complex.real_smul]
      _ ≤ C0 * (n : ℝ) ^ (β - 1) := by
        simpa [C0] using hbase
      _ ≤ C * (n : ℝ) ^ (β - 1) := by
        exact mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [Real.pi_pos])
          (Real.rpow_nonneg hn_nonneg (β - 1))
  · have hn_eq : n = 1 := by omega
    subst n
    calc
      ∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - ((1 : ℝ) - (1 : ℝ) / (1 : ℕ)) •
              Complex.exp (θ * Complex.I)‖ ^ (-β)
          = ∫ _θ in (-Real.pi)..Real.pi, (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro θ _
            norm_num [Complex.real_smul]
      _ = 2 * Real.pi := by
        rw [intervalIntegral.integral_const]
        simp
        ring
      _ ≤ C * ((1 : ℕ) : ℝ) ^ (β - 1) := by
        simp
        dsimp [C]
        nlinarith [hC0_nonneg, Real.pi_pos]
