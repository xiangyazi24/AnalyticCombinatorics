import AnalyticCombinatorics.Ch8.SaddlePoint.GaussianCore
import Mathlib.Probability.Distributions.Gaussian.Real

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Gaussian moments for the saddle correction

This file records the standard Gaussian moments needed by the second-order
saddle correction.
-/

open Complex Filter Asymptotics MeasureTheory ProbabilityTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

private def gaussianMGFCore (t : ℝ) : ℝ :=
  Real.exp (t ^ 2 / 2)

private lemma deriv_gaussianMGFCore :
    deriv gaussianMGFCore = fun t : ℝ => t * gaussianMGFCore t := by
  ext t
  unfold gaussianMGFCore
  rw [_root_.deriv_exp (by fun_prop)]
  simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow,
    Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
  ring

private lemma deriv_t_mul_gaussianMGFCore :
    deriv (fun t : ℝ => t * gaussianMGFCore t) =
      fun t : ℝ => (1 + t ^ 2) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp
  ring_nf

private lemma deriv_poly2_mul_gaussianMGFCore :
    deriv (fun t : ℝ => (1 + t ^ 2) * gaussianMGFCore t) =
      fun t : ℝ => (3 * t + t ^ 3) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.add, deriv_fun_add, deriv_const',
    deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
  ring_nf

private lemma deriv_poly3_mul_gaussianMGFCore :
    deriv (fun t : ℝ => (3 * t + t ^ 3) * gaussianMGFCore t) =
      fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one]
  have hpoly : deriv (fun t : ℝ => 3 * t + t ^ 3) t = 3 + 3 * t ^ 2 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 3 * y) t = 3 := by
      rw [deriv_const_mul_field (u := (3 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hpow : deriv (fun y : ℝ => y ^ 3) t = 3 * t ^ 2 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hpow]
  rw [hpoly]
  ring_nf

private lemma deriv_poly4_mul_gaussianMGFCore :
    deriv (fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * gaussianMGFCore t) =
      fun t : ℝ => (15 * t + 10 * t ^ 3 + t ^ 5) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const', deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one,
    pow_one, deriv_id'', mul_one, zero_add]
  have hpoly :
      deriv (fun t : ℝ => 3 + 6 * t ^ 2 + t ^ 4) t =
        12 * t + 4 * t ^ 3 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hconst : deriv (fun _ : ℝ => (3 : ℝ)) t = 0 := by
      rw [deriv_const']
    have hquad : deriv (fun y : ℝ => 6 * y ^ 2) t = 12 * t := by
      rw [deriv_const_mul_field (u := (6 : ℝ)) (v := fun y : ℝ => y ^ 2) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquart : deriv (fun y : ℝ => y ^ 4) t = 4 * t ^ 3 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hconst, hquad, hquart]
  rw [hpoly]
  ring_nf

private lemma deriv_poly5_mul_gaussianMGFCore :
    deriv (fun t : ℝ => (15 * t + 10 * t ^ 3 + t ^ 5) * gaussianMGFCore t) =
      fun t : ℝ => (15 + 45 * t ^ 2 + 15 * t ^ 4 + t ^ 6) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one]
  have hpoly :
      deriv (fun t : ℝ => 15 * t + 10 * t ^ 3 + t ^ 5) t =
        15 + 30 * t ^ 2 + 5 * t ^ 4 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 15 * y) t = 15 := by
      rw [deriv_const_mul_field (u := (15 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hcubic : deriv (fun y : ℝ => 10 * y ^ 3) t = 30 * t ^ 2 := by
      rw [deriv_const_mul_field (u := (10 : ℝ)) (v := fun y : ℝ => y ^ 3) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquint : deriv (fun y : ℝ => y ^ 5) t = 5 * t ^ 4 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hcubic, hquint]
  rw [hpoly]
  ring_nf

lemma gaussianReal_moment_two :
    (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1)) = (1 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1))
        = iteratedDeriv 2 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 1 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 2 gaussianMGFCore 0 = 1
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCore, deriv_t_mul_gaussianMGFCore]
      simp [gaussianMGFCore]

lemma gaussianReal_moment_three :
    (∫ x : ℝ, x ^ 3 ∂(gaussianReal 0 1)) = (0 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 3 ∂(gaussianReal 0 1))
        = iteratedDeriv 3 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 0 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 3 gaussianMGFCore 0 = 0
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCore, deriv_t_mul_gaussianMGFCore,
        deriv_poly2_mul_gaussianMGFCore]
      simp [gaussianMGFCore]

lemma gaussianReal_moment_four :
    (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1)) = (3 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1))
        = iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 3 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 4 gaussianMGFCore 0 = 3
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCore, deriv_t_mul_gaussianMGFCore,
        deriv_poly2_mul_gaussianMGFCore, deriv_poly3_mul_gaussianMGFCore]
      simp [gaussianMGFCore]

lemma gaussianReal_moment_six :
    (∫ x : ℝ, x ^ 6 ∂(gaussianReal 0 1)) = (15 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 6 ∂(gaussianReal 0 1))
        = iteratedDeriv 6 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 15 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 6 gaussianMGFCore 0 = 15
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCore, deriv_t_mul_gaussianMGFCore,
        deriv_poly2_mul_gaussianMGFCore, deriv_poly3_mul_gaussianMGFCore,
        deriv_poly4_mul_gaussianMGFCore, deriv_poly5_mul_gaussianMGFCore]
      simp [gaussianMGFCore]

lemma gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  simp [gaussianPDFReal]

private lemma gaussian_weighted_moment_from_probability (k : ℕ) (m : ℝ)
    (hm : (∫ x : ℝ, x ^ k ∂(gaussianReal 0 1)) = m) :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k) =
      Real.sqrt (2 * Real.pi) * m := by
  have hprob :=
    integral_gaussianReal_eq_integral_smul
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
      (f := fun x : ℝ => x ^ k) (by norm_num : (1 : ℝ≥0) ≠ 0)
  rw [hm] at hprob
  rw [show (∫ x : ℝ, gaussianPDFReal 0 1 x • x ^ k) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k by
        simp_rw [gaussianPDFReal_zero_one, smul_eq_mul]
        rw [← integral_const_mul]
        apply integral_congr_ae
        refine ae_of_all _ ?_
        intro x
        ring] at hprob
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := hsqrt_pos.ne'
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k)
        = Real.sqrt (2 * Real.pi) *
            ((Real.sqrt (2 * Real.pi))⁻¹ *
              ∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k) := by
          field_simp [hsqrt_ne]
    _ = Real.sqrt (2 * Real.pi) * m := by rw [← hprob]

lemma gaussian_weighted_moment_two :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 2) =
      Real.sqrt (2 * Real.pi) := by
  simpa using gaussian_weighted_moment_from_probability 2 1 gaussianReal_moment_two

lemma gaussian_weighted_moment_three :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 3) = (0 : ℝ) := by
  simpa using gaussian_weighted_moment_from_probability 3 0 gaussianReal_moment_three

lemma gaussian_weighted_moment_four :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 4) =
      3 * Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 4)
        = Real.sqrt (2 * Real.pi) * 3 :=
          gaussian_weighted_moment_from_probability 4 3 gaussianReal_moment_four
    _ = 3 * Real.sqrt (2 * Real.pi) := by ring

lemma gaussian_weighted_moment_six :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 6) =
      15 * Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 6)
        = Real.sqrt (2 * Real.pi) * 15 :=
          gaussian_weighted_moment_from_probability 6 15 gaussianReal_moment_six
    _ = 15 * Real.sqrt (2 * Real.pi) := by ring
