import AnalyticCombinatorics.Ch4.Analytic.SingularityGeneral
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Central binomial coefficients from the general singularity scale

This file specializes the general `α`-scale
`[z^n] (1 - z)^{-α} ~ n^{α-1} / Γ(α)` to `α = 1/2`, obtaining the
classical central-binomial estimate
`Nat.centralBinom n ~ 4^n / sqrt (π n)`.
-/

open Filter Asymptotics
open scoped Topology BigOperators

lemma half_not_neg_nat : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -m := by
  intro m hm
  have hr := congrArg Complex.re hm
  have hmnonneg : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  norm_num at hr
  linarith

lemma half_choose_step (n : ℕ) :
    ((n + 1 : ℂ) *
        Ring.choose ((1 / 2 : ℂ) + (n + 1 : ℕ) - 1) (n + 1)) =
      (((1 / 2 : ℂ) + n) *
        Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n) := by
  have h := Ring.choose_smul_choose (R := ℂ)
    (((1 / 2 : ℂ) + (n + 1 : ℕ) - 1)) (n := n + 1) (k := 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  simpa [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right, Nat.cast_add,
    Nat.cast_one, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using h

lemma centralBinom_eq_four_pow_mul_half_choose (n : ℕ) :
    ((n.centralBinom : ℂ) =
      (4 : ℂ) ^ n * Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n) := by
  induction n with
  | zero =>
      simp [Nat.centralBinom]
  | succ n ih =>
      have hn1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      apply (mul_right_inj' hn1).mp
      calc
        (n + 1 : ℂ) * (((n + 1).centralBinom : ℂ))
            = (2 : ℂ) * (2 * n + 1) * (n.centralBinom : ℂ) := by
              exact_mod_cast Nat.succ_mul_centralBinom_succ n
        _ = (2 : ℂ) * (2 * n + 1) *
              ((4 : ℂ)^n * Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n) := by
              rw [ih]
        _ = (n + 1 : ℂ) *
              ((4 : ℂ)^(n + 1) *
                Ring.choose ((1 / 2 : ℂ) + (n + 1 : ℕ) - 1) (n + 1)) := by
              rw [pow_succ]
              rw [show (n + 1 : ℂ) *
                    ((4 : ℂ)^n * 4 *
                      Ring.choose ((1 / 2 : ℂ) + (n + 1 : ℕ) - 1) (n + 1)) =
                    ((4 : ℂ)^n * 4) *
                      ((n + 1 : ℂ) *
                        Ring.choose ((1 / 2 : ℂ) + (n + 1 : ℕ) - 1) (n + 1)) by
                ring]
              rw [half_choose_step n]
              ring

private lemma half_scale_inner (n : ℕ) (hn : n ≠ 0) :
    (((n : ℂ)^((1 / 2 : ℂ) - 1)) /
          ((Real.pi : ℂ) ^ (1 / 2 : ℂ))) =
      (1 / (Real.sqrt (Real.pi * (n : ℝ)) : ℂ)) := by
  have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnreal_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hnroot_sq : ((n : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = (n : ℂ) := by
    have hcpow : (((n : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
        (n : ℂ) ^ (1 / 2 : ℂ) := by
      simpa using Complex.ofReal_cpow hnreal_nonneg (1 / 2 : ℝ)
    rw [← hcpow]
    rw [← Complex.ofReal_pow]
    rw [← Real.sqrt_eq_rpow]
    rw [Real.sq_sqrt hnreal_nonneg]
    norm_num
  have hnroot_ne : (n : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hpiroot_ne : (Real.pi : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hn_sqrt : (Real.sqrt (n : ℝ) : ℂ) = (n : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa using Complex.ofReal_cpow hnreal_nonneg (1 / 2 : ℝ)
  have hpi_sqrt : (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa using Complex.ofReal_cpow Real.pi_nonneg (1 / 2 : ℝ)
  have hsqrt_mul : (Real.sqrt (Real.pi * (n : ℝ)) : ℂ) =
      ((Real.pi : ℂ) ^ (1 / 2 : ℂ)) * ((n : ℂ) ^ (1 / 2 : ℂ)) := by
    rw [Real.sqrt_mul Real.pi_nonneg (n : ℝ)]
    rw [Complex.ofReal_mul, hpi_sqrt, hn_sqrt]
  rw [Complex.cpow_sub _ _ hncast, Complex.cpow_one, hsqrt_mul]
  field_simp [hncast, hnroot_ne, hpiroot_ne]
  exact hnroot_sq

lemma half_scale_to_sqrt_pi_n :
    (fun n : ℕ =>
      (4 : ℂ)^n *
        (((n : ℂ)^((1 / 2 : ℂ) - 1)) /
          ((Real.pi : ℂ) ^ (1 / 2 : ℂ)))) =ᶠ[atTop]
    (fun n : ℕ =>
      (4 : ℂ)^n / (Real.sqrt (Real.pi * (n : ℝ)) : ℂ)) := by
  exact (eventually_ne_atTop 0).mono fun n hn => by
    dsimp
    rw [half_scale_inner n hn]
    ring

theorem half_singularity_rescaled_isEquivalent :
    (fun n : ℕ =>
      (4 : ℂ)^n *
        Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n)
      ~[atTop]
    (fun n : ℕ =>
      (4 : ℂ)^n / (Real.sqrt (Real.pi * (n : ℝ)) : ℂ)) := by
  have hscale :=
    choose_standard_scale_complex (α := (1 / 2 : ℂ)) half_not_neg_nat
  have hmul :
      (fun n : ℕ =>
        (4 : ℂ)^n * Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n)
        ~[atTop]
      (fun n : ℕ =>
        (4 : ℂ)^n *
          (((n : ℂ)^((1 / 2 : ℂ) - 1)) / Complex.Gamma (1 / 2 : ℂ))) := by
    simpa only [Pi.mul_apply] using
      (Asymptotics.IsEquivalent.refl
        (l := atTop) (u := fun n : ℕ => (4 : ℂ)^n)).mul hscale
  have hmulpi :
      (fun n : ℕ =>
        (4 : ℂ)^n * Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n)
        ~[atTop]
      (fun n : ℕ =>
        (4 : ℂ)^n *
          (((n : ℂ)^((1 / 2 : ℂ) - 1)) /
            ((Real.pi : ℂ) ^ (1 / 2 : ℂ)))) := by
    convert hmul using 1
    ext n
    rw [Complex.Gamma_one_half_eq]
  exact hmulpi.trans_eventuallyEq half_scale_to_sqrt_pi_n

theorem centralBinom_isEquivalent_complex_sqrt :
    (fun n : ℕ => (n.centralBinom : ℂ)) ~[atTop]
      (fun n : ℕ =>
        (4 : ℂ)^n / (Real.sqrt (Real.pi * (n : ℝ)) : ℂ)) := by
  have hbridge :
      (fun n : ℕ => (n.centralBinom : ℂ)) =ᶠ[atTop]
        (fun n : ℕ =>
          (4 : ℂ)^n *
            Ring.choose ((1 / 2 : ℂ) + (n : ℕ) - 1) n) := by
    exact Eventually.of_forall fun n =>
      centralBinom_eq_four_pow_mul_half_choose n
  exact hbridge.trans_isEquivalent half_singularity_rescaled_isEquivalent
