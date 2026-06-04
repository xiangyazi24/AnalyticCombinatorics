import Mathlib
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics

/-!
# Ternary trees and the Fuss-Catalan asymptotic

The number of full ternary trees with `n` internal nodes is
`1 / (2n + 1) * binom(3n,n)`.  This file proves the corresponding
Fuss-Catalan asymptotic directly from Stirling's formula.
-/

open Filter Asymptotics
open scoped Topology

/-- The number of full ternary trees with `n` internal nodes. -/
def ternaryTreeCount (n : ℕ) : ℕ :=
  Nat.choose (3 * n) n / (2 * n + 1)

noncomputable def stirlingScale (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) * Real.pi) * (((n : ℝ) / Real.exp 1) ^ n)

lemma ternary_choose_dvd (n : ℕ) :
    2 * n + 1 ∣ Nat.choose (3 * n) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hrel := Nat.choose_succ_right_eq (3 * n) (n - 1)
    have hpred : n - 1 + 1 = n := Nat.sub_one_add_one hn
    have hsub : 3 * n - (n - 1) = 2 * n + 1 := by omega
    rw [hpred, hsub] at hrel
    have hdvd : 2 * n + 1 ∣ Nat.choose (3 * n) n * n := by
      rw [hrel, mul_comm]
      exact dvd_mul_left _ _
    have hcop : Nat.Coprime (2 * n + 1) n := by
      have h : 2 * n + 1 = (n + 1) + n := by omega
      rw [h, Nat.coprime_add_self_left]
      have h2 : n + 1 = 1 + n := by omega
      rw [h2, Nat.coprime_add_self_left]
      simp
    exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hdvd)

lemma ternaryTreeCount_cast (n : ℕ) :
    (ternaryTreeCount n : ℝ) =
      ((Nat.choose (3 * n) n : ℕ) : ℝ) / (((2 * n + 1 : ℕ) : ℝ)) := by
  unfold ternaryTreeCount
  exact Nat.cast_div (ternary_choose_dvd n) (by positivity)

lemma choose_three_mul_cast (n : ℕ) :
    ((Nat.choose (3 * n) n : ℕ) : ℝ) =
      (((3 * n).factorial : ℕ) : ℝ) /
        ((((n.factorial : ℕ) : ℝ) * (((2 * n).factorial : ℕ) : ℝ))) := by
  have hle : n ≤ 3 * n := by omega
  rw [Nat.cast_choose ℝ hle]
  have hsub : 3 * n - n = 2 * n := by omega
  rw [hsub]

lemma tendsto_two_mul_atTop : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
  simpa [nsmul_eq_mul] using
    ((tendsto_id : Tendsto (fun n : ℕ => n) atTop atTop).nsmul_atTop
      (by norm_num : 0 < 2))

lemma tendsto_three_mul_atTop : Tendsto (fun n : ℕ => 3 * n) atTop atTop := by
  simpa [nsmul_eq_mul] using
    ((tendsto_id : Tendsto (fun n : ℕ => n) atTop atTop).nsmul_atTop
      (by norm_num : 0 < 3))

lemma factorial_two_mul_isEquivalent :
    (fun n : ℕ => (((2 * n).factorial : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ => stirlingScale (2 * n)) := by
  simpa [stirlingScale, Function.comp_def] using
    Stirling.factorial_isEquivalent_stirling.comp_tendsto tendsto_two_mul_atTop

lemma factorial_three_mul_isEquivalent :
    (fun n : ℕ => (((3 * n).factorial : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ => stirlingScale (3 * n)) := by
  simpa [stirlingScale, Function.comp_def] using
    Stirling.factorial_isEquivalent_stirling.comp_tendsto tendsto_three_mul_atTop

lemma factorial_ratio_isEquivalent :
    (fun n : ℕ => (((3 * n).factorial : ℕ) : ℝ) /
      ((((n.factorial : ℕ) : ℝ) * (((2 * n).factorial : ℕ) : ℝ)))) ~[atTop]
    (fun n : ℕ => stirlingScale (3 * n) / (stirlingScale n * stirlingScale (2 * n))) := by
  have hden := Stirling.factorial_isEquivalent_stirling.mul factorial_two_mul_isEquivalent
  simpa only [Pi.div_apply, Pi.mul_apply] using factorial_three_mul_isEquivalent.div hden

lemma power_ratio_core (n : ℕ) (y : ℝ) (hy : y ≠ 0) :
    ((27 * y ^ 3) ^ n) / (y ^ n * (4 * y ^ 2) ^ n) = (27 / 4 : ℝ) ^ n := by
  rw [mul_pow, mul_pow]
  field_simp [pow_ne_zero n hy]
  rw [show (27 : ℝ) ^ n = 4 ^ n * (27 / 4 : ℝ) ^ n by
    rw [← mul_pow]
    norm_num]
  ring

lemma stirling_power_ratio (n : ℕ) (hn : n ≠ 0) :
    ((((3 * n : ℕ) : ℝ) / Real.exp 1) ^ (3 * n)) /
      ((((n : ℝ) / Real.exp 1) ^ n) *
        ((((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n))) =
      (27 / 4 : ℝ) ^ n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hE : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have hy : (n : ℝ) / Real.exp 1 ≠ 0 := div_ne_zero hnR hE
  rw [show (((3 * n : ℕ) : ℝ) / Real.exp 1) =
      3 * ((n : ℝ) / Real.exp 1) by
        norm_num
        ring,
    show (((2 * n : ℕ) : ℝ) / Real.exp 1) =
      2 * ((n : ℝ) / Real.exp 1) by
        norm_num
        ring]
  rw [pow_mul (3 * ((n : ℝ) / Real.exp 1)) 3 n,
    pow_mul (2 * ((n : ℝ) / Real.exp 1)) 2 n]
  rw [show (3 * ((n : ℝ) / Real.exp 1)) ^ 3 =
      27 * ((n : ℝ) / Real.exp 1) ^ 3 by ring,
    show (2 * ((n : ℝ) / Real.exp 1)) ^ 2 =
      4 * ((n : ℝ) / Real.exp 1) ^ 2 by ring]
  exact power_ratio_core n ((n : ℝ) / Real.exp 1) hy

lemma stirling_sqrt_ratio (n : ℕ) (hn : n ≠ 0) :
    Real.sqrt (2 * ((3 * n : ℕ) : ℝ) * Real.pi) /
      (Real.sqrt (2 * (n : ℝ) * Real.pi) *
        Real.sqrt (2 * ((2 * n : ℕ) : ℝ) * Real.pi)) =
    Real.sqrt 3 / (2 * Real.sqrt (Real.pi * (n : ℝ))) := by
  have hnum : Real.sqrt (2 * ((3 * n : ℕ) : ℝ) * Real.pi) =
      Real.sqrt 3 * Real.sqrt (2 * (n : ℝ) * Real.pi) := by
    rw [show 2 * ((3 * n : ℕ) : ℝ) * Real.pi =
        3 * (2 * (n : ℝ) * Real.pi) by
          norm_num
          ring]
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (3 : ℝ))]
  have hden2 : Real.sqrt (2 * ((2 * n : ℕ) : ℝ) * Real.pi) =
      2 * Real.sqrt (Real.pi * (n : ℝ)) := by
    rw [show 2 * ((2 * n : ℕ) : ℝ) * Real.pi =
        4 * (Real.pi * (n : ℝ)) by
          norm_num
          ring]
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
    norm_num
  have hden1_ne : Real.sqrt (2 * (n : ℝ) * Real.pi) ≠ 0 := by positivity
  rw [hnum, hden2]
  field_simp [hden1_ne]

lemma stirling_choose_scale_eq (n : ℕ) (hn : n ≠ 0) :
    stirlingScale (3 * n) / (stirlingScale n * stirlingScale (2 * n)) =
      (27 / 4 : ℝ) ^ n * Real.sqrt 3 /
        (2 * Real.sqrt (Real.pi * (n : ℝ))) := by
  unfold stirlingScale
  rw [show
      (Real.sqrt (2 * ↑(3 * n) * Real.pi) * (↑(3 * n) / Real.exp 1) ^ (3 * n)) /
          ((Real.sqrt (2 * ↑n * Real.pi) * (↑n / Real.exp 1) ^ n) *
            (Real.sqrt (2 * ↑(2 * n) * Real.pi) *
              (↑(2 * n) / Real.exp 1) ^ (2 * n))) =
        (Real.sqrt (2 * ↑(3 * n) * Real.pi) /
          (Real.sqrt (2 * ↑n * Real.pi) * Real.sqrt (2 * ↑(2 * n) * Real.pi))) *
        (((↑(3 * n) / Real.exp 1) ^ (3 * n)) /
          (((↑n / Real.exp 1) ^ n) * ((↑(2 * n) / Real.exp 1) ^ (2 * n)))) by
        ring_nf]
  rw [stirling_sqrt_ratio n hn, stirling_power_ratio n hn]
  ring

theorem choose_three_mul_isEquivalent :
    (fun n : ℕ => ((Nat.choose (3 * n) n : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ => (27 / 4 : ℝ) ^ n * Real.sqrt 3 /
        (2 * Real.sqrt (Real.pi * (n : ℝ)))) := by
  have hbridge :
      (fun n : ℕ => ((Nat.choose (3 * n) n : ℕ) : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => (((3 * n).factorial : ℕ) : ℝ) /
          ((((n.factorial : ℕ) : ℝ) * (((2 * n).factorial : ℕ) : ℝ)))) :=
    Eventually.of_forall choose_three_mul_cast
  have hraw := hbridge.trans_isEquivalent factorial_ratio_isEquivalent
  exact hraw.trans_eventuallyEq ((eventually_ne_atTop 0).mono fun n hn => by
    dsimp
    rw [stirling_choose_scale_eq n hn])

lemma natCast_isEquivalent_add_half_real :
    (fun n : ℕ => (n : ℝ)) ~[atTop] (fun n : ℕ => (n : ℝ) + (1 / 2 : ℝ)) := by
  apply isEquivalent_of_tendsto_one
  simpa [add_comm] using tendsto_natCast_div_add_atTop (1 / 2 : ℝ)

lemma two_mul_add_one_isEquivalent_two_mul :
    (fun n : ℕ => (((2 * n + 1 : ℕ) : ℝ))) ~[atTop]
      (fun n : ℕ => (2 : ℝ) * (n : ℝ)) := by
  have hmul :
      (fun n : ℕ => (2 : ℝ) * (n : ℝ)) ~[atTop]
        (fun n : ℕ => (2 : ℝ) * ((n : ℝ) + (1 / 2 : ℝ))) := by
    simpa only [Pi.mul_apply] using
      (Asymptotics.IsEquivalent.refl (l := atTop) (u := fun _ : ℕ => (2 : ℝ))).mul
        natCast_isEquivalent_add_half_real
  simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, mul_add, two_mul,
    add_comm, add_left_comm, add_assoc] using hmul.symm

lemma rpow_three_halves_mul_nat_real (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  nth_rw 2 [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnpos]
  norm_num

lemma sqrt_pi_mul_nat_eq_sqrt_pi_mul_rpow_real (n : ℕ) (hn : n ≠ 0) :
    Real.sqrt (Real.pi * (n : ℝ)) * (n : ℝ) =
      Real.sqrt Real.pi * ((n : ℝ) ^ (3 / 2 : ℝ)) := by
  rw [Real.sqrt_mul Real.pi_nonneg]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [mul_assoc, rpow_three_halves_mul_nat_real n hn]

lemma ternary_scale_simplified (n : ℕ) (hn : n ≠ 0) :
    (((27 / 4 : ℝ) ^ n * Real.sqrt 3 / (2 * Real.sqrt (Real.pi * (n : ℝ)))) /
      (2 * (n : ℝ))) =
    (27 / 4 : ℝ) ^ n * Real.sqrt 3 /
      (4 * Real.sqrt Real.pi * ((n : ℝ) ^ (3 / 2 : ℝ))) := by
  rw [div_div]
  rw [show 2 * Real.sqrt (Real.pi * (n : ℝ)) * (2 * (n : ℝ)) =
      4 * (Real.sqrt (Real.pi * (n : ℝ)) * (n : ℝ)) by ring]
  rw [sqrt_pi_mul_nat_eq_sqrt_pi_mul_rpow_real n hn]
  ring

theorem ternaryTreeCount_isEquivalent_sqrt_pi_n :
    (fun n : ℕ => (ternaryTreeCount n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        ((27 / 4 : ℝ) ^ n * Real.sqrt 3 / (2 * Real.sqrt (Real.pi * (n : ℝ)))) /
          (2 * (n : ℝ))) := by
  have hbridge :
      (fun n : ℕ => (ternaryTreeCount n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ =>
          ((Nat.choose (3 * n) n : ℕ) : ℝ) / (((2 * n + 1 : ℕ) : ℝ))) :=
    Eventually.of_forall ternaryTreeCount_cast
  have hdiv :
      (fun n : ℕ =>
          ((Nat.choose (3 * n) n : ℕ) : ℝ) / (((2 * n + 1 : ℕ) : ℝ))) ~[atTop]
        (fun n : ℕ =>
          ((27 / 4 : ℝ) ^ n * Real.sqrt 3 / (2 * Real.sqrt (Real.pi * (n : ℝ)))) /
            (2 * (n : ℝ))) := by
    simpa only [Pi.div_apply] using
      choose_three_mul_isEquivalent.div two_mul_add_one_isEquivalent_two_mul
  exact hbridge.trans_isEquivalent hdiv

/--
The full ternary-tree Fuss-Catalan asymptotic.  Stirling gives the constant
`sqrt 3 / (4 sqrt pi)`.
-/
theorem ternaryTreeCount_isEquivalent :
    (fun n : ℕ => (ternaryTreeCount n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        (27 / 4 : ℝ) ^ n * Real.sqrt 3 /
          (4 * Real.sqrt Real.pi * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  exact ternaryTreeCount_isEquivalent_sqrt_pi_n.trans_eventuallyEq
    ((eventually_ne_atTop 0).mono fun n hn => by
      dsimp
      rw [ternary_scale_simplified n hn])
