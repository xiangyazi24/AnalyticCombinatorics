import AnalyticCombinatorics.Ch4.Analytic.CentralBinomial

/-!
# Catalan asymptotics

This file derives the standard asymptotic estimate for Catalan numbers from the
central binomial coefficient estimate.
-/

open Filter Asymptotics
open scoped Topology BigOperators

lemma catalan_eq_centralBinom_div_complex (n : ℕ) :
    (catalan n : ℂ) = (n.centralBinom : ℂ) / ((n : ℂ) + 1) := by
  have h : ((n : ℂ) + 1) * (catalan n : ℂ) = (n.centralBinom : ℂ) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (show (((n + 1) * catalan n : ℕ) : ℂ) = (n.centralBinom : ℂ) by
        exact_mod_cast succ_mul_catalan_eq_centralBinom n)
  have hn : (n : ℂ) + 1 ≠ 0 := by
    have hn' : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    simpa [Nat.cast_add, Nat.cast_one] using hn'
  rw [← h]
  field_simp [hn]

lemma catalan_eventuallyEq_centralBinom_div_complex :
    (fun n : ℕ => (catalan n : ℂ)) =ᶠ[atTop]
      (fun n : ℕ => (n.centralBinom : ℂ) / ((n : ℂ) + 1)) := by
  exact Eventually.of_forall catalan_eq_centralBinom_div_complex

lemma natCast_isEquivalent_succ_complex :
    (fun n : ℕ => (n : ℂ)) ~[atTop] (fun n : ℕ => (n : ℂ) + 1) := by
  apply isEquivalent_of_tendsto_one
  simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
    (tendsto_natCast_div_add_atTop (1 : ℂ))

theorem catalan_isEquivalent_complex_sqrt_mul_nat :
    (fun n : ℕ => (catalan n : ℂ)) ~[atTop]
      (fun n : ℕ =>
        (4 : ℂ)^n / ((Real.sqrt (Real.pi * (n : ℝ)) : ℂ) * (n : ℂ))) := by
  have hdiv :
      (fun n : ℕ => (n.centralBinom : ℂ) / ((n : ℂ) + 1)) ~[atTop]
        (fun n : ℕ =>
          ((4 : ℂ)^n / (Real.sqrt (Real.pi * (n : ℝ)) : ℂ)) / (n : ℂ)) := by
    simpa only [Pi.div_apply] using
      centralBinom_isEquivalent_complex_sqrt.div natCast_isEquivalent_succ_complex.symm
  have hnorm :
      (fun n : ℕ =>
          ((4 : ℂ)^n / (Real.sqrt (Real.pi * (n : ℝ)) : ℂ)) / (n : ℂ)) =ᶠ[atTop]
        (fun n : ℕ =>
          (4 : ℂ)^n / ((Real.sqrt (Real.pi * (n : ℝ)) : ℂ) * (n : ℂ))) := by
    exact (eventually_ne_atTop 0).mono fun n _hn => by
      dsimp
      rw [div_div]
  exact catalan_eventuallyEq_centralBinom_div_complex.trans_isEquivalent
    (hdiv.trans_eventuallyEq hnorm)

lemma rpow_three_halves_mul_nat (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  nth_rw 2 [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnpos]
  norm_num

lemma sqrt_pi_mul_nat_eq_sqrt_pi_mul_rpow (n : ℕ) (hn : n ≠ 0) :
    (Real.sqrt (Real.pi * (n : ℝ)) : ℂ) * (n : ℂ) =
      (((Real.sqrt Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hreal : Real.sqrt (Real.pi * (n : ℝ)) * (n : ℝ) =
      (Real.sqrt Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)) := by
    rw [Real.sqrt_mul Real.pi_nonneg (n : ℝ)]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [mul_assoc, rpow_three_halves_mul_nat n hn]
  exact_mod_cast hreal

lemma sqrt_mul_nat_eventuallyEq_rpow :
    (fun n : ℕ =>
        (4 : ℂ)^n / ((Real.sqrt (Real.pi * (n : ℝ)) : ℂ) * (n : ℂ))) =ᶠ[atTop]
      (fun n : ℕ =>
        (4 : ℂ)^n /
          (((Real.sqrt Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  exact (eventually_ne_atTop 0).mono fun n hn => by
    dsimp
    rw [sqrt_pi_mul_nat_eq_sqrt_pi_mul_rpow n hn]

theorem catalan_isEquivalent_complex_rpow :
    (fun n : ℕ => (catalan n : ℂ)) ~[atTop]
      (fun n : ℕ =>
        (4 : ℂ)^n /
          (((Real.sqrt Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  exact catalan_isEquivalent_complex_sqrt_mul_nat.trans_eventuallyEq
    sqrt_mul_nat_eventuallyEq_rpow
