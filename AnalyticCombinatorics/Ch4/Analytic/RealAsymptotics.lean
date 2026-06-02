import AnalyticCombinatorics.Ch4.Analytic.CentralBinomial
import AnalyticCombinatorics.Ch4.Analytic.Catalan
import AnalyticCombinatorics.Ch4.Analytic.Fibonacci
import AnalyticCombinatorics.Ch4.Analytic.SingularityGeneral
import AnalyticCombinatorics.Ch4.Analytic.SingularityInteger

/-!
# Real-valued central-binomial and Catalan asymptotics

This file reflects the complex-valued asymptotic equivalents back to their
natural real-valued forms.
-/

open Filter Asymptotics
open scoped Topology BigOperators

lemma ofReal_isEquivalent_iff {f g : ℕ → ℝ} :
    ((fun n => (f n : ℂ)) ~[atTop] (fun n => (g n : ℂ))) ↔
      f ~[atTop] g := by
  constructor
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn

theorem centralBinom_isEquivalent_real_sqrt :
    (fun n : ℕ => (n.centralBinom : ℝ)) ~[atTop]
      (fun n : ℕ => (4 : ℝ)^n / Real.sqrt (Real.pi * (n : ℝ))) := by
  rw [← ofReal_isEquivalent_iff]
  simpa [Complex.ofReal_div, Complex.ofReal_pow] using
    centralBinom_isEquivalent_complex_sqrt

theorem catalan_isEquivalent_real_rpow :
    (fun n : ℕ => (catalan n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        (4 : ℝ)^n / (Real.sqrt Real.pi * (n : ℝ)^(3 / 2 : ℝ))) := by
  rw [← ofReal_isEquivalent_iff]
  simpa [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow] using
    catalan_isEquivalent_complex_rpow

theorem fib_isEquivalent_real :
    (fun n : ℕ => (Nat.fib (n + 1) : ℝ)) ~[atTop]
      (fun n : ℕ =>
        (Real.goldenRatio / (Real.goldenRatio - Real.goldenConj)) * Real.goldenRatio ^ n) := by
  rw [← ofReal_isEquivalent_iff]
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_natCast] using
    fib_isEquivalent

private lemma choose_ofReal (α : ℝ) (n : ℕ) :
    Ring.choose (((α : ℂ) + n - 1)) n =
      ((Ring.choose (α + n - 1) n : ℝ) : ℂ) := by
  rw [Ring.choose]
  rw [Ring.choose]
  change Ring.multichoose ((α : ℂ) + n - 1 - n + 1) n =
    (algebraMap ℝ ℂ) (Ring.multichoose ((α + n - 1 : ℝ) - n + 1) n)
  rw [Ring.map_multichoose (algebraMap ℝ ℂ) ((α + n - 1 : ℝ) - n + 1) n]
  congr 1
  norm_num [Complex.ofReal_add, Complex.ofReal_sub]

private lemma natCast_cpow_ofReal (α : ℝ) (n : ℕ) :
    (n : ℂ)^((α : ℂ) - 1) = (((n : ℝ)^(α - 1) : ℝ) : ℂ) := by
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  simpa only [Complex.ofReal_natCast, Complex.ofReal_sub, Complex.ofReal_one] using
    (Complex.ofReal_cpow hn (α - 1)).symm

theorem choose_standard_scale_real {α : ℝ} (hα : ∀ m : ℕ, α ≠ -m) :
    (fun n : ℕ => Ring.choose (α + n - 1) n) ~[atTop]
      (fun n : ℕ => (n : ℝ)^(α - 1) / Real.Gamma α) := by
  rw [← ofReal_isEquivalent_iff]
  have hαc : ∀ m : ℕ, (α : ℂ) ≠ -m := by
    intro m hm
    apply hα m
    apply Complex.ofReal_injective
    simpa [Complex.ofReal_neg] using hm
  simpa only [choose_ofReal, natCast_cpow_ofReal, Complex.ofReal_div,
    Complex.Gamma_ofReal] using
    choose_standard_scale_complex (α := (α : ℂ)) hαc
