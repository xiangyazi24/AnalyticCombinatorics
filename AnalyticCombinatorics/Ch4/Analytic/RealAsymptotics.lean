import AnalyticCombinatorics.Ch4.Analytic.CentralBinomial
import AnalyticCombinatorics.Ch4.Analytic.Catalan
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
