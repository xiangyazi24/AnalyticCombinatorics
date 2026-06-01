import AnalyticCombinatorics.Ch4.Analytic.Rational
import Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Integer-exponent singularity scale

This file proves the first integer-exponent standard scale for singularity
analysis:
`[z^n] (1 - z)^{-k} ~ n^{k-1} / (k-1)!` for natural `k ≥ 1`.

The general non-integer transfer for `(1 - z)^{-α}` is OUT OF SCOPE here; it
needs Gamma/binomial infrastructure and analytic domain hypotheses such as
Δ-domains.
-/

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

lemma shifted_choose_isEquivalent (d : ℕ) :
    (fun n : ℕ => ((n + d).choose d : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ)^d / d.factorial) := by
  have h0 := (isEquivalent_choose d).comp_tendsto (Filter.tendsto_add_atTop_nat d)
  have haff :
      (fun n : ℕ => (((n + d : ℕ) : ℝ))) ~[atTop] (fun n : ℕ => (n : ℝ)) := by
    simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
      (IsEquivalent.add_const_of_norm_tendsto_atTop
        (IsEquivalent.refl (l := atTop) (u := fun n : ℕ => (n : ℝ))) (by
          simpa using
            tendsto_norm_atTop_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))))
  have h1 :
      (fun n : ℕ => (((n + d : ℕ) : ℝ))^d / d.factorial) ~[atTop]
        (fun n : ℕ => (n : ℝ)^d / d.factorial) := by
    simpa using
      (haff.pow d).div
        (IsEquivalent.refl (l := atTop) (u := fun _ : ℕ => (d.factorial : ℝ)))
  exact h0.trans h1

lemma ofReal_isEquivalent {f g : ℕ → ℝ} (hfg : f ~[atTop] g)
    (hg : ∀ᶠ n in atTop, g n ≠ 0) :
    (fun n => (f n : ℂ)) ~[atTop] (fun n => (g n : ℂ)) := by
  rw [isEquivalent_iff_tendsto_one hg] at hfg
  rw [isEquivalent_iff_tendsto_one]
  · have hc : Tendsto (fun n => ((f n / g n : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
      simpa using hfg.ofReal
    convert hc using 1
    ext n
    simp
  · filter_upwards [hg] with n hn
    exact_mod_cast hn

lemma coeff_invOneSubPow_isEquivalent (d : ℕ) :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n (PowerSeries.invOneSubPow ℂ (d + 1)).val)
      ~[atTop]
    (fun n : ℕ => (n : ℂ)^d / (d.factorial : ℂ)) := by
  have hnonzero : ∀ᶠ n : ℕ in atTop, (n : ℝ)^d / d.factorial ≠ 0 := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.succ_le_iff.mp hn))
    have hfact : (d.factorial : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero d)
    exact div_ne_zero (pow_ne_zero d hn0) hfact
  have hcomplex := ofReal_isEquivalent (shifted_choose_isEquivalent d) hnonzero
  simpa [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, Nat.add_comm,
    Complex.ofReal_div, Complex.ofReal_pow] using hcomplex

lemma coeff_invOneSubPow_isEquivalent_of_one_le (k : ℕ) (hk : 1 ≤ k) :
    (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n (PowerSeries.invOneSubPow ℂ k).val)
      ~[atTop]
    (fun n : ℕ => (n : ℂ)^(k - 1) / ((k - 1).factorial : ℂ)) := by
  have hk0 : k ≠ 0 := by
    have hpos : 0 < k := Nat.succ_le_iff.mp hk
    exact Nat.ne_of_gt hpos
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  simpa using coeff_invOneSubPow_isEquivalent d
