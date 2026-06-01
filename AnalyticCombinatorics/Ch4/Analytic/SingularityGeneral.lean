import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# General-exponent singularity scale

This is the Flajolet--Sedgewick Theorem VI.1 standard scale for general `α`:
`[z^n] (1 - z)^{-α} ~ n^{α-1} / Γ(α)`. The integer case
`Γ(k) = (k - 1)!` is in `SingularityInteger.lean`; the full transfer theorem
with Δ-domains and Hankel contours remains out of scope here.

The hypothesis `∀ m : ℕ, α ≠ -m` says `α ∉ {0, -1, -2, ...}`. It holds for
all non-integer real `α` and is the correct non-vacuous hypothesis.
-/

open scoped BigOperators
open Finset Polynomial Filter Asymptotics

lemma ascPochhammer_eval_eq_prod_range_complex (n : ℕ) (r : ℂ) :
    Polynomial.eval r (ascPochhammer ℂ n) = ∏ j ∈ Finset.range n, (r + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_natCast, ih, Finset.prod_range_succ]

lemma choose_eq_prod_range_complex (α : ℂ) (n : ℕ) :
    Ring.choose (α + n - 1) n = (∏ j ∈ Finset.range n, (α + j)) / (n.factorial : ℂ) := by
  have hmul := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (R := ℂ) α n
  have hfac : (n.factorial : ℂ) * Ring.choose (α + n - 1) n =
      ∏ j ∈ Finset.range n, (α + j) := by
    rw [← Ring.multichoose_eq α n]
    simpa [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval,
      ascPochhammer_eval_eq_prod_range_complex] using hmul
  have hne : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hne]
  simpa [mul_comm] using hfac

lemma GammaSeq_ne_zero_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m)
    {n : ℕ} (hn : n ≠ 0) : Complex.GammaSeq α n ≠ 0 := by
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnpow : (n : ℂ)^α ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hαn : α + n ≠ 0 := by
    intro h
    exact hα n (eq_neg_of_add_eq_zero_left h)
  have hprod : (∏ j ∈ Finset.range n, (α + j)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj hzero
    exact hα j (eq_neg_of_add_eq_zero_left hzero)
  have hGs : Complex.GammaSeq α n =
      (n : ℂ)^α * (n.factorial : ℂ) /
        ((∏ j ∈ Finset.range n, (α + j)) * (α + n)) := by
    simp [Complex.GammaSeq, Finset.prod_range_succ]
  rw [hGs]
  exact div_ne_zero (mul_ne_zero hnpow hfact) (mul_ne_zero hprod hαn)

lemma choose_eq_cpow_div_gammaSeq_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m)
    {n : ℕ} (hn : n ≠ 0) :
    Ring.choose (α + n - 1) n =
      (n : ℂ)^α / ((α + n) * Complex.GammaSeq α n) := by
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnpow : (n : ℂ)^α ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hαn : α + n ≠ 0 := by
    intro h
    exact hα n (eq_neg_of_add_eq_zero_left h)
  have hprod : (∏ j ∈ Finset.range n, (α + j)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj hzero
    exact hα j (eq_neg_of_add_eq_zero_left hzero)
  have hGs : Complex.GammaSeq α n =
      (n : ℂ)^α * (n.factorial : ℂ) /
        ((∏ j ∈ Finset.range n, (α + j)) * (α + n)) := by
    simp [Complex.GammaSeq, Finset.prod_range_succ]
  rw [choose_eq_prod_range_complex, hGs]
  field_simp [hfact, hprod, hαn, hnpow]

lemma choose_ratio_eq_gammaSeq_ratio_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m)
    {n : ℕ} (hn : n ≠ 0) :
    Ring.choose (α + n - 1) n / ((n : ℂ)^(α - 1) / Complex.Gamma α) =
      (Complex.Gamma α / Complex.GammaSeq α n) * ((n : ℂ) / (n + α)) := by
  have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnpowα : (n : ℂ)^α ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hnpowα1 : (n : ℂ)^(α - 1) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hncast
  have hαn : α + n ≠ 0 := by
    intro h
    exact hα n (eq_neg_of_add_eq_zero_left h)
  have hnα : (n : ℂ) + α ≠ 0 := by
    simpa [add_comm] using hαn
  have hΓ : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero hα
  have hGseq : Complex.GammaSeq α n ≠ 0 := GammaSeq_ne_zero_complex hα hn
  rw [choose_eq_cpow_div_gammaSeq_complex hα hn]
  rw [Complex.cpow_sub _ _ hncast, Complex.cpow_one]
  field_simp [hncast, hnpowα, hnpowα1, hαn, hnα, hΓ, hGseq]
  ring

lemma choose_ratio_tendsto_one_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m) :
    Tendsto (fun n : ℕ =>
      Ring.choose (α + n - 1) n / ((n : ℂ)^(α - 1) / Complex.Gamma α))
      atTop (nhds 1) := by
  have hΓ : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero hα
  have h_event : (fun n : ℕ =>
      Ring.choose (α + n - 1) n / ((n : ℂ)^(α - 1) / Complex.Gamma α))
      =ᶠ[atTop]
      (fun n : ℕ => (Complex.Gamma α / Complex.GammaSeq α n) * ((n : ℂ) / (n + α))) := by
    exact (eventually_ne_atTop 0).mono fun n hn => choose_ratio_eq_gammaSeq_ratio_complex hα hn
  apply Filter.Tendsto.congr' h_event.symm
  have h₁ : Tendsto (fun n : ℕ => Complex.Gamma α / Complex.GammaSeq α n) atTop (nhds 1) := by
    simpa [div_self hΓ] using
      (tendsto_const_nhds (x := Complex.Gamma α)).div (Complex.GammaSeq_tendsto_Gamma α) hΓ
  have h₂ : Tendsto (fun n : ℕ => (n : ℂ) / (n + α)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop α
  simpa using h₁.mul h₂

theorem choose_standard_scale_complex {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m) :
    (fun n : ℕ => Ring.choose (α + n - 1) n) ~[atTop]
      (fun n : ℕ => (n : ℂ)^(α - 1) / Complex.Gamma α) := by
  have hΓ : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero hα
  have htarget : ∀ᶠ n : ℕ in atTop, (n : ℂ)^(α - 1) / Complex.Gamma α ≠ 0 := by
    refine (eventually_ne_atTop 0).mono ?_
    intro n hn
    have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hpow : (n : ℂ)^(α - 1) ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]
      exact Or.inl hncast
    exact div_ne_zero hpow hΓ
  rw [isEquivalent_iff_tendsto_one htarget]
  exact choose_ratio_tendsto_one_complex hα

theorem coeff_oneDivOneSubCpow_isEquivalent {α : ℂ} (hα : ∀ m : ℕ, α ≠ -m) :
    (fun n : ℕ =>
      ((FormalMultilinearSeries.ofScalars ℂ
        (fun n : ℕ => Ring.choose (α + n - 1) n)).coeff n)) ~[atTop]
      (fun n : ℕ => (n : ℂ)^(α - 1) / Complex.Gamma α) := by
  simpa using choose_standard_scale_complex hα
