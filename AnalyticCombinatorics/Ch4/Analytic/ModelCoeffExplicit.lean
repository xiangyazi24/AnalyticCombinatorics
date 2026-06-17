import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics
import AnalyticCombinatorics.Ch4.Analytic.LogSingularity
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Explicit first-order model coefficient estimate

This file packages the exact Gamma-ratio route for the standard model
coefficient

`[z^n] (1 - z)^(-α) = Ring.choose (α + n - 1) n`.

The algebraic coefficient/Gamma identity is proved here.  The first-order
Gamma-ratio estimate is proved below from Bohr-Mollerup log-convexity.
-/

open Filter Asymptotics
open scoped BigOperators

noncomputable section

private lemma not_neg_nat_of_pos {α : ℝ} (hα : 0 < α) :
    ∀ m : ℕ, α ≠ -m := by
  intro m hm
  have hmnonneg : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  linarith

lemma choose_ofReal_model (α : ℝ) (n : ℕ) :
    Ring.choose (((α : ℂ) + n - 1)) n =
      ((Ring.choose (α + n - 1) n : ℝ) : ℂ) := by
  rw [Ring.choose]
  rw [Ring.choose]
  change Ring.multichoose ((α : ℂ) + n - 1 - n + 1) n =
    (algebraMap ℝ ℂ) (Ring.multichoose ((α + n - 1 : ℝ) - n + 1) n)
  rw [Ring.map_multichoose (algebraMap ℝ ℂ) ((α + n - 1 : ℝ) - n + 1) n]
  congr 1
  norm_num [Complex.ofReal_add, Complex.ofReal_sub]

/-- Compatibility with the repository's complex model coefficient. -/
lemma binCoeffℂ_ofReal_model (α : ℝ) (n : ℕ) :
    binCoeffℂ (α : ℂ) n = ((Ring.choose (α + n - 1) n : ℝ) : ℂ) := by
  simpa [binCoeffℂ] using choose_ofReal_model α n

private lemma ascPochhammer_eval_eq_prod_range_real (n : ℕ) (r : ℝ) :
    Polynomial.eval r (ascPochhammer ℝ n) = ∏ j ∈ Finset.range n, (r + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_natCast, ih, Finset.prod_range_succ]

/-- Real product form of the generalized binomial coefficient. -/
lemma choose_eq_prod_range_real (α : ℝ) (n : ℕ) :
    Ring.choose (α + n - 1) n =
      (∏ j ∈ Finset.range n, (α + j)) / (n.factorial : ℝ) := by
  have hmul := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (R := ℝ) α n
  have hfac : (n.factorial : ℝ) * Ring.choose (α + n - 1) n =
      ∏ j ∈ Finset.range n, (α + j) := by
    rw [← Ring.multichoose_eq α n]
    simpa [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval,
      ascPochhammer_eval_eq_prod_range_real] using hmul
  have hne : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hne]
  simpa [mul_comm] using hfac

/-- Iterating `Γ(x+1)=xΓ(x)` along a positive real arithmetic progression. -/
lemma Real.Gamma_add_nat_prod {α : ℝ} (hα : 0 < α) (n : ℕ) :
    Real.Gamma (α + n) = (∏ j ∈ Finset.range n, (α + j)) * Real.Gamma α := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 0 < α + n := by positivity
      have hne : α + n ≠ 0 := ne_of_gt hpos
      calc
        Real.Gamma (α + (n + 1 : ℕ))
            = Real.Gamma ((α + n) + 1) := by
                norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
        _ = (α + n) * Real.Gamma (α + n) := Real.Gamma_add_one hne
        _ = (α + n) * ((∏ j ∈ Finset.range n, (α + j)) * Real.Gamma α) := by
              rw [ih]
        _ = (∏ j ∈ Finset.range (n + 1), (α + j)) * Real.Gamma α := by
              rw [Finset.prod_range_succ]
              ring

/-- Exact Gamma-ratio identity for the real model coefficient. -/
theorem modelCoeff_eq_gamma_ratio {α : ℝ} (hα : 0 < α) (n : ℕ) :
    Ring.choose (α + n - 1) n =
      Real.Gamma (n + α) / (Real.Gamma α * Real.Gamma (n + 1)) := by
  have hchoose := choose_eq_prod_range_real α n
  have hgamma := Real.Gamma_add_nat_prod (α := α) hα n
  have hgamman : Real.Gamma (n + 1 : ℝ) = (n.factorial : ℝ) := by
    simpa using Real.Gamma_nat_eq_factorial n
  have hΓ : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  calc
    Ring.choose (α + n - 1) n
        = (∏ j ∈ Finset.range n, (α + j)) / (n.factorial : ℝ) := hchoose
    _ = ((∏ j ∈ Finset.range n, (α + j)) * Real.Gamma α) /
          (Real.Gamma α * (n.factorial : ℝ)) := by
            field_simp [hΓ, hfac]
    _ = Real.Gamma (n + α) / (Real.Gamma α * Real.Gamma (n + 1)) := by
            rw [← hgamma, hgamman]
            ring_nf

private lemma logGamma_add_one {y : ℝ} (hy : 0 < y) :
    (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
  dsimp [Function.comp_def]
  rw [Real.Gamma_add_one hy.ne']
  rw [Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
  ring

private lemma logGamma_unit_upper
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : n ≠ 0) :
    Real.log (Real.Gamma ((n : ℝ) + β))
      ≤ Real.log (Real.Gamma (n : ℝ)) + β * Real.log (n : ℝ) := by
  simpa [Function.comp_def] using
    Real.BohrMollerup.f_add_nat_le
      (f := Real.log ∘ Real.Gamma)
      Real.convexOn_log_Gamma
      (fun {y} hy => logGamma_add_one hy)
      hn hβ0 hβ1

private lemma logGamma_unit_lower
    {β : ℝ} (hβ0 : 0 < β)
    {n : ℕ} (hn : 2 ≤ n) :
    Real.log (Real.Gamma (n : ℝ)) + β * Real.log ((n : ℝ) - 1)
      ≤ Real.log (Real.Gamma ((n : ℝ) + β)) := by
  simpa [Function.comp_def] using
    Real.BohrMollerup.f_add_nat_ge
      (f := Real.log ∘ Real.Gamma)
      Real.convexOn_log_Gamma
      (fun {y} hy => logGamma_add_one hy)
      hn hβ0

private lemma gamma_unit_upper
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : n ≠ 0) :
    Real.Gamma ((n : ℝ) + β)
      ≤ Real.Gamma (n : ℝ) * (n : ℝ) ^ β := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hΓn_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnpos
  have hΓnb_pos : 0 < Real.Gamma ((n : ℝ) + β) := Real.Gamma_pos_of_pos (by positivity)
  have hrpow_pos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hnpos β
  rw [← Real.log_le_log_iff hΓnb_pos (mul_pos hΓn_pos hrpow_pos)]
  calc
    Real.log (Real.Gamma ((n : ℝ) + β))
        ≤ Real.log (Real.Gamma (n : ℝ)) + β * Real.log (n : ℝ) :=
          logGamma_unit_upper hβ0 hβ1 hn
    _ = Real.log (Real.Gamma (n : ℝ) * (n : ℝ) ^ β) := by
          rw [Real.log_mul hΓn_pos.ne' hrpow_pos.ne', Real.log_rpow hnpos]

private lemma gamma_unit_lower
    {β : ℝ} (hβ0 : 0 < β)
    {n : ℕ} (hn : 2 ≤ n) :
    Real.Gamma (n : ℝ) * ((n : ℝ) - 1) ^ β
      ≤ Real.Gamma ((n : ℝ) + β) := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1_nat : (1 : ℕ) < n := Nat.lt_of_succ_le hn
  have hn1r : (1 : ℝ) < n := by exact_mod_cast hn1_nat
  have hnm1pos : 0 < (n : ℝ) - 1 := by linarith
  have hΓn_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnpos
  have hΓnb_pos : 0 < Real.Gamma ((n : ℝ) + β) := Real.Gamma_pos_of_pos (by positivity)
  have hrpow_pos : 0 < ((n : ℝ) - 1) ^ β := Real.rpow_pos_of_pos hnm1pos β
  rw [← Real.log_le_log_iff (mul_pos hΓn_pos hrpow_pos) hΓnb_pos]
  calc
    Real.log (Real.Gamma (n : ℝ) * ((n : ℝ) - 1) ^ β)
        = Real.log (Real.Gamma (n : ℝ)) + β * Real.log ((n : ℝ) - 1) := by
          rw [Real.log_mul hΓn_pos.ne' hrpow_pos.ne', Real.log_rpow hnm1pos]
    _ ≤ Real.log (Real.Gamma ((n : ℝ) + β)) := logGamma_unit_lower hβ0 hn

private lemma gamma_unit_norm_eq {β : ℝ} {n : ℕ} (hn : 0 < (n : ℝ)) :
    Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1) / ((n : ℝ) ^ (β - 1)) =
      Real.Gamma ((n : ℝ) + β) / (Real.Gamma (n : ℝ) * (n : ℝ) ^ β) := by
  have hΓn_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hn
  have hpow_pos : 0 < (n : ℝ) ^ (β - 1) := Real.rpow_pos_of_pos hn (β - 1)
  have hpowβ_pos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hn β
  have hΓn1 : Real.Gamma ((n : ℝ) + 1) = (n : ℝ) * Real.Gamma (n : ℝ) :=
    Real.Gamma_add_one hn.ne'
  have hpow : (n : ℝ) * (n : ℝ) ^ (β - 1) = (n : ℝ) ^ β := by
    calc
      (n : ℝ) * (n : ℝ) ^ (β - 1) =
          (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (β - 1) := by
            rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + (β - 1)) := by rw [Real.rpow_add hn]
      _ = (n : ℝ) ^ β := by ring_nf
  rw [hΓn1]
  field_simp [hΓn_pos.ne', hn.ne', hpow_pos.ne', hpowβ_pos.ne']
  calc
    Real.Gamma ((n : ℝ) + β) * (n : ℝ) ^ β =
        Real.Gamma ((n : ℝ) + β) * ((n : ℝ) * (n : ℝ) ^ (β - 1)) := by
          rw [hpow]
    _ = (n : ℝ) * Real.Gamma ((n : ℝ) + β) * (n : ℝ) ^ (β - 1) := by ring

private lemma lower_mul_eq {β : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    (1 - (1 : ℝ) / (n : ℝ)) ^ β *
        (Real.Gamma (n : ℝ) * (n : ℝ) ^ β) =
      Real.Gamma (n : ℝ) * ((n : ℝ) - 1) ^ β := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1_nat : (1 : ℕ) < n := Nat.lt_of_succ_le hn
  have hn1r : (1 : ℝ) < n := by exact_mod_cast hn1_nat
  have hnm1_nonneg : 0 ≤ (n : ℝ) - 1 := by linarith
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hnpos
  have hdiv : ((n : ℝ) - 1) / (n : ℝ) = 1 - (1 : ℝ) / (n : ℝ) := by
    field_simp [hnpos.ne']
  have hdivpow : (1 - (1 : ℝ) / (n : ℝ)) ^ β =
      ((n : ℝ) - 1) ^ β / (n : ℝ) ^ β := by
    rw [← hdiv]
    rw [Real.div_rpow hnm1_nonneg hn_nonneg]
  rw [hdivpow]
  have hpowβ_pos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hnpos β
  field_simp [hpowβ_pos.ne']

private lemma gamma_unit_norm_between
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) :
    (1 - (1 : ℝ) / (n : ℝ)) ^ β
      ≤ Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
          / ((n : ℝ) ^ (β - 1))
      ∧ Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
          / ((n : ℝ) ^ (β - 1)) ≤ 1 := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hΓn_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnpos
  have hpowβ_pos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hnpos β
  have hden_pos : 0 < Real.Gamma (n : ℝ) * (n : ℝ) ^ β := mul_pos hΓn_pos hpowβ_pos
  have hR_eq := gamma_unit_norm_eq (β := β) (n := n) hnpos
  constructor
  · rw [hR_eq, le_div_iff₀ hden_pos]
    calc
      (1 - (1 : ℝ) / (n : ℝ)) ^ β * (Real.Gamma (n : ℝ) * (n : ℝ) ^ β)
          = Real.Gamma (n : ℝ) * ((n : ℝ) - 1) ^ β := lower_mul_eq (β := β) hn
      _ ≤ Real.Gamma ((n : ℝ) + β) := gamma_unit_lower hβ0 hn
  · rw [hR_eq, div_le_one hden_pos]
    exact gamma_unit_upper hβ0 hβ1 (Nat.ne_of_gt hnpos_nat)

private lemma one_sub_inv_le_rpow
    {β : ℝ} (hβ1 : β ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) :
    1 - (1 : ℝ) / (n : ℝ)
      ≤ (1 - (1 : ℝ) / (n : ℝ)) ^ β := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1_nat : (1 : ℕ) < n := Nat.lt_of_succ_le hn
  have hn1r : (1 : ℝ) < n := by exact_mod_cast hn1_nat
  have hdivlt : (1 : ℝ) / (n : ℝ) < 1 := (div_lt_one hnpos).mpr hn1r
  have hdiv_nonneg : 0 ≤ (1 : ℝ) / (n : ℝ) := by positivity
  have hx0 : 0 < 1 - (1 : ℝ) / (n : ℝ) := by linarith
  have hx1 : 1 - (1 : ℝ) / (n : ℝ) ≤ 1 := by linarith
  calc
    1 - (1 : ℝ) / (n : ℝ) =
        (1 - (1 : ℝ) / (n : ℝ)) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
    _ ≤ (1 - (1 : ℝ) / (n : ℝ)) ^ β :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hβ1

private theorem gamma_ratio_unit_rel_error_isBigO
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
        / ((n : ℝ) ^ (β - 1)) - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
  have hbetween := gamma_unit_norm_between hβ0 hβ1 hn
  have hlow : 1 - (1 : ℝ) / (n : ℝ)
      ≤ Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
          / ((n : ℝ) ^ (β - 1)) :=
    (one_sub_inv_le_rpow hβ1 hn).trans hbetween.1
  have hupper := hbetween.2
  let R : ℝ :=
    Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
      / ((n : ℝ) ^ (β - 1))
  have hnonpos : R - 1 ≤ 0 := by simpa [R] using sub_nonpos.mpr hupper
  have hdist : ‖R - 1‖ = 1 - R := by
    rw [Real.norm_of_nonpos hnonpos]
    ring
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hpow_inv : (n : ℝ) ^ (-(1 : ℝ)) = ((n : ℝ)⁻¹) := by
    rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  have hle_inv : 1 - R ≤ (n : ℝ)⁻¹ := by
    have hlowR : 1 - (1 : ℝ) / (n : ℝ) ≤ R := by simpa [R] using hlow
    have hlowR' : 1 - (n : ℝ)⁻¹ ≤ R := by simpa [one_div] using hlowR
    linarith
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ (-(1 : ℝ)) := by positivity
  calc
    ‖R - 1‖ = 1 - R := hdist
    _ ≤ (n : ℝ) ^ (-(1 : ℝ)) := by simpa [hpow_inv] using hle_inv
    _ = 1 * ‖(n : ℝ) ^ (-(1 : ℝ))‖ := by
          rw [Real.norm_of_nonneg hpow_nonneg]
          ring

private def gammaShiftNorm (β : ℝ) (m n : ℕ) : ℝ :=
  Real.Gamma ((n : ℝ) + β + m) / Real.Gamma ((n : ℝ) + 1) /
    ((n : ℝ) ^ (β + (m : ℝ) - 1))

private lemma gammaShiftNorm_succ_eq {β : ℝ} (hβ0 : 0 < β)
    {m n : ℕ} (hn : 0 < n) :
    gammaShiftNorm β (m + 1) n =
      gammaShiftNorm β m n * (1 + (β + (m : ℝ)) / (n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hΓden_pos : 0 < Real.Gamma ((n : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hpow_m_pos : 0 < (n : ℝ) ^ (β + (m : ℝ) - 1) :=
    Real.rpow_pos_of_pos hnpos _
  have hs_pos : 0 < (n : ℝ) + β + (m : ℝ) := by positivity
  have hΓsucc : Real.Gamma ((n : ℝ) + β + (m + 1 : ℕ)) =
      ((n : ℝ) + β + (m : ℝ)) * Real.Gamma ((n : ℝ) + β + m) := by
    calc
      Real.Gamma ((n : ℝ) + β + (m + 1 : ℕ))
          = Real.Gamma (((n : ℝ) + β + (m : ℝ)) + 1) := by
              norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      _ = ((n : ℝ) + β + (m : ℝ)) * Real.Gamma ((n : ℝ) + β + m) :=
          Real.Gamma_add_one hs_pos.ne'
  have hpow_succ : (n : ℝ) ^ (β + ((m + 1 : ℕ) : ℝ) - 1) =
      (n : ℝ) ^ (β + (m : ℝ) - 1) * (n : ℝ) := by
    calc
      (n : ℝ) ^ (β + ((m + 1 : ℕ) : ℝ) - 1)
          = (n : ℝ) ^ ((β + (m : ℝ) - 1) + 1) := by
              congr 1
              norm_num [Nat.cast_add]
              ring
      _ = (n : ℝ) ^ (β + (m : ℝ) - 1) * (n : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (β + (m : ℝ) - 1) * (n : ℝ) := by rw [Real.rpow_one]
  unfold gammaShiftNorm
  rw [hΓsucc, hpow_succ]
  field_simp [hΓden_pos.ne', hpow_m_pos.ne', hnpos.ne']
  ring

private lemma const_div_natCast_isBigO_rpow_neg_one (c : ℝ) :
    (fun n : ℕ => c / (n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  refine IsBigO.of_bound ‖c‖ ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hpow_inv : (n : ℝ) ^ (-(1 : ℝ)) = ((n : ℝ)⁻¹) := by
    rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  calc
    ‖c / (n : ℝ)‖ = ‖c‖ * ‖(n : ℝ) ^ (-(1 : ℝ))‖ := by
      rw [div_eq_mul_inv, norm_mul, hpow_inv]
    _ ≤ ‖c‖ * ‖(n : ℝ) ^ (-(1 : ℝ))‖ := le_rfl

private lemma inv_natCast_rpow_neg_one_isBigO_one :
    (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) =O[atTop]
      (fun _n : ℕ => (1 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow_inv : (n : ℝ) ^ (-(1 : ℝ)) = ((n : ℝ)⁻¹) := by
    rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  have hinv_le : ((n : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hn1
  have hinv_nonneg : 0 ≤ ((n : ℝ)⁻¹) := by positivity
  rw [hpow_inv, Real.norm_of_nonneg hinv_nonneg, Real.norm_of_nonneg zero_le_one]
  simpa using hinv_le

private lemma one_add_const_div_isBigO_one (c : ℝ) :
    (fun n : ℕ => 1 + c / (n : ℝ)) =O[atTop]
      (fun _n : ℕ => (1 : ℝ)) := by
  have hconst : (fun _n : ℕ => (1 : ℝ)) =O[atTop] (fun _n : ℕ => (1 : ℝ)) :=
    isBigO_refl _ _
  have hcdiv := (const_div_natCast_isBigO_rpow_neg_one c).trans
    inv_natCast_rpow_neg_one_isBigO_one
  exact hconst.add hcdiv

private theorem gamma_ratio_shift_rel_error_isBigO
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (m : ℕ) :
    (fun n : ℕ => gammaShiftNorm β m n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  induction m with
  | zero =>
      simpa [gammaShiftNorm] using gamma_ratio_unit_rel_error_isBigO hβ0 hβ1
  | succ m ih =>
      let c : ℝ := β + (m : ℝ)
      have hfactor : (fun n : ℕ => 1 + c / (n : ℝ)) =O[atTop]
          (fun _n : ℕ => (1 : ℝ)) := one_add_const_div_isBigO_one c
      have hcdiv : (fun n : ℕ => c / (n : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) :=
        const_div_natCast_isBigO_rpow_neg_one c
      have hprod0 := ih.mul hfactor
      have hprod : (fun n : ℕ => (gammaShiftNorm β m n - 1) * (1 + c / (n : ℝ)))
          =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
        exact hprod0.congr_right (fun n => by ring)
      have hsum := hprod.add hcdiv
      have heq : (fun n : ℕ => gammaShiftNorm β (m + 1) n - 1) =ᶠ[atTop]
          (fun n : ℕ => (gammaShiftNorm β m n - 1) *
              (1 + c / (n : ℝ)) + c / (n : ℝ)) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
        rw [gammaShiftNorm_succ_eq hβ0 hnpos]
        dsimp [c]
        ring
      exact heq.trans_isBigO hsum

private theorem gamma_ratio_shift_firstOrder
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (m : ℕ) :
    (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + β + m) / Real.Gamma ((n : ℝ) + 1)
        - (n : ℝ) ^ (β + (m : ℝ) - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (β + (m : ℝ) - 2)) := by
  have hrel := gamma_ratio_shift_rel_error_isBigO hβ0 hβ1 m
  have hp : (fun n : ℕ => (n : ℝ) ^ (β + (m : ℝ) - 1)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (β + (m : ℝ) - 1)) := isBigO_refl _ _
  have hmul : (fun n : ℕ =>
        (n : ℝ) ^ (β + (m : ℝ) - 1) * (gammaShiftNorm β m n - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (β + (m : ℝ) - 2)) := by
    exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := β + (m : ℝ) - 1) (b := -(1 : ℝ)) (c := β + (m : ℝ) - 2)
      hp hrel (by linarith)
  have heq : (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + β + m) / Real.Gamma ((n : ℝ) + 1)
        - (n : ℝ) ^ (β + (m : ℝ) - 1)) =ᶠ[atTop]
      (fun n : ℕ =>
        (n : ℝ) ^ (β + (m : ℝ) - 1) * (gammaShiftNorm β m n - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hp_pos : 0 < (n : ℝ) ^ (β + (m : ℝ) - 1) := Real.rpow_pos_of_pos hnpos _
    unfold gammaShiftNorm
    field_simp [hp_pos.ne']
  exact heq.trans_isBigO hmul

private theorem gamma_ratio_first_order_of_decomp
    {α β : ℝ} (m : ℕ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hα : α = β + (m : ℝ)) :
    (fun n : ℕ => Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
        (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  subst α
  simpa [add_assoc, add_comm, add_left_comm] using
    gamma_ratio_shift_firstOrder hβ0 hβ1 m

private theorem gamma_ratio_decomp {α : ℝ} (hα : 0 < α) :
    ∃ (β : ℝ) (m : ℕ), 0 < β ∧ β ≤ 1 ∧ α = β + (m : ℝ) := by
  let m : ℕ := Nat.ceil α - 1
  let β : ℝ := α - (m : ℝ)
  have hceil_pos : 0 < Nat.ceil α := Nat.ceil_pos.mpr hα
  have hm_lt_ceil : m < Nat.ceil α := by
    dsimp [m]
    exact Nat.sub_one_lt (Nat.ne_of_gt hceil_pos)
  have hm_lt_alpha : (m : ℝ) < α := (Nat.lt_ceil).mp hm_lt_ceil
  have hβ0 : 0 < β := by
    dsimp [β]
    linarith
  have hceil_le_alpha : α ≤ (Nat.ceil α : ℝ) := (Nat.ceil_le).mp (le_refl (Nat.ceil α))
  have hm_succ : m + 1 = Nat.ceil α := by
    dsimp [m]
    exact Nat.succ_pred_eq_of_pos hceil_pos
  have hm1_cast : (m : ℝ) + 1 = (Nat.ceil α : ℝ) := by
    rw [← hm_succ]
    norm_num
  have hβ1 : β ≤ 1 := by
    dsimp [β]
    linarith
  refine ⟨β, m, hβ0, hβ1, ?_⟩
  dsimp [β]
  ring

theorem gamma_ratio_first_order {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => Real.Gamma (n + α) / Real.Gamma (n + 1) - (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  rcases gamma_ratio_decomp hα with ⟨β, m, hβ0, hβ1, hαeq⟩
  exact gamma_ratio_first_order_of_decomp m hβ0 hβ1 hαeq

/--
Existing leading-order scale, restated under the positive-`α` hypothesis used
for model coefficients.
-/
theorem modelCoeff_leading {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => Ring.choose (α + n - 1) n) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ (α - 1) / Real.Gamma α) :=
  choose_standard_scale_real (α := α) (not_neg_nat_of_pos hα)

/--
Explicit first-order model coefficient estimate:

`[z^n] (1-z)^(-α) - n^(α-1)/Γ(α) = O(n^(α-2))`.
-/
theorem modelCoeff_explicit {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => Ring.choose (α + n - 1) n - (n : ℝ) ^ (α - 1) / Real.Gamma α)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  have hΓ : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have h :=
    (gamma_ratio_first_order (α := α) hα).const_mul_left (Real.Gamma α)⁻¹
  exact h.congr_left fun n => by
    have hΓn : Real.Gamma (n + 1 : ℝ) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < n + 1)).ne'
    rw [modelCoeff_eq_gamma_ratio (α := α) hα n]
    field_simp [hΓ, hΓn]

end
