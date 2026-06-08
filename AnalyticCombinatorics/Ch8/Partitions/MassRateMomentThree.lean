import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateBoseKernel4

/-!
# The `M₃` Lambert identity

Termwise differentiation of the `M₂` identity (`sigmaMoment_two_lambert`) gives

  `Σ_m m³·σ(m)e^{−tm} = Σ_k k³·boseKernel4(tk)`,

using `boseKernel3_hasDerivAt : HasDerivAt boseKernel3 (−boseKernel4) z`.
Faithful mirror of `sigmaMoment_two_lambert`, powers shifted `+1`.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Set
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **The `M₃` Lambert identity.** -/
theorem sigmaMoment_three_lambert {t : ℝ} (ht : 0 < t) :
    sigmaMoment 3 t
      = ∑' k : ℕ, if k = 0 then 0 else (k : ℝ) ^ 3 * boseKernel4 (t * (k : ℝ)) := by
  classical
  have ht2 : 0 < t / 2 := by linarith
  set s := Set.Ioi (t / 2) with hsdef
  have hs_open : IsOpen s := isOpen_Ioi
  have hs_conn : IsPreconnected s := (convex_Ioi _).isPreconnected
  have hts : t ∈ s := by
    rw [hsdef]; exact Set.mem_Ioi.mpr (by linarith)
  set r := Real.exp (-(t / 2)) with hrdef
  have hr1 : r < 1 := by rw [hrdef, Real.exp_lt_one_iff]; linarith
  have hr0 : 0 < r := Real.exp_pos _
  -- ===== σ-side: differentiate  m²·σ·e^{−um}  →  −m³·σ·e^{−um} =====
  set fσ := (fun (m : ℕ) (u : ℝ) =>
    if m = 0 then (0:ℝ) else (m : ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-u * (m : ℝ))) with hfσdef
  set fσ' := (fun (m : ℕ) (u : ℝ) =>
    if m = 0 then (0:ℝ)
    else -((m : ℝ) ^ 3 * Sigma.sigmaR m * Real.exp (-u * (m : ℝ)))) with hfσ'def
  have hσ_deriv : ∀ m : ℕ, ∀ u ∈ s, HasDerivAt (fσ m) (fσ' m u) u := by
    intro m u _hu
    by_cases hm : m = 0
    · subst hm
      simp only [hfσdef, hfσ'def, if_pos rfl]
      exact hasDerivAt_const u 0
    · simp only [hfσdef, hfσ'def, if_neg hm]
      have hinner : HasDerivAt (fun u : ℝ => -u * (m : ℝ)) (-(m : ℝ)) u := by
        simpa using ((hasDerivAt_id u).neg.mul_const ((m : ℝ)))
      have hexp := (Real.hasDerivAt_exp (-u * (m : ℝ))).comp u hinner
      have := hexp.const_mul ((m : ℝ) ^ 2 * Sigma.sigmaR m)
      convert this using 1
      ring
  have hσ_dom : ∀ m : ℕ, ∀ u ∈ s,
      ‖fσ' m u‖ ≤ (m : ℝ) ^ 3 * Sigma.sigmaR m * r ^ m := by
    intro m u hu
    by_cases hm : m = 0
    · subst hm; simp [hfσ'def]
    · simp only [hfσ'def, if_neg hm]
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by
        have := sigmaR_nonneg m; positivity)]
      have hum : Real.exp (-u * (m : ℝ)) ≤ r ^ m := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hu2 : t / 2 < u := hu
        have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
        nlinarith
      have := sigmaR_nonneg m
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      exact mul_le_mul_of_nonneg_left hum (by positivity)
  have hσ_u_summable : Summable (fun m : ℕ => (m : ℝ) ^ 3 * Sigma.sigmaR m * r ^ m) := by
    have habs : |r| = r := abs_of_pos hr0
    have := summable_pow_sigma_geometric 3 (r := r)
      (by rw [Real.norm_eq_abs, habs]; exact hr1)
    rwa [habs] at this
  have hσ_at_t : Summable (fun m : ℕ => fσ m t) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => ?_) hσ_u_summable
    by_cases hm : m = 0
    · subst hm; simp [hfσdef]
    · simp only [hfσdef, if_neg hm]
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        have := sigmaR_nonneg m; positivity)]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
      have hum : Real.exp (-t * (m : ℝ)) ≤ r ^ m := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hσn := sigmaR_nonneg m
      have hs1 : (m : ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))
          ≤ (m : ℝ) ^ 2 * Sigma.sigmaR m * r ^ m :=
        mul_le_mul_of_nonneg_left hum (by positivity)
      have hs2 : (m : ℝ) ^ 2 * Sigma.sigmaR m * r ^ m
          ≤ (m : ℝ) ^ 3 * Sigma.sigmaR m * r ^ m := by
        have hmn : (0:ℝ) ≤ (m : ℝ) := by linarith
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg
          (by linarith : (0:ℝ) ≤ (m : ℝ) - 1) (by positivity : (0:ℝ) ≤ (m:ℝ)^2)) hσn)
          (pow_pos hr0 m).le]
      exact le_trans hs1 hs2
  have hA := hasDerivAt_tsum_of_isPreconnected hσ_u_summable hs_open hs_conn
    hσ_deriv hσ_dom hts hσ_at_t hts
  -- ===== Bose side: differentiate  k²·boseKernel3(uk)  →  −k³·boseKernel4(uk) =====
  set gB := (fun (k : ℕ) (u : ℝ) =>
    if k = 0 then (0:ℝ) else (k : ℝ) ^ 2 * boseKernel3 (u * (k : ℝ))) with hgBdef
  set gB' := (fun (k : ℕ) (u : ℝ) =>
    if k = 0 then (0:ℝ) else -(boseKernel4 (u * (k : ℝ))) * (k : ℝ) ^ 3) with hgB'def
  set CB := (24:ℝ) / (1 - Real.exp (-(t / 2))) ^ 5 with hCBdef
  have het2 : Real.exp (-(t / 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hdt2 : 0 < 1 - Real.exp (-(t / 2)) := by linarith
  have hCB0 : 0 < CB := by rw [hCBdef]; positivity
  have hB_deriv : ∀ k : ℕ, ∀ u ∈ s, HasDerivAt (gB k) (gB' k u) u := by
    intro k u hu
    by_cases hk : k = 0
    · subst hk
      simp only [hgBdef, hgB'def, if_pos rfl]
      exact hasDerivAt_const u 0
    · simp only [hgBdef, hgB'def, if_neg hk]
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
      have hu0 : 0 < u := lt_trans ht2 hu
      have hukpos : 0 < u * (k : ℝ) := by positivity
      have hinner : HasDerivAt (fun u : ℝ => u * (k : ℝ)) ((k : ℝ)) u := by
        simpa using (hasDerivAt_id u).mul_const ((k : ℝ))
      have houter := boseKernel3_hasDerivAt hukpos
      have hcomp := houter.comp u hinner
      have := (hcomp.const_mul ((k : ℝ) ^ 2))
      convert this using 1
      ring
  have hB_dom : ∀ k : ℕ, ∀ u ∈ s,
      ‖gB' k u‖ ≤ (k : ℝ) ^ 3 * CB * r ^ k := by
    intro k u hu
    by_cases hk : k = 0
    · subst hk; simp [hgB'def]
    · simp only [hgB'def, if_neg hk]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have hu2 : t / 2 < u := hu
      have hu0 : 0 < u := lt_trans ht2 hu2
      have hukpos : 0 < u * (k : ℝ) := mul_pos hu0 (by linarith)
      have hbk4_nonneg := boseKernel4_nonneg hukpos
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hbk4_nonneg, abs_pow,
        Nat.abs_cast]
      have hzge : t / 2 ≤ u * (k : ℝ) := by nlinarith
      have hle := boseKernel4_le ht2 hzge
      have hexp_le : Real.exp (-(u * (k : ℝ))) ≤ r ^ k := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hc1 : boseKernel4 (u * (k : ℝ)) * (k : ℝ) ^ 3
          ≤ (24 * Real.exp (-(u * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 5) * (k : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      have hc2 : (24 * Real.exp (-(u * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 5) * (k : ℝ) ^ 3
          = (k : ℝ) ^ 3 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * Real.exp (-(u * (k : ℝ))) := by
        ring
      have hc3 : (k : ℝ) ^ 3 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * Real.exp (-(u * (k : ℝ)))
          ≤ (k : ℝ) ^ 3 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * r ^ k :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
      have hc4 : (k : ℝ) ^ 3 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * r ^ k
          = (k : ℝ) ^ 3 * CB * r ^ k := by rw [hCBdef]
      exact le_trans (hc1.trans_eq hc2) (hc3.trans_eq hc4)
  have hB_u_summable : Summable (fun k : ℕ => (k : ℝ) ^ 3 * CB * r ^ k) := by
    have hbase : Summable (fun k : ℕ => (k : ℝ) ^ 3 * r ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3
        (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    have := hbase.mul_left CB
    refine this.congr fun k => ?_
    ring
  have hB_at_t : Summable (fun k : ℕ => gB k t) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (hB_u_summable.congr (fun k => rfl))
    by_cases hk : k = 0
    · subst hk; simp [hgBdef]
    · simp only [hgBdef, if_neg hk]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have htkpos : 0 < t * (k : ℝ) := by positivity
      have hbk3_nonneg := boseKernel3_nonneg htkpos
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hbk3_nonneg, abs_pow, Nat.abs_cast]
      have hzge : t / 2 ≤ t * (k : ℝ) := by nlinarith
      have hle := boseKernel3_le ht2 hzge
      have hexp_le : Real.exp (-(t * (k : ℝ))) ≤ r ^ k := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      -- k²·boseKernel3(tk) ≤ k²·(6 e^{−tk}/(1−e^{−t/2})⁴) ≤ k³·CB·r^k
      have hstep1 : (k : ℝ) ^ 2 * boseKernel3 (t * (k : ℝ))
          ≤ (k : ℝ) ^ 2 * (6 * Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 4) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have hstep2 : (k : ℝ) ^ 2 * (6 * Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 4)
          ≤ (k : ℝ) ^ 3 * CB * r ^ k := by
        rw [hCBdef]
        have hcoef : 6 / (1 - Real.exp (-(t / 2))) ^ 4
            ≤ 24 / (1 - Real.exp (-(t / 2))) ^ 5 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hd1 : 1 - Real.exp (-(t / 2)) ≤ 1 := by
            have := Real.exp_pos (-(t / 2)); linarith
          have hp4 : (0:ℝ) < (1 - Real.exp (-(t / 2))) ^ 4 := by positivity
          nlinarith [hp4, hd1, hdt2]
        have hexp0 := Real.exp_pos (-(t * (k : ℝ)))
        have hr_pow : (0:ℝ) < r ^ k := pow_pos hr0 k
        have hk3 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by nlinarith
        calc (k : ℝ) ^ 2 * (6 * Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 4)
            = (k : ℝ) ^ 2 * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * Real.exp (-(t * (k : ℝ))) := by
              ring
          _ ≤ (k : ℝ) ^ 2 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * Real.exp (-(t * (k : ℝ))) := by
              apply mul_le_mul_of_nonneg_right _ hexp0.le
              exact mul_le_mul_of_nonneg_left hcoef (by positivity)
          _ ≤ (k : ℝ) ^ 2 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * r ^ k :=
            mul_le_mul_of_nonneg_left hexp_le (by positivity)
          _ ≤ (k : ℝ) ^ 3 * (24 / (1 - Real.exp (-(t / 2))) ^ 5) * r ^ k := by
              apply mul_le_mul_of_nonneg_right _ hr_pow.le
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact hk3
      exact le_trans hstep1 hstep2
  have hB := hasDerivAt_tsum_of_isPreconnected hB_u_summable hs_open hs_conn
    hB_deriv hB_dom hts hB_at_t hts
  -- ===== the two sums agree on s =====
  have hEq : (fun z => ∑' m : ℕ, fσ m z) =ᶠ[𝓝 t] (fun z => ∑' k : ℕ, gB k z) := by
    filter_upwards [hs_open.mem_nhds hts] with u hu
    have hu0 : 0 < u := lt_trans ht2 hu
    have hML := sigmaMoment_two_lambert (t := u) hu0
    have hLHS : sigmaMoment 2 u = ∑' m : ℕ, fσ m u := by
      rw [sigmaMoment]
    have hRHS : (∑' k : ℕ, if k = 0 then 0 else (k : ℝ) ^ 2 * boseKernel3 (u * (k : ℝ)))
        = ∑' k : ℕ, gB k u := by
      refine tsum_congr fun k => ?_
      by_cases hk : k = 0
      · subst hk; simp [hgBdef]
      · simp only [hgBdef, if_neg hk]
    rw [← hLHS, hML, ← hRHS]
  -- transfer the derivative + uniqueness
  have hA' : HasDerivAt (fun z => ∑' k : ℕ, gB k z) (∑' m : ℕ, fσ' m t) t :=
    hA.congr_of_eventuallyEq hEq.symm
  have huniq := hA'.unique hB
  have hLHS' : (∑' m : ℕ, fσ' m t) = -(sigmaMoment 3 t) := by
    rw [sigmaMoment, ← tsum_neg]
    refine tsum_congr fun m => ?_
    by_cases hm : m = 0
    · subst hm; simp [hfσ'def]
    · simp only [hfσ'def, if_neg hm]
  have hRHS' : (∑' k : ℕ, gB' k t)
      = -(∑' k : ℕ, if k = 0 then 0 else (k : ℝ) ^ 3 * boseKernel4 (t * (k : ℝ))) := by
    rw [← tsum_neg]
    refine tsum_congr fun k => ?_
    by_cases hk : k = 0
    · subst hk; simp [hgB'def]
    · simp only [hgB'def, if_neg hk]
      ring
  rw [hLHS', hRHS'] at huniq
  linarith [huniq]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
