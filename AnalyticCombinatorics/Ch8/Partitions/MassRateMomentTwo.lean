import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentOne

/-!
# Mass-rate campaign: the `M₂` Lambert identity by termwise differentiation

`M₂(t) = Σ_k k²·boseKernel3(tk)`, `boseKernel3(z) = e^{−z}(1+4e^{−z}+e^{−2z})/(1−e^{−z})⁴
= Σ_d d³e^{−dz}` — obtained by differentiating both sides of `sigmaMoment_one_lambert`
termwise on `Ioi (t/2)` via `hasDerivAt_tsum_of_isPreconnected`, then `HasDerivAt.unique`.
Mirror of `MassRateMomentOne`.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `Σ_d d³ e^{−dz}` in closed form. -/
noncomputable def boseKernel3 (z : ℝ) : ℝ :=
  Real.exp (-z) * (1 + 4 * Real.exp (-z) + Real.exp (-z) ^ 2) / (1 - Real.exp (-z)) ^ 4

/-- `boseKernel2` has derivative `−boseKernel3` on `(0,∞)` (quotient rule). -/
lemma boseKernel2_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt boseKernel2 (-boseKernel3 z) z := by
  have hy1 : Real.exp (-z) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd0 : (0:ℝ) < 1 - Real.exp (-z) := by linarith
  have hy : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-z)) z := by
    have hinner : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) z := by
      simpa using (hasDerivAt_id z).neg
    simpa using (Real.hasDerivAt_exp (-z)).comp z hinner
  -- numerator y(1+y)
  have hone : HasDerivAt (fun u : ℝ => 1 + Real.exp (-u)) (-Real.exp (-z)) z :=
    hy.const_add 1
  have hN := hy.mul hone
  -- denominator (1−y)³
  have hbase : HasDerivAt (fun u : ℝ => 1 - Real.exp (-u)) (Real.exp (-z)) z := by
    simpa using hy.const_sub 1
  have hD := hbase.pow 3
  have hQ := hN.div hD (pow_ne_zero 3 hd0.ne')
  have hshape : boseKernel2
      = fun u : ℝ => Real.exp (-u) * (1 + Real.exp (-u)) / (1 - Real.exp (-u)) ^ 3 := rfl
  rw [hshape]
  convert hQ using 1
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply]
  rw [boseKernel3]
  field_simp
  ring

/-- `boseKernel3 ≥ 0` on `(0,∞)`. -/
lemma boseKernel3_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ boseKernel3 z := by
  have h1 : Real.exp (-z) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h2 : 0 < 1 - Real.exp (-z) := by linarith
  rw [boseKernel3]
  positivity

/-- Tail comparison: `boseKernel3(z) ≤ 6e^{−z}/(1−e^{−a})⁴` for `z ≥ a > 0`. -/
lemma boseKernel3_le {a z : ℝ} (ha : 0 < a) (hz : a ≤ z) :
    boseKernel3 z ≤ 6 * Real.exp (-z) / (1 - Real.exp (-a)) ^ 4 := by
  have hea : Real.exp (-a) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hda : 0 < 1 - Real.exp (-a) := by linarith
  have hez : Real.exp (-z) ≤ Real.exp (-a) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hdz : 0 < 1 - Real.exp (-z) := by linarith
  have hd_mono : 1 - Real.exp (-a) ≤ 1 - Real.exp (-z) := by linarith
  rw [boseKernel3]
  apply div_le_div₀ (by positivity)
  · have h2 : 1 + 4 * Real.exp (-z) + Real.exp (-z) ^ 2 ≤ 6 := by
      nlinarith [Real.exp_pos (-z), hez, hea]
    nlinarith [Real.exp_pos (-z)]
  · positivity
  · exact pow_le_pow_left₀ hda.le hd_mono 4

/--
**The `M₂` Lambert identity** (termwise differentiation of the `M₁` identity):

  `Σ_m m²·σ(m)e^{−tm} = Σ_k k²·boseKernel3(tk)`.
-/
theorem sigmaMoment_two_lambert {t : ℝ} (ht : 0 < t) :
    sigmaMoment 2 t
      = ∑' k : ℕ, if k = 0 then 0 else (k : ℝ) ^ 2 * boseKernel3 (t * (k : ℝ)) := by
  classical
  have ht2 : 0 < t / 2 := by linarith
  set s := Set.Ioi (t / 2) with hsdef
  have hs_open : IsOpen s := isOpen_Ioi
  have hs_conn : IsPreconnected s := (convex_Ioi _).isPreconnected
  have hts : t ∈ s := by
    rw [hsdef]
    exact Set.mem_Ioi.mpr (by linarith)
  set r := Real.exp (-(t / 2)) with hrdef
  have hr1 : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff]
    linarith
  have hr0 : 0 < r := Real.exp_pos _
  -- ===== σ-side =====
  set fσ := (fun (m : ℕ) (u : ℝ) =>
    if m = 0 then (0:ℝ) else (m : ℝ) * Sigma.sigmaR m * Real.exp (-u * (m : ℝ))) with hfσdef
  set fσ' := (fun (m : ℕ) (u : ℝ) =>
    if m = 0 then (0:ℝ)
    else -((m : ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-u * (m : ℝ)))) with hfσ'def
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
      have := hexp.const_mul ((m : ℝ) * Sigma.sigmaR m)
      convert this using 1
      ring
  have hσ_dom : ∀ m : ℕ, ∀ u ∈ s,
      ‖fσ' m u‖ ≤ (m : ℝ) ^ 2 * Sigma.sigmaR m * r ^ m := by
    intro m u hu
    by_cases hm : m = 0
    · subst hm
      simp [hfσ'def]
    · simp only [hfσ'def, if_neg hm]
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by
        have := sigmaR_nonneg m
        positivity)]
      have hum : Real.exp (-u * (m : ℝ)) ≤ r ^ m := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hu2 : t / 2 < u := hu
        have hm0 : (0 : ℝ) < (m : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hm
        nlinarith
      have := sigmaR_nonneg m
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      exact mul_le_mul_of_nonneg_left hum (by positivity)
  have hσ_u_summable : Summable (fun m : ℕ => (m : ℝ) ^ 2 * Sigma.sigmaR m * r ^ m) := by
    have habs : |r| = r := abs_of_pos hr0
    have := summable_pow_sigma_geometric 2 (r := r)
      (by rw [Real.norm_eq_abs, habs]; exact hr1)
    rwa [habs] at this
  have hσ_at_t : Summable (fun m : ℕ => fσ m t) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => ?_) hσ_u_summable
    by_cases hm : m = 0
    · subst hm
      simp [hfσdef]
    · simp only [hfσdef, if_neg hm]
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        have := sigmaR_nonneg m
        positivity)]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
      have hum : Real.exp (-t * (m : ℝ)) ≤ r ^ m := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hσn := sigmaR_nonneg m
      have hs1 : (m : ℝ) * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))
          ≤ (m : ℝ) * Sigma.sigmaR m * r ^ m :=
        mul_le_mul_of_nonneg_left hum (by positivity)
      have hs2 : (m : ℝ) * Sigma.sigmaR m * r ^ m
          ≤ (m : ℝ) ^ 2 * Sigma.sigmaR m * r ^ m := by
        have hmn : (0:ℝ) ≤ (m : ℝ) := by linarith
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg
          (by linarith : (0:ℝ) ≤ (m : ℝ) - 1) hmn) hσn) (pow_pos hr0 m).le]
      exact le_trans hs1 hs2
  have hA := hasDerivAt_tsum_of_isPreconnected hσ_u_summable hs_open hs_conn
    hσ_deriv hσ_dom hts hσ_at_t hts
  -- ===== Bose side =====
  set gB := (fun (k : ℕ) (u : ℝ) =>
    if k = 0 then (0:ℝ) else (k : ℝ) * boseKernel2 (u * (k : ℝ))) with hgBdef
  set gB' := (fun (k : ℕ) (u : ℝ) =>
    if k = 0 then (0:ℝ) else -(boseKernel3 (u * (k : ℝ))) * (k : ℝ) ^ 2) with hgB'def
  set CB := (6:ℝ) / (1 - Real.exp (-(t / 2))) ^ 4 with hCBdef
  have het2 : Real.exp (-(t / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hdt2 : 0 < 1 - Real.exp (-(t / 2)) := by linarith
  have hCB0 : 0 < CB := by
    rw [hCBdef]
    positivity
  have hB_deriv : ∀ k : ℕ, ∀ u ∈ s, HasDerivAt (gB k) (gB' k u) u := by
    intro k u hu
    by_cases hk : k = 0
    · subst hk
      simp only [hgBdef, hgB'def, if_pos rfl]
      exact hasDerivAt_const u 0
    · simp only [hgBdef, hgB'def, if_neg hk]
      have hk0 : (0 : ℝ) < (k : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      have hu0 : 0 < u := lt_trans ht2 hu
      have hukpos : 0 < u * (k : ℝ) := by positivity
      have hinner : HasDerivAt (fun u : ℝ => u * (k : ℝ)) ((k : ℝ)) u := by
        simpa using (hasDerivAt_id u).mul_const ((k : ℝ))
      have houter := boseKernel2_hasDerivAt hukpos
      have hcomp := houter.comp u hinner
      have := hcomp.const_mul ((k : ℝ))
      convert this using 1
      ring
  have hB_dom : ∀ k : ℕ, ∀ u ∈ s,
      ‖gB' k u‖ ≤ (k : ℝ) ^ 2 * CB * r ^ k := by
    intro k u hu
    by_cases hk : k = 0
    · subst hk
      simp [hgB'def]
    · simp only [hgB'def, if_neg hk]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have hu2 : t / 2 < u := hu
      have hu0 : 0 < u := lt_trans ht2 hu2
      have hukpos : 0 < u * (k : ℝ) := mul_pos hu0 (by linarith)
      have hbk3_nonneg := boseKernel3_nonneg hukpos
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hbk3_nonneg, abs_pow,
        Nat.abs_cast]
      have hzge : t / 2 ≤ u * (k : ℝ) := by nlinarith
      have hle := boseKernel3_le ht2 hzge
      have hexp_le : Real.exp (-(u * (k : ℝ))) ≤ r ^ k := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hc1 : boseKernel3 (u * (k : ℝ)) * (k : ℝ) ^ 2
          ≤ (6 * Real.exp (-(u * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 4) * (k : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      have hc2 : (6 * Real.exp (-(u * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 4) * (k : ℝ) ^ 2
          = (k : ℝ) ^ 2 * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * Real.exp (-(u * (k : ℝ))) := by
        ring
      have hc3 : (k : ℝ) ^ 2 * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * Real.exp (-(u * (k : ℝ)))
          ≤ (k : ℝ) ^ 2 * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * r ^ k :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
      have hc4 : (k : ℝ) ^ 2 * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * r ^ k
          = (k : ℝ) ^ 2 * CB * r ^ k := by
        rw [hCBdef]
      exact le_trans (hc1.trans_eq hc2) (hc3.trans_eq hc4)
  have hB_u_summable : Summable (fun k : ℕ => (k : ℝ) ^ 2 * CB * r ^ k) := by
    have hbase : Summable (fun k : ℕ => (k : ℝ) ^ 2 * r ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
        (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    have := hbase.mul_left CB
    refine this.congr fun k => ?_
    ring
  have hB_at_t : Summable (fun k : ℕ => gB k t) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (hB_u_summable.congr (fun k => rfl))
    by_cases hk : k = 0
    · subst hk
      simp [hgBdef]
    · simp only [hgBdef, if_neg hk]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      have htkpos : 0 < t * (k : ℝ) := by positivity
      have hbk2_nonneg := boseKernel2_nonneg htkpos
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hbk2_nonneg, Nat.abs_cast]
      have hzge : t / 2 ≤ t * (k : ℝ) := by nlinarith
      have hle := boseKernel2_le ht2 hzge
      have hexp_le : Real.exp (-(t * (k : ℝ))) ≤ r ^ k := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      -- k·boseKernel2(tk) ≤ k·(2e^{−tk}/(1−e^{−t/2})³) ≤ k²·CB·r^k
      have hstep1 : (k : ℝ) * boseKernel2 (t * (k : ℝ))
          ≤ (k : ℝ) * (2 * Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 3) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have hstep2 : (k : ℝ) * (2 * Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 3)
          ≤ (k : ℝ) ^ 2 * CB * r ^ k := by
        rw [hCBdef]
        have hcoef : 2 / (1 - Real.exp (-(t / 2))) ^ 3
            ≤ 6 / (1 - Real.exp (-(t / 2))) ^ 4 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hd1 : 1 - Real.exp (-(t / 2)) ≤ 1 := by
            have := Real.exp_pos (-(t / 2))
            linarith
          have hp3 : (0:ℝ) < (1 - Real.exp (-(t / 2))) ^ 3 := by positivity
          nlinarith [hp3, hd1, hdt2]
        have hexp0 := Real.exp_pos (-(t * (k : ℝ)))
        have hr_pow : (0:ℝ) < r ^ k := pow_pos hr0 k
        have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
        calc (k : ℝ) * (2 * Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 3)
            = (k : ℝ) * (2 / (1 - Real.exp (-(t / 2))) ^ 3) * Real.exp (-(t * (k : ℝ))) := by
              ring
          _ ≤ (k : ℝ) * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * Real.exp (-(t * (k : ℝ))) := by
              apply mul_le_mul_of_nonneg_right _ hexp0.le
              exact mul_le_mul_of_nonneg_left hcoef (by linarith)
          _ ≤ (k : ℝ) * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * r ^ k :=
            mul_le_mul_of_nonneg_left hexp_le (by positivity)
          _ ≤ (k : ℝ) ^ 2 * (6 / (1 - Real.exp (-(t / 2))) ^ 4) * r ^ k := by
              apply mul_le_mul_of_nonneg_right _ hr_pow.le
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              nlinarith
      exact le_trans hstep1 hstep2
  have hB := hasDerivAt_tsum_of_isPreconnected hB_u_summable hs_open hs_conn
    hB_deriv hB_dom hts hB_at_t hts
  -- ===== the two sums agree on s =====
  have hEq : (fun z => ∑' m : ℕ, fσ m z) =ᶠ[𝓝 t] (fun z => ∑' k : ℕ, gB k z) := by
    filter_upwards [hs_open.mem_nhds hts] with u hu
    have hu0 : 0 < u := lt_trans ht2 hu
    have hML := sigmaMoment_one_lambert (t := u) hu0
    have hLHS : sigmaMoment 1 u = ∑' m : ℕ, fσ m u := by
      rw [sigmaMoment]
      refine tsum_congr fun m => ?_
      by_cases hm : m = 0
      · subst hm
        simp [hfσdef]
      · simp only [hfσdef, if_neg hm]
        rw [pow_one]
    have hRHS : (∑' k : ℕ, if k = 0 then 0 else (k : ℝ) * boseKernel2 (u * (k : ℝ)))
        = ∑' k : ℕ, gB k u := by
      refine tsum_congr fun k => ?_
      by_cases hk : k = 0
      · subst hk
        simp [hgBdef]
      · simp only [hgBdef, if_neg hk]
    rw [← hLHS, hML, ← hRHS]
  -- transfer the derivative + uniqueness
  have hA' : HasDerivAt (fun z => ∑' k : ℕ, gB k z) (∑' m : ℕ, fσ' m t) t :=
    hA.congr_of_eventuallyEq hEq.symm
  have huniq := hA'.unique hB
  have hLHS' : (∑' m : ℕ, fσ' m t) = -(sigmaMoment 2 t) := by
    rw [sigmaMoment, ← tsum_neg]
    refine tsum_congr fun m => ?_
    by_cases hm : m = 0
    · subst hm
      simp [hfσ'def]
    · simp only [hfσ'def, if_neg hm]
  have hRHS' : (∑' k : ℕ, gB' k t)
      = -(∑' k : ℕ, if k = 0 then 0 else (k : ℝ) ^ 2 * boseKernel3 (t * (k : ℝ))) := by
    rw [← tsum_neg]
    refine tsum_congr fun k => ?_
    by_cases hk : k = 0
    · subst hk
      simp [hgB'def]
    · simp only [hgB'def, if_neg hk]
      ring
  rw [hLHS', hRHS'] at huniq
  linarith [huniq]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
