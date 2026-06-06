import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateDerivInt
import AnalyticCombinatorics.Ch8.Partitions.MassRateLambert

/-!
# Mass-rate campaign: the `M₁` Lambert identity by termwise differentiation

`M₁(t) = Σ_k k·boseKernel2(tk)`, `boseKernel2(z) = e^{−z}(1+e^{−z})/(1−e^{−z})³ = Σ_d d²e^{−dz}`
— obtained by differentiating both sides of the banked `M₀` Lambert identity termwise on
`Ioi (t/2)` via `hasDerivAt_tsum_of_isPreconnected`, then `HasDerivAt.unique`.
Replaces the retired antidiagonal draft.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `Σ_d d² e^{−dz}` in closed form. -/
noncomputable def boseKernel2 (z : ℝ) : ℝ :=
  Real.exp (-z) * (1 + Real.exp (-z)) / (1 - Real.exp (-z)) ^ 3

/-- `boseKernel` has derivative `−boseKernel2` on `(0,∞)`. -/
lemma boseKernel_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt boseKernel (-boseKernel2 z) z := by
  have hy : 0 < Real.exp z - 1 := by
    have := Real.add_one_lt_exp (x := z) hz.ne'
    linarith
  have hez := Real.exp_pos z
  -- boseKernel = boseReg0 + 1/x² near z
  have h1 := boseReg0_hasDerivAt hz
  have h2 : HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-(2 / z ^ 3)) z := by
    have ha : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z ^ 1) z := hasDerivAt_pow 2 z
    have hb := ha.inv (pow_ne_zero 2 hz.ne')
    have heq : -(2 * z ^ 1) / (z ^ 2) ^ 2 = -(2 / z ^ 3) := by
      field_simp
    have h3 : HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹) (-(2 / z ^ 3)) z := by
      rw [← heq]
      convert hb using 1
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [one_div]
  have hsum := h1.add h2
  have hev : boseKernel =ᶠ[𝓝 z] fun y => boseReg0 y + 1 / y ^ 2 := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with y _hy
    rw [boseReg0]
    ring
  have hfinal := hsum.congr_of_eventuallyEq hev
  -- identify the derivative value
  have hval : boseReg0Deriv z + -(2 / z ^ 3) = -boseKernel2 z := by
    rw [boseReg0Deriv, boseKernel2]
    have hexp_form : Real.exp z * (Real.exp z + 1) / (Real.exp z - 1) ^ 3
        = Real.exp (-z) * (1 + Real.exp (-z)) / (1 - Real.exp (-z)) ^ 3 := by
      rw [Real.exp_neg]
      field_simp
    rw [← hexp_form]
    ring
  rwa [hval] at hfinal

/-- Summability of `m^j·σ(m)·r^m` for `‖r‖ < 1`. -/
lemma summable_pow_sigma_geometric (j : ℕ) {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun m : ℕ => (m : ℝ) ^ j * Sigma.sigmaR m * |r| ^ m) := by
  have hr' : ‖|r|‖ < 1 := by
    rw [Real.norm_eq_abs, abs_abs]
    rwa [Real.norm_eq_abs] at hr
  have hbig := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (j + 2) hr'
  refine Summable.of_nonneg_of_le
    (f := fun m : ℕ => ((m : ℝ)) ^ (j + 2) * |r| ^ m) (fun m => ?_) (fun m => ?_) hbig
  · have := sigmaR_nonneg m
    positivity
  ·
    by_cases hm : m = 0
    · subst hm
      have hσ0 : Sigma.sigmaR 0 = 0 := by
        rw [sigmaR_eq_sigma_one]
        simp
      simp only [hσ0, Nat.cast_zero, mul_zero, zero_mul]
      positivity
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hσ : Sigma.sigmaR m ≤ (m : ℝ) ^ 2 := sigmaR_le_square hm1
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have habs : (0 : ℝ) ≤ |r| ^ m := by positivity
      calc (m : ℝ) ^ j * Sigma.sigmaR m * |r| ^ m
          ≤ (m : ℝ) ^ j * (m : ℝ) ^ 2 * |r| ^ m := by
            apply mul_le_mul_of_nonneg_right _ habs
            exact mul_le_mul_of_nonneg_left hσ (by positivity)
        _ = (m : ℝ) ^ (j + 2) * |r| ^ m := by ring

/-- `boseKernel2 ≥ 0` on `(0,∞)`. -/
lemma boseKernel2_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ boseKernel2 z := by
  have h1 : Real.exp (-z) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h2 : 0 < 1 - Real.exp (-z) := by linarith
  rw [boseKernel2]
  positivity

/-- Tail comparison: `boseKernel2(z) ≤ 2e^{−z}/(1−e^{−a})³` for `z ≥ a > 0`. -/
lemma boseKernel2_le {a z : ℝ} (ha : 0 < a) (hz : a ≤ z) :
    boseKernel2 z ≤ 2 * Real.exp (-z) / (1 - Real.exp (-a)) ^ 3 := by
  have hea : Real.exp (-a) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hda : 0 < 1 - Real.exp (-a) := by linarith
  have hez : Real.exp (-z) ≤ Real.exp (-a) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hdz : 0 < 1 - Real.exp (-z) := by linarith
  have hd_mono : 1 - Real.exp (-a) ≤ 1 - Real.exp (-z) := by linarith
  rw [boseKernel2]
  apply div_le_div₀ (by positivity)
  · have h2 : 1 + Real.exp (-z) ≤ 2 := by
      have := Real.exp_pos (-z)
      linarith [hez, hea]
    nlinarith [Real.exp_pos (-z)]
  · positivity
  · exact pow_le_pow_left₀ hda.le hd_mono 3

/--
**The `M₁` Lambert identity** (termwise differentiation of the `M₀` identity):

  `Σ_m m·σ(m)e^{−tm} = Σ_k k·boseKernel2(tk)`.
-/
theorem sigmaMoment_one_lambert {t : ℝ} (ht : 0 < t) :
    sigmaMoment 1 t
      = ∑' k : ℕ, if k = 0 then 0 else (k : ℝ) * boseKernel2 (t * (k : ℝ)) := by
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
    if m = 0 then (0:ℝ) else Sigma.sigmaR m * Real.exp (-u * (m : ℝ))) with hfσdef
  set fσ' := (fun (m : ℕ) (u : ℝ) =>
    if m = 0 then (0:ℝ) else -((m : ℝ) * Sigma.sigmaR m * Real.exp (-u * (m : ℝ)))) with hfσ'def
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
      have := hexp.const_mul (Sigma.sigmaR m)
      convert this using 1
      ring
  have hσ_dom : ∀ m : ℕ, ∀ u ∈ s, ‖fσ' m u‖ ≤ (m : ℝ) * Sigma.sigmaR m * r ^ m := by
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
  have hσ_u_summable : Summable (fun m : ℕ => (m : ℝ) * Sigma.sigmaR m * r ^ m) := by
    have habs : |r| = r := abs_of_pos hr0
    have := summable_pow_sigma_geometric 1 (r := r)
      (by rw [Real.norm_eq_abs, habs]; exact hr1)
    rw [habs] at this
    refine this.congr fun m => ?_
    rw [pow_one]
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
      have hs1 : Sigma.sigmaR m * Real.exp (-t * (m : ℝ)) ≤ Sigma.sigmaR m * r ^ m :=
        mul_le_mul_of_nonneg_left hum hσn
      have hs2 : Sigma.sigmaR m * r ^ m ≤ (m : ℝ) * Sigma.sigmaR m * r ^ m := by
        nlinarith [mul_nonneg (mul_nonneg
          (by linarith : (0:ℝ) ≤ (m : ℝ) - 1) hσn) (pow_pos hr0 m).le]
      exact le_trans hs1 hs2
  have hA := hasDerivAt_tsum_of_isPreconnected hσ_u_summable hs_open hs_conn
    hσ_deriv hσ_dom hts hσ_at_t hts
  -- ===== Bose side =====
  set gB := (fun (k : ℕ) (u : ℝ) =>
    if k = 0 then (0:ℝ) else boseKernel (u * (k : ℝ))) with hgBdef
  set gB' := (fun (k : ℕ) (u : ℝ) =>
    if k = 0 then (0:ℝ) else -(boseKernel2 (u * (k : ℝ))) * (k : ℝ)) with hgB'def
  set CB := (2:ℝ) / (1 - Real.exp (-(t / 2))) ^ 3 with hCBdef
  have hCB0 : 0 < CB := by
    rw [hCBdef]
    have : Real.exp (-(t / 2)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have : 0 < 1 - Real.exp (-(t / 2)) := by linarith
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
      have houter := boseKernel_hasDerivAt hukpos
      have := houter.comp u hinner
      convert this using 1
  have hB_dom : ∀ k : ℕ, ∀ u ∈ s,
      ‖gB' k u‖ ≤ (k : ℝ) * CB * r ^ k := by
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
      have hbk2_nonneg := boseKernel2_nonneg hukpos
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hbk2_nonneg,
        Nat.abs_cast]
      have hzge : t / 2 ≤ u * (k : ℝ) := by nlinarith
      have hle := boseKernel2_le ht2 hzge
      have hexp_le : Real.exp (-(u * (k : ℝ))) ≤ r ^ k := by
        rw [hrdef, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith
      have hc1 : boseKernel2 (u * (k : ℝ)) * (k : ℝ)
          ≤ (2 * Real.exp (-(u * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 3) * (k : ℝ) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      have hc2 : (2 * Real.exp (-(u * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 3) * (k : ℝ)
          = (k : ℝ) * (2 / (1 - Real.exp (-(t / 2))) ^ 3) * Real.exp (-(u * (k : ℝ))) := by
        ring
      have hc3 : (k : ℝ) * (2 / (1 - Real.exp (-(t / 2))) ^ 3) * Real.exp (-(u * (k : ℝ)))
          ≤ (k : ℝ) * (2 / (1 - Real.exp (-(t / 2))) ^ 3) * r ^ k :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
      have hc4 : (k : ℝ) * (2 / (1 - Real.exp (-(t / 2))) ^ 3) * r ^ k
          = (k : ℝ) * CB * r ^ k := by
        rw [hCBdef]
      exact le_trans (hc1.trans_eq hc2) (hc3.trans_eq hc4)
  have hB_u_summable : Summable (fun k : ℕ => (k : ℝ) * CB * r ^ k) := by
    have hbase : Summable (fun k : ℕ => (k : ℝ) * r ^ k) :=
      (hasSum_coe_mul_geometric_of_norm_lt_one
        (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)).summable
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
      have hbk_pos : 0 < boseKernel (t * (k : ℝ)) := by
        rw [boseKernel]
        have h1 : Real.exp (-(t * (k : ℝ))) < 1 := by
          rw [Real.exp_lt_one_iff]
          linarith
        have h2 : 0 < 1 - Real.exp (-(t * (k : ℝ))) := by linarith
        positivity
      rw [Real.norm_eq_abs, abs_of_pos hbk_pos]
      -- boseKernel(tk) ≤ boseKernel2(tk) ≤ CB·r^k ≤ k·CB·r^k
      have h2 : boseKernel (t * (k : ℝ)) ≤ CB * r ^ k := by
        have hzge : t / 2 ≤ t * (k : ℝ) := by nlinarith
        have hea : Real.exp (-(t / 2)) < 1 := by
          rw [Real.exp_lt_one_iff]
          linarith
        have hda : 0 < 1 - Real.exp (-(t / 2)) := by linarith
        have hez : Real.exp (-(t * (k : ℝ))) ≤ Real.exp (-(t / 2)) := by
          apply Real.exp_le_exp.mpr
          linarith
        have hdz : 0 < 1 - Real.exp (-(t * (k : ℝ))) := by linarith
        have hd_mono : 1 - Real.exp (-(t / 2)) ≤ 1 - Real.exp (-(t * (k : ℝ))) := by
          linarith
        have hexp_le : Real.exp (-(t * (k : ℝ))) ≤ r ^ k := by
          rw [hrdef, ← Real.exp_nat_mul]
          apply Real.exp_le_exp.mpr
          nlinarith
        rw [boseKernel, hCBdef]
        have ho1 : Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t * (k : ℝ)))) ^ 2
            ≤ Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 2 := by
          apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
          exact pow_le_pow_left₀ hda.le hd_mono 2
        have ho2 : Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t / 2))) ^ 2
            ≤ (2 / (1 - Real.exp (-(t / 2))) ^ 3) * r ^ k := by
          rw [div_eq_mul_inv, mul_comm]
          have hkey : ((1 - Real.exp (-(t / 2))) ^ 2)⁻¹
              ≤ 2 / (1 - Real.exp (-(t / 2))) ^ 3 := by
            rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hda, Real.exp_pos (-(t / 2))]
          apply mul_le_mul hkey hexp_le (Real.exp_pos _).le (by positivity)
        exact le_trans ho1 ho2
      have hf2 : CB * r ^ k ≤ (k : ℝ) * CB * r ^ k := by
        nlinarith [pow_pos hr0 k, hCB0]
      exact le_trans h2 hf2
  have hB := hasDerivAt_tsum_of_isPreconnected hB_u_summable hs_open hs_conn
    hB_deriv hB_dom hts hB_at_t hts
  -- ===== the two sums agree on s =====
  have hEq : (fun z => ∑' m : ℕ, fσ m z) =ᶠ[𝓝 t] (fun z => ∑' k : ℕ, gB k z) := by
    filter_upwards [hs_open.mem_nhds hts] with u hu
    have hu0 : 0 < u := lt_trans ht2 hu
    have hML := sigmaMoment_zero_lambert (t := u) hu0
    have hLHS : sigmaMoment 0 u = ∑' m : ℕ, fσ m u := by
      rw [sigmaMoment]
      refine tsum_congr fun m => ?_
      by_cases hm : m = 0
      · subst hm
        simp [hfσdef]
      · simp only [hfσdef, if_neg hm]
        rw [pow_zero, one_mul]
    have hRHS : (∑' k : ℕ, if k = 0 then 0 else boseKernel (u * (k : ℝ)))
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
  -- huniq : Σ' fσ' m t = Σ' gB' k t; negate
  have hLHS' : (∑' m : ℕ, fσ' m t) = -(sigmaMoment 1 t) := by
    rw [sigmaMoment, ← tsum_neg]
    refine tsum_congr fun m => ?_
    by_cases hm : m = 0
    · subst hm
      simp [hfσ'def]
    · simp only [hfσ'def, if_neg hm]
      ring
  have hRHS' : (∑' k : ℕ, gB' k t)
      = -(∑' k : ℕ, if k = 0 then 0 else (k : ℝ) * boseKernel2 (t * (k : ℝ))) := by
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
