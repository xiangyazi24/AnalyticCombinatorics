import AnalyticCombinatorics.Ch7.SingularityApp.CayleySecondOrder
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Third-order Cayley tree-function coefficient asymptotic

This file extends the Stirling route from `CayleySecondOrder` by one relative
order.  The sharper log-tail squeeze is

`1/(12n) - 1/n^3 ≤ log (stirlingSeq n / sqrt pi) ≤ 1/(12n)`,

which is enough to exponentiate `-log (stirlingSeq n / sqrt pi)` through the
quadratic term.  The third relative Cayley coefficient is `1/288`.
-/

set_option maxHeartbeats 1200000

open Filter Asymptotics
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

noncomputable section

def cayleyRelativeThirdConstant : ℝ :=
  1 / 288

def cayleyThirdOrderApprox (n : ℕ) : ℝ :=
  cayleyMainTerm n *
    (1 + cayleyRelativeSecondConstant * (n : ℝ)⁻¹ +
      cayleyRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2)

private def stirlingLog (n : ℕ) : ℝ :=
  Real.log (Stirling.stirlingSeq n)

private def stirlingLogTail (n : ℕ) : ℝ :=
  stirlingLog n - Real.log (Real.sqrt Real.pi)

private def stirlingLogCorr (n : ℕ) : ℝ :=
  (1 / 12 : ℝ) * (n : ℝ)⁻¹

private def stirlingLogCorrLower (n : ℕ) : ℝ :=
  stirlingLogCorr n - ((n : ℝ)⁻¹) ^ 3

lemma cayleyRelativeThirdConstant_eq :
    cayleyRelativeThirdConstant = (1 / 288 : ℝ) := rfl

private lemma stirlingSeq_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < Stirling.stirlingSeq n := by
  cases n with
  | zero => cases hn
  | succ n => simpa using Stirling.stirlingSeq'_pos n

private lemma stirlingLog_tendsto_log_sqrt_pi :
    Tendsto stirlingLog atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
  have hlog :=
    (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  simpa [stirlingLog] using hlog

private lemma stirlingLogCorr_tendsto_zero :
    Tendsto stirlingLogCorr atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1 / 12 : ℝ) * (n : ℝ)⁻¹) atTop (𝓝 0)
  simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 12 : ℝ)

private lemma inv_nat_cube_tendsto_zero :
    Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) atTop (𝓝 0) := by
  simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 3

private lemma stirlingLogCorrLower_tendsto_zero :
    Tendsto stirlingLogCorrLower atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => stirlingLogCorr n - ((n : ℝ)⁻¹) ^ 3) atTop (𝓝 0)
  simpa [sub_zero] using stirlingLogCorr_tendsto_zero.sub inv_nat_cube_tendsto_zero

private lemma stirlingLogCorr_sub_succ (n : ℕ) (hn : n ≠ 0) :
    stirlingLogCorr n - stirlingLogCorr (n + 1) =
      1 / (12 * (n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn1R : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold stirlingLogCorr
  field_simp [hnR, hn1R]
  norm_num [Nat.cast_add]

private lemma stirlingLog_diff_le_corr_diff {n : ℕ} (hn : 1 ≤ n) :
    stirlingLog n - stirlingLog (n + 1) ≤
      stirlingLogCorr n - stirlingLogCorr (n + 1) := by
  have hn0 : n ≠ 0 := by omega
  rw [stirlingLogCorr_sub_succ n hn0]
  simpa [stirlingLog] using Stirling.log_stirlingSeq_diff_le n

private lemma stirlingLog_diff_first_term_le {n : ℕ} (hn : 1 ≤ n) :
    1 / (3 * (2 * (n : ℝ) + 1) ^ 2) ≤
      stirlingLog n - stirlingLog (n + 1) := by
  classical
  let f : ℕ → ℝ := fun j =>
    (1 : ℝ) / (2 * ((j + 1 : ℕ) : ℝ) + 1) *
      (((1 : ℝ) / (2 * (((n - 1 : ℕ) + 1 : ℕ) : ℝ) + 1)) ^ 2) ^ (j + 1)
  have hsum : HasSum f (stirlingLog n - stirlingLog (n + 1)) := by
    have hraw := Stirling.log_stirlingSeq_diff_hasSum (n - 1)
    have hsub1 : (n - 1 + 1 : ℕ) = n := Nat.sub_add_cancel hn
    have hsub2 : (n - 1 + 2 : ℕ) = n + 1 := by omega
    simpa [f, stirlingLog, hsub1, hsub2] using hraw
  have hfirst : f 0 ≤ stirlingLog n - stirlingLog (n + 1) := by
    refine le_hasSum hsum 0 ?_
    intro j _hj
    positivity
  have hf0 : f 0 = 1 / (3 * (2 * (n : ℝ) + 1) ^ 2) := by
    have hsub1 : (n - 1 + 1 : ℕ) = n := Nat.sub_add_cancel hn
    unfold f
    rw [hsub1]
    norm_num
    field_simp
  simpa [hf0] using hfirst

private lemma stirlingLogCorrLower_step_le_first {n : ℕ} (hn : 1 ≤ n) :
    stirlingLogCorrLower n - stirlingLogCorrLower (n + 1) ≤
      1 / (3 * (2 * (n : ℝ) + 1) ^ 2) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hn1pos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have htwopos : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hn0 : n ≠ 0 := by omega
  have hdiff :
      1 / (12 * (n : ℝ) * ((n + 1 : ℕ) : ℝ)) -
          1 / (3 * (2 * (n : ℝ) + 1) ^ 2) =
        1 / (12 * (n : ℝ) * ((n + 1 : ℕ) : ℝ) *
          (2 * (n : ℝ) + 1) ^ 2) := by
    field_simp [hnpos.ne', hn1pos.ne', htwopos.ne']
    norm_num [Nat.cast_add]
    ring
  have hcube :
      1 / (12 * (n : ℝ) * ((n + 1 : ℕ) : ℝ) *
          (2 * (n : ℝ) + 1) ^ 2) ≤
        ((n : ℝ)⁻¹) ^ 3 - (((n + 1 : ℕ) : ℝ)⁻¹) ^ 3 := by
    field_simp [hnpos.ne', hn1pos.ne', htwopos.ne']
    norm_num [Nat.cast_add]
    nlinarith [sq_nonneg (n : ℝ), hnpos]
  unfold stirlingLogCorrLower
  rw [show stirlingLogCorr n - (n : ℝ)⁻¹ ^ 3 -
        (stirlingLogCorr (n + 1) - (((n + 1 : ℕ) : ℝ)⁻¹) ^ 3) =
      (stirlingLogCorr n - stirlingLogCorr (n + 1)) -
        (((n : ℝ)⁻¹) ^ 3 - (((n + 1 : ℕ) : ℝ)⁻¹) ^ 3) by ring]
  rw [stirlingLogCorr_sub_succ n hn0]
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
  rw [hdiff]
  exact hcube

private lemma stirlingLogCorrLower_step {n : ℕ} (hn : 1 ≤ n) :
    stirlingLogCorrLower n - stirlingLogCorrLower (n + 1) ≤
      stirlingLog n - stirlingLog (n + 1) := by
  exact le_trans (stirlingLogCorrLower_step_le_first hn)
    (stirlingLog_diff_first_term_le hn)

private lemma stirlingLogTail_upper_finite {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    stirlingLog n - stirlingLog m ≤ stirlingLogCorr n - stirlingLogCorr m := by
  induction m, hnm using Nat.le_induction with
  | base =>
      simp
  | succ m hnm ih =>
      have hm : 1 ≤ m := le_trans hn hnm
      have hstep := stirlingLog_diff_le_corr_diff hm
      calc
        stirlingLog n - stirlingLog (m + 1)
            = (stirlingLog n - stirlingLog m) +
                (stirlingLog m - stirlingLog (m + 1)) := by ring
        _ ≤ (stirlingLogCorr n - stirlingLogCorr m) +
              (stirlingLogCorr m - stirlingLogCorr (m + 1)) := by
                exact add_le_add ih hstep
        _ = stirlingLogCorr n - stirlingLogCorr (m + 1) := by ring

private lemma stirlingLogTail_lower_finite {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    stirlingLogCorrLower n - stirlingLogCorrLower m ≤
      stirlingLog n - stirlingLog m := by
  induction m, hnm using Nat.le_induction with
  | base =>
      simp
  | succ m hnm ih =>
      have hm : 1 ≤ m := le_trans hn hnm
      have hstep := stirlingLogCorrLower_step hm
      calc
        stirlingLogCorrLower n - stirlingLogCorrLower (m + 1)
            = (stirlingLogCorrLower n - stirlingLogCorrLower m) +
                (stirlingLogCorrLower m - stirlingLogCorrLower (m + 1)) := by ring
        _ ≤ (stirlingLog n - stirlingLog m) +
              (stirlingLog m - stirlingLog (m + 1)) := by
                exact add_le_add ih hstep
        _ = stirlingLog n - stirlingLog (m + 1) := by ring

private lemma stirlingLogTail_upper {n : ℕ} (hn : 1 ≤ n) :
    stirlingLogTail n ≤ stirlingLogCorr n := by
  have hleft : Tendsto (fun m : ℕ => stirlingLog n - stirlingLog m) atTop
      (𝓝 (stirlingLogTail n)) := by
    simpa [stirlingLogTail] using tendsto_const_nhds.sub stirlingLog_tendsto_log_sqrt_pi
  have hright : Tendsto (fun m : ℕ => stirlingLogCorr n - stirlingLogCorr m) atTop
      (𝓝 (stirlingLogCorr n)) := by
    simpa using tendsto_const_nhds.sub stirlingLogCorr_tendsto_zero
  exact le_of_tendsto_of_tendsto hleft hright
    (eventually_atTop.mpr ⟨n, fun m hm => stirlingLogTail_upper_finite hn hm⟩)

private lemma stirlingLogTail_lower {n : ℕ} (hn : 1 ≤ n) :
    stirlingLogCorrLower n ≤ stirlingLogTail n := by
  have hleft : Tendsto (fun m : ℕ => stirlingLogCorrLower n - stirlingLogCorrLower m)
      atTop (𝓝 (stirlingLogCorrLower n)) := by
    simpa using tendsto_const_nhds.sub stirlingLogCorrLower_tendsto_zero
  have hright : Tendsto (fun m : ℕ => stirlingLog n - stirlingLog m) atTop
      (𝓝 (stirlingLogTail n)) := by
    simpa [stirlingLogTail] using tendsto_const_nhds.sub stirlingLog_tendsto_log_sqrt_pi
  exact le_of_tendsto_of_tendsto hleft hright
    (eventually_atTop.mpr ⟨n, fun m hm => stirlingLogTail_lower_finite hn hm⟩)

private lemma inv_nat_sq_isBigO_inv :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) =O[atTop] fun n : ℕ => (n : ℝ)⁻¹ := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hinv_le_one : (n : ℝ)⁻¹ ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_le_one_of_one_le₀ hn1
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 2),
    Real.norm_of_nonneg hinv_nonneg]
  nlinarith [mul_le_mul_of_nonneg_right hinv_le_one hinv_nonneg]

private lemma inv_nat_cube_isLittleO_inv_sq :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) =o[atTop]
      fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine IsLittleO.of_bound ?_
  intro c hc
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ < c :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (Iio_mem_nhds hc)
  filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hninvc
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 3),
    Real.norm_of_nonneg (pow_nonneg hinv_nonneg 2)]
  calc
    ((n : ℝ)⁻¹) ^ 3 = (n : ℝ)⁻¹ * ((n : ℝ)⁻¹) ^ 2 := by ring
    _ ≤ c * ((n : ℝ)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_of_lt hninvc) (pow_nonneg hinv_nonneg 2)

theorem stirlingLogTail_thirdOrder :
    (fun n : ℕ => stirlingLogTail n - stirlingLogCorr n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hcube := inv_nat_cube_isLittleO_inv_sq
  rw [Asymptotics.isLittleO_iff] at hcube ⊢
  intro c hc
  have hcubec := hcube hc
  filter_upwards [eventually_ge_atTop 1, hcubec] with n hn hcubec_n
  have hupper := stirlingLogTail_upper hn
  have hlower := stirlingLogTail_lower hn
  have hnonpos : stirlingLogTail n - stirlingLogCorr n ≤ 0 := by linarith
  have hbound : stirlingLogCorr n - stirlingLogTail n ≤ ((n : ℝ)⁻¹) ^ 3 := by
    unfold stirlingLogCorrLower at hlower
    linarith
  calc
    ‖stirlingLogTail n - stirlingLogCorr n‖
        = stirlingLogCorr n - stirlingLogTail n := by
            rw [Real.norm_of_nonpos hnonpos]
            ring
    _ ≤ ((n : ℝ)⁻¹) ^ 3 := hbound
    _ = ‖((n : ℝ)⁻¹) ^ 3‖ := by
          rw [Real.norm_of_nonneg (by positivity)]
    _ ≤ c * ‖((n : ℝ)⁻¹) ^ 2‖ := hcubec_n

private lemma stirlingLogTail_tendsto_zero :
    Tendsto stirlingLogTail atTop (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ => Real.log (Real.sqrt Real.pi)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) := tendsto_const_nhds
  have h := stirlingLog_tendsto_log_sqrt_pi.sub hconst
  simpa [stirlingLogTail, sub_self] using h

private lemma stirlingLogCorr_isBigO_inv :
    stirlingLogCorr =O[atTop] fun n : ℕ => (n : ℝ)⁻¹ := by
  exact (isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop).const_mul_left (1 / 12 : ℝ)

private lemma stirlingLogTail_isBigO_inv :
    stirlingLogTail =O[atTop] fun n : ℕ => (n : ℝ)⁻¹ := by
  have hsmallO : (fun n : ℕ => stirlingLogTail n - stirlingLogCorr n)
      =O[atTop] fun n : ℕ => (n : ℝ)⁻¹ :=
    stirlingLogTail_thirdOrder.isBigO.trans inv_nat_sq_isBigO_inv
  have hsum := hsmallO.add stirlingLogCorr_isBigO_inv
  refine hsum.congr_left ?_
  intro n
  ring

private lemma neg_stirlingLogTail_sq_isBigO_inv_sq :
    (fun n : ℕ => (-stirlingLogTail n) ^ 2) =O[atTop]
      fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hxO : (fun n : ℕ => -stirlingLogTail n) =O[atTop]
      fun n : ℕ => (n : ℝ)⁻¹ := by
    refine (stirlingLogTail_isBigO_inv.const_mul_left (-1)).congr_left ?_
    intro n
    ring
  have hsq := hxO.mul hxO
  refine hsq.congr' ?_ ?_
  · exact Eventually.of_forall fun n => by ring
  · exact Eventually.of_forall fun n => by ring

private lemma exp_neg_stirlingLogTail_thirdOrder_corr :
    (fun n : ℕ =>
      Real.exp (-stirlingLogTail n) -
        (1 - stirlingLogCorr n + (stirlingLogCorr n) ^ 2 / 2))
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  let x : ℕ → ℝ := fun n => -stirlingLogTail n
  let a : ℕ → ℝ := fun n => -stirlingLogCorr n
  have hx0 : Tendsto x atTop (𝓝 0) := by
    simpa [x] using stirlingLogTail_tendsto_zero.neg
  have ha0 : Tendsto a atTop (𝓝 0) := by
    simpa [a] using stirlingLogCorr_tendsto_zero.neg
  have hremLocal :
      (fun n : ℕ => Real.exp (x n) - (1 + x n + (x n) ^ 2 / 2))
        =o[atTop] fun n : ℕ => (x n) ^ 2 := by
    have h := (Real.exp_sub_sum_range_succ_isLittleO_pow 2).comp_tendsto hx0
    simpa [Finset.sum_range_succ] using h
  have hrem :
      (fun n : ℕ => Real.exp (x n) - (1 + x n + (x n) ^ 2 / 2))
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 :=
    hremLocal.trans_isBigO neg_stirlingLogTail_sq_isBigO_inv_sq
  have hdiff :
      (fun n : ℕ => x n - a n) =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    have h := stirlingLogTail_thirdOrder.const_mul_left (-1)
    refine h.congr_left ?_
    intro n
    simp [x, a]
    ring
  have hplusO : (fun n : ℕ => x n + a n) =O[atTop] fun _n : ℕ => (1 : ℝ) := by
    exact (hx0.add ha0).isBigO_one ℝ
  have hprod :
      (fun n : ℕ => (x n - a n) * (x n + a n) / 2)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    have h := hdiff.mul_isBigO hplusO
    have h' : (fun n : ℕ => (x n - a n) * (x n + a n))
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
      refine h.congr_right ?_
      intro n
      ring
    exact (h'.const_mul_left (1 / 2 : ℝ)).congr_left fun n => by ring
  have hpoly :
      (fun n : ℕ =>
        (1 + x n + (x n) ^ 2 / 2) - (1 + a n + (a n) ^ 2 / 2))
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    have hsum := hdiff.add hprod
    refine hsum.congr_left ?_
    intro n
    ring
  have htotal := hrem.add hpoly
  refine htotal.congr_left ?_
  intro n
  simp [x, a]
  ring

private lemma exp_neg_stirlingLogTail_thirdOrder :
    (fun n : ℕ =>
      Real.exp (-stirlingLogTail n) -
        (1 + cayleyRelativeSecondConstant * (n : ℝ)⁻¹ +
          cayleyRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine exp_neg_stirlingLogTail_thirdOrder_corr.congr_left ?_
  intro n
  unfold stirlingLogCorr cayleyRelativeSecondConstant cayleyRelativeThirdConstant
  ring

private lemma exp_neg_stirlingLogTail_eq_ratio {n : ℕ} (hn : 0 < n) :
    Real.exp (-stirlingLogTail n) =
      Real.sqrt Real.pi / Stirling.stirlingSeq n := by
  have hS : 0 < Stirling.stirlingSeq n := stirlingSeq_pos_of_pos hn
  have hπ : 0 < Real.sqrt Real.pi := by positivity
  unfold stirlingLogTail stirlingLog
  rw [neg_sub, Real.exp_sub, Real.exp_log hπ, Real.exp_log hS]

theorem stirlingSeq_inv_ratio_thirdOrder :
    (fun n : ℕ =>
      Real.sqrt Real.pi / Stirling.stirlingSeq n -
        (1 + cayleyRelativeSecondConstant * (n : ℝ)⁻¹ +
          cayleyRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine exp_neg_stirlingLogTail_thirdOrder.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [exp_neg_stirlingLogTail_eq_ratio hn]

private lemma treeFunctionCoeff_ratio_eq_inv_stirling_ratio {n : ℕ} (hn : n ≠ 0) :
    treeFunctionCoeff n / cayleyMainTerm n =
      Real.sqrt Real.pi / Stirling.stirlingSeq n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hS : Stirling.stirlingSeq n ≠ 0 := (stirlingSeq_pos_of_pos (Nat.pos_of_ne_zero hn)).ne'
  have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrt2 : Real.sqrt (2 * (n : ℝ)) ≠ 0 := by positivity
  have hexp : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have hnpow : (n : ℝ) ^ n ≠ 0 := pow_ne_zero _ hnR
  have hpowNm1 : (n : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hnR
  have hfact : (n.factorial : ℝ) ≠ 0 := by positivity
  have hsqrt_main : Real.sqrt (2 * Real.pi) * (n : ℝ) ^ (3 / 2 : ℝ) ≠ 0 := by
    positivity
  have hfact_eq :
      (n.factorial : ℝ) =
        Stirling.stirlingSeq n *
          (Real.sqrt (2 * (n : ℝ)) * (((n : ℝ) / Real.exp 1) ^ n)) := by
    unfold Stirling.stirlingSeq
    field_simp [hsqrt2, hnpow, hexp]
  have hpow :
      (n : ℝ) ^ n = (n : ℝ) ^ (n - 1) * (n : ℝ) := by
    conv_lhs => rw [← Nat.sub_one_add_one hn]
    rw [pow_succ, Nat.sub_one_add_one hn]
  have hsqrt_split :
      Real.sqrt (2 * (n : ℝ)) =
        Real.sqrt 2 * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
  have hsqrt_pi_split :
      Real.sqrt (2 * Real.pi) =
        Real.sqrt 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
  have hrpow_three :
      Real.sqrt (n : ℝ) * (n : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    nth_rw 2 [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hnpos]
    norm_num
  unfold treeFunctionCoeff cayleyMainTerm
  rw [cayleyRootedTree_cast]
  rw [hfact_eq, div_pow, hpow, hsqrt_split, hsqrt_pi_split, Real.exp_one_pow]
  rw [show Real.exp (n : ℝ) = (Real.exp 1) ^ n by
    rw [exp_one_pow_nat_eq_exp_nat]]
  field_simp [hnR, hS, hπ, hsqrt2, hexp, hnpow, hpowNm1, hfact, hsqrt_main]
  rw [← hrpow_three]

theorem treeFunctionCoeff_relative_thirdOrder :
    (fun n : ℕ =>
      treeFunctionCoeff n / cayleyMainTerm n -
        (1 + cayleyRelativeSecondConstant * (n : ℝ)⁻¹ +
          cayleyRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine stirlingSeq_inv_ratio_thirdOrder.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [treeFunctionCoeff_ratio_eq_inv_stirling_ratio hn0]

theorem cayleyRootedTree_over_factorial_relative_thirdOrder :
    (fun n : ℕ =>
      ((cayleyRootedTree n : ℝ) / n.factorial) / cayleyMainTerm n -
        (1 + cayleyRelativeSecondConstant * (n : ℝ)⁻¹ +
          cayleyRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  simpa [treeFunctionCoeff] using treeFunctionCoeff_relative_thirdOrder

end

end AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS
