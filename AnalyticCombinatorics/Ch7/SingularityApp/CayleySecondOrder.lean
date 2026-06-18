import AnalyticCombinatorics.Ch7.SingularityApp.TreeFunction
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Second-order Cayley tree-function coefficient asymptotic

This file proves the second relative coefficient for

`treeFunctionCoeff n = n^(n-1) / n!`.

The proof uses Stirling's sequence.  Robbins' stepwise upper bound and the
first positive term in Mathlib's exact series for
`log (stirlingSeq n) - log (stirlingSeq (n+1))` squeeze

`log (stirlingSeq n / sqrt pi) = 1/(12n) + o(1/n)`.

Exponentiating and inverting gives the Cayley correction `c = -1/12`.
-/

open Filter Asymptotics
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

noncomputable section

def cayleyRelativeSecondConstant : ℝ :=
  -(1 / 12 : ℝ)

def cayleyMainTerm (n : ℕ) : ℝ :=
  Real.exp (n : ℝ) /
    (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))

def cayleySecondOrderApprox (n : ℕ) : ℝ :=
  cayleyMainTerm n * (1 + cayleyRelativeSecondConstant * (n : ℝ)⁻¹)

private def stirlingLog (n : ℕ) : ℝ :=
  Real.log (Stirling.stirlingSeq n)

private def stirlingLogTail (n : ℕ) : ℝ :=
  stirlingLog n - Real.log (Real.sqrt Real.pi)

private def stirlingLogCorr (n : ℕ) : ℝ :=
  (1 / 12 : ℝ) * (n : ℝ)⁻¹

lemma cayleyRelativeSecondConstant_eq :
    cayleyRelativeSecondConstant = -(1 / 12 : ℝ) := rfl

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

private lemma stirlingLogCorr_sub_succ (n : ℕ) (hn : n ≠ 0) :
    stirlingLogCorr n - stirlingLogCorr (n + 1) =
      1 / (12 * (n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn1R : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold stirlingLogCorr
  field_simp [hnR, hn1R]
  norm_num [Nat.cast_add]

private lemma stirlingLogCorr_succ_sub_succ_succ (n : ℕ) :
    stirlingLogCorr (n + 1) - stirlingLogCorr (n + 2) =
      1 / (12 * ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by
  have hn1 : n + 1 ≠ 0 := by omega
  simpa [Nat.add_assoc] using stirlingLogCorr_sub_succ (n + 1) hn1

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

private lemma stirlingLogCorr_lower_step {n : ℕ} (hn : 1 ≤ n) :
    stirlingLogCorr (n + 1) - stirlingLogCorr (n + 2) ≤
      stirlingLog n - stirlingLog (n + 1) := by
  have hfirst := stirlingLog_diff_first_term_le hn
  have hcmp :
      stirlingLogCorr (n + 1) - stirlingLogCorr (n + 2) ≤
        1 / (3 * (2 * (n : ℝ) + 1) ^ 2) := by
    rw [stirlingLogCorr_succ_sub_succ_succ n]
    have hden1 : 0 < 12 * ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) := by positivity
    have hden2 : 0 < 3 * (2 * (n : ℝ) + 1) ^ 2 := by positivity
    rw [one_div_le_one_div hden1 hden2]
    norm_num [Nat.cast_add]
    nlinarith [sq_nonneg (2 * (n : ℝ) + 1)]
  exact le_trans hcmp hfirst

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
    stirlingLogCorr (n + 1) - stirlingLogCorr (m + 1) ≤
      stirlingLog n - stirlingLog m := by
  induction m, hnm using Nat.le_induction with
  | base =>
      simp
  | succ m hnm ih =>
      have hm : 1 ≤ m := le_trans hn hnm
      have hstep := stirlingLogCorr_lower_step hm
      calc
        stirlingLogCorr (n + 1) - stirlingLogCorr (m + 2)
            = (stirlingLogCorr (n + 1) - stirlingLogCorr (m + 1)) +
                (stirlingLogCorr (m + 1) - stirlingLogCorr (m + 2)) := by ring
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
    stirlingLogCorr (n + 1) ≤ stirlingLogTail n := by
  have hleft : Tendsto (fun m : ℕ => stirlingLogCorr (n + 1) - stirlingLogCorr (m + 1))
      atTop (𝓝 (stirlingLogCorr (n + 1))) := by
    have hshift : Tendsto (fun m : ℕ => stirlingLogCorr (m + 1)) atTop (𝓝 0) :=
      stirlingLogCorr_tendsto_zero.comp (tendsto_add_atTop_nat 1)
    simpa using tendsto_const_nhds.sub hshift
  have hright : Tendsto (fun m : ℕ => stirlingLog n - stirlingLog m) atTop
      (𝓝 (stirlingLogTail n)) := by
    simpa [stirlingLogTail] using tendsto_const_nhds.sub stirlingLog_tendsto_log_sqrt_pi
  exact le_of_tendsto_of_tendsto hleft hright
    (eventually_atTop.mpr ⟨n, fun m hm => stirlingLogTail_lower_finite hn hm⟩)

private lemma stirlingLogCorr_diff_isLittleO_inv :
    (fun n : ℕ => stirlingLogCorr n - stirlingLogCorr (n + 1))
      =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  rw [Asymptotics.isLittleO_iff_tendsto' ?_]
  · have hratio :
        (fun n : ℕ =>
          (stirlingLogCorr n - stirlingLogCorr (n + 1)) / (n : ℝ)⁻¹)
          =ᶠ[atTop] fun n : ℕ => (1 / 12 : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹ := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have hn0 : n ≠ 0 := Nat.ne_of_gt hn
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
        have hn1R : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        rw [stirlingLogCorr_sub_succ n hn0]
        field_simp [hnR, hn1R]
    have hlim :
        Tendsto (fun n : ℕ => (1 / 12 : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
      have h :=
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      simpa using h.const_mul (1 / 12 : ℝ)
    exact hlim.congr' hratio.symm
  · filter_upwards [eventually_gt_atTop 0] with n hn hzero
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    exact (hnR (inv_eq_zero.mp hzero)).elim

theorem stirlingLogTail_secondOrder :
    (fun n : ℕ => stirlingLogTail n - stirlingLogCorr n)
      =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  have hdiff := stirlingLogCorr_diff_isLittleO_inv
  rw [Asymptotics.isLittleO_iff] at hdiff ⊢
  intro c hc
  have hcorr := hdiff hc
  filter_upwards [eventually_ge_atTop 1, hcorr] with n hn hcorrn
  have hupper := stirlingLogTail_upper hn
  have hlower := stirlingLogTail_lower hn
  have hnonpos : stirlingLogTail n - stirlingLogCorr n ≤ 0 := by linarith
  calc
    ‖stirlingLogTail n - stirlingLogCorr n‖
        = stirlingLogCorr n - stirlingLogTail n := by
            rw [Real.norm_of_nonpos hnonpos]
            ring
    _ ≤ stirlingLogCorr n - stirlingLogCorr (n + 1) := by linarith
    _ ≤ ‖stirlingLogCorr n - stirlingLogCorr (n + 1)‖ := le_abs_self _
    _ ≤ c * ‖(n : ℝ)⁻¹‖ := hcorrn

private lemma stirlingLogTail_tendsto_zero :
    Tendsto stirlingLogTail atTop (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ => Real.log (Real.sqrt Real.pi)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) := tendsto_const_nhds
  have h := stirlingLog_tendsto_log_sqrt_pi.sub hconst
  simpa [stirlingLogTail, sub_self] using h

private lemma stirlingLogCorr_isBigO_inv :
    stirlingLogCorr =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  exact (isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop).const_mul_left (1 / 12 : ℝ)

private lemma stirlingLogTail_isBigO_inv :
    stirlingLogTail =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  have hsmall := stirlingLogTail_secondOrder.isBigO
  have hsum := hsmall.add stirlingLogCorr_isBigO_inv
  refine hsum.congr_left ?_
  intro n
  ring

private lemma exp_stirlingLogTail_secondOrder :
    (fun n : ℕ => Real.exp (stirlingLogTail n) - (1 + stirlingLogCorr n))
      =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  have hlinear := stirlingLogTail_secondOrder
  have hquad :
      (fun n : ℕ => Real.exp (stirlingLogTail n) - 1 - stirlingLogTail n)
        =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have htail0 : ∀ᶠ n in atTop, ‖stirlingLogTail n‖ ≤ 1 := by
      simpa using
        (stirlingLogTail_tendsto_zero.norm.eventually_le_const
          (by norm_num : ‖(0 : ℝ)‖ < 1))
    have htailO := stirlingLogTail_isBigO_inv
    rw [Asymptotics.isBigO_iff] at htailO
    rcases htailO with ⟨C, hC⟩
    have hCpos : 0 < max C 1 := lt_max_of_lt_right zero_lt_one
    have hsmall :
        ∀ᶠ n : ℕ in atTop, (max C 1) * ‖(n : ℝ)⁻¹‖ ≤ c / (max C 1) := by
      have htend :
          Tendsto (fun n : ℕ => (max C 1) * ‖(n : ℝ)⁻¹‖) atTop (𝓝 0) := by
        have hinv : Tendsto (fun n : ℕ => ‖(n : ℝ)⁻¹‖) atTop (𝓝 0) := by
          simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).norm
        simpa using hinv.const_mul (max C 1)
      exact htend.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < c / max C 1))
    filter_upwards [htail0, hC, hsmall] with n hnorm1 hO hsmalln
    have hquadn :
        ‖Real.exp (stirlingLogTail n) - 1 - stirlingLogTail n‖ ≤
          ‖stirlingLogTail n‖ ^ 2 :=
      Real.norm_exp_sub_one_sub_id_le hnorm1
    have hO' : ‖stirlingLogTail n‖ ≤ max C 1 * ‖(n : ℝ)⁻¹‖ := by
      exact hO.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg _))
    calc
      ‖Real.exp (stirlingLogTail n) - 1 - stirlingLogTail n‖
          ≤ ‖stirlingLogTail n‖ ^ 2 := hquadn
      _ ≤ ‖stirlingLogTail n‖ * ((max C 1) * ‖(n : ℝ)⁻¹‖) := by
            rw [pow_two]
            exact mul_le_mul_of_nonneg_left hO' (norm_nonneg _)
      _ ≤ ((max C 1) * ‖(n : ℝ)⁻¹‖) *
            ((max C 1) * ‖(n : ℝ)⁻¹‖) := by
            exact mul_le_mul_of_nonneg_right hO' (by positivity)
      _ ≤ (c / max C 1) * ((max C 1) * ‖(n : ℝ)⁻¹‖) := by
            exact mul_le_mul_of_nonneg_right hsmalln (by positivity)
      _ = c * ‖(n : ℝ)⁻¹‖ := by
            field_simp [ne_of_gt hCpos]
  have hsum := hquad.add hlinear
  refine hsum.congr_left ?_
  intro n
  ring

private lemma exp_stirlingLogTail_eq_ratio {n : ℕ} (hn : 0 < n) :
    Real.exp (stirlingLogTail n) =
      Stirling.stirlingSeq n / Real.sqrt Real.pi := by
  have hS : 0 < Stirling.stirlingSeq n := stirlingSeq_pos_of_pos hn
  have hπ : 0 < Real.sqrt Real.pi := by positivity
  unfold stirlingLogTail stirlingLog
  rw [Real.exp_sub, Real.exp_log hS, Real.exp_log hπ]

theorem stirlingSeq_ratio_secondOrder :
    (fun n : ℕ =>
      Stirling.stirlingSeq n / Real.sqrt Real.pi - (1 + stirlingLogCorr n))
      =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  refine exp_stirlingLogTail_secondOrder.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [exp_stirlingLogTail_eq_ratio hn]

private lemma inv_ratio_secondOrder :
    (fun n : ℕ =>
      (Real.sqrt Real.pi / Stirling.stirlingSeq n) -
        (1 - stirlingLogCorr n))
      =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  let r : ℕ → ℝ := fun n => Stirling.stirlingSeq n / Real.sqrt Real.pi
  let e : ℕ → ℝ := fun n => r n - (1 + stirlingLogCorr n)
  have he : e =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
    simpa [e, r] using stirlingSeq_ratio_secondOrder
  have hcorr0 : Tendsto stirlingLogCorr atTop (𝓝 0) := stirlingLogCorr_tendsto_zero
  have hr : Tendsto r atTop (𝓝 1) := by
    have hs : Tendsto (fun n : ℕ => Stirling.stirlingSeq n / Real.sqrt Real.pi)
        atTop (𝓝 (Real.sqrt Real.pi / Real.sqrt Real.pi)) :=
      Stirling.tendsto_stirlingSeq_sqrt_pi.div tendsto_const_nhds (by positivity)
    convert hs using 1
    field_simp [show Real.sqrt Real.pi ≠ 0 by positivity]
  have hden : ∀ᶠ n in atTop, r n ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hs : Stirling.stirlingSeq n ≠ 0 := (stirlingSeq_pos_of_pos hn).ne'
    have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
    exact div_ne_zero hs hπ
  have hprod :
      (fun n : ℕ =>
        (stirlingLogCorr n * stirlingLogCorr n +
            stirlingLogCorr n * e n - e n) / r n)
        =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
    have hinvr : Tendsto (fun n : ℕ => (r n)⁻¹) atTop (𝓝 1) := by
      have h := hr.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
      simpa using h
    have hinvrO : (fun n : ℕ => (r n)⁻¹) =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
      hinvr.isBigO_one ℝ
    have hdiv : (fun n : ℕ => e n / r n)
        =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
      simpa [div_eq_mul_inv, one_mul] using he.mul_isBigO hinvrO
    have hcorrBigO : stirlingLogCorr =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
      hcorr0.isBigO_one ℝ
    have hcorrSmall : stirlingLogCorr =o[atTop] (fun _ : ℕ => (1 : ℝ)) :=
      (isLittleO_one_iff ℝ).mpr hcorr0
    have hprodSmall : (fun n : ℕ => stirlingLogCorr n * (e n / r n))
        =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) :=
      (hcorrBigO.mul_isLittleO hdiv).congr_right fun n => by ring
    have hcorrSq : (fun n : ℕ => stirlingLogCorr n * stirlingLogCorr n)
        =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) :=
      (stirlingLogCorr_isBigO_inv.mul_isLittleO hcorrSmall).congr_right fun n => by ring
    have hcorrSqDiv : (fun n : ℕ => stirlingLogCorr n * stirlingLogCorr n / r n)
        =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
      simpa [div_eq_mul_inv, one_mul] using hcorrSq.mul_isBigO hinvrO
    have hprodSmallDiv : (fun n : ℕ => stirlingLogCorr n * e n / r n)
        =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
      exact hprodSmall.congr_left fun n => by ring
    have hdivNeg : (fun n : ℕ => -(e n / r n))
        =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
      exact (hdiv.const_mul_left (-1)).congr_left fun n => by ring
    have hsum := (hcorrSqDiv.add hprodSmallDiv).add hdivNeg
    refine hsum.congr_left ?_
    intro n
    ring
  refine hprod.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [hden] with n hdenn
  have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hS : Stirling.stirlingSeq n ≠ 0 := by
    intro hzero
    apply hdenn
    dsimp [r]
    simp [hzero]
  dsimp [e, r]
  field_simp [hdenn, hπ, hS]
  ring

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
  field_simp [hnR, hS, hπ, hsqrt2, hexp, hnpow, hpowNm1, hsqrt_main]
  rw [← hrpow_three]

theorem treeFunctionCoeff_relative_secondOrder :
    (fun n : ℕ =>
      treeFunctionCoeff n / cayleyMainTerm n -
        (1 + cayleyRelativeSecondConstant * (n : ℝ)⁻¹))
      =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  refine inv_ratio_secondOrder.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [treeFunctionCoeff_ratio_eq_inv_stirling_ratio hn0]
  unfold cayleyRelativeSecondConstant stirlingLogCorr
  ring

theorem cayleyRootedTree_over_factorial_relative_secondOrder :
    (fun n : ℕ =>
      ((cayleyRootedTree n : ℝ) / n.factorial) / cayleyMainTerm n -
        (1 + cayleyRelativeSecondConstant * (n : ℝ)⁻¹))
      =o[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  simpa [treeFunctionCoeff] using treeFunctionCoeff_relative_secondOrder

end

end AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS
