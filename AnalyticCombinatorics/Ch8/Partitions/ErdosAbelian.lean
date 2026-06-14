import AnalyticCombinatorics.Ch8.Partitions.ErdosConstant
import AnalyticCombinatorics.Ch8.Partitions.ErdosRenewalConnect

/-!
# Brick 3: Abelian comparison `P(e^{-t}) ~ a · modelSaddle` (HR constant)

From `u_n → a` (Erdős limit) and the global bound `u_abs_le`, the weighted sum
`∑ u_n w_n(t)` is Abelian-comparable to `a · ∑ w_n(t) = a · modelSaddle t`, where
`w_n(t) = e^{C√n − tn}/n`. Since `P = 1 + ∑ u_n w_n` and `modelSaddle → ∞`, this gives
`log P − log a − log modelSaddle → 0` (taking `modelSaddle → ∞` as a brick-4 hypothesis).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators
open scoped Topology BigOperators
open AnalyticCombinatorics.Ch8.Partitions.Erdos

noncomputable section

/-- The model weight `w_n(t) = e^{C√n−tn}/n`; `n=0` value is `0`. -/
noncomputable def modelWeight (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ)

/-- Weighted sum `∑ u_n w_n(t)`. -/
noncomputable def weightedU (t : ℝ) : ℝ :=
  ∑' n : ℕ, u n * modelWeight t n

lemma modelWeight_nonneg (t : ℝ) (n : ℕ) : 0 ≤ modelWeight t n := by
  unfold modelWeight; positivity

lemma summable_modelWeight {t : ℝ} (ht : 0 < t) : Summable (modelWeight t) := by
  simpa [modelWeight] using summable_modelSaddleTerm ht

lemma modelSaddle_eq_tsum_modelWeight (t : ℝ) :
    modelSaddle t = ∑' n : ℕ, modelWeight t n := rfl

lemma summable_weightedU {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => u n * modelWeight t n) := by
  obtain ⟨Mu, hMu0, hMu⟩ := u_abs_le
  have hs : Summable (fun n : ℕ => Mu * modelWeight t n) :=
    (summable_modelWeight (t := t) ht).mul_left Mu
  refine hs.of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  have hw : 0 ≤ modelWeight t n := modelWeight_nonneg t n
  rw [abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_right (hMu n) hw

lemma weightedU_term_eq_partLaplace_term {t : ℝ} {n : ℕ} (hn : n ≠ 0) :
    u n * modelWeight t n = part n * Real.exp (-(t * n)) := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  unfold u modelWeight
  field_simp
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring

lemma partLaplace_pos' {t : ℝ} (ht : 0 < t) : 0 < PartLaplace t := by
  unfold PartLaplace
  have hs := partLaplace_summable (t := t) ht
  have hnonneg : ∀ n : ℕ, 0 ≤ part n * Real.exp (-(t * n)) := fun n =>
    mul_nonneg (part_pos n).le (Real.exp_pos _).le
  have h0 : 0 < part 0 * Real.exp (-(t * (0 : ℕ))) := by
    simpa using mul_pos (part_pos 0) (Real.exp_pos (-(t * (0 : ℕ))))
  simpa using hs.tsum_pos hnonneg 0 h0

lemma partLaplace_eq_one_add_weightedU {t : ℝ} (ht : 0 < t) :
    PartLaplace t = 1 + weightedU t := by
  unfold PartLaplace weightedU
  have hp := partLaplace_summable (t := t) ht
  have hw := summable_weightedU (t := t) ht
  rw [hp.tsum_eq_zero_add, hw.tsum_eq_zero_add]
  have h0w : u 0 * modelWeight t 0 = 0 := by unfold u modelWeight; norm_num
  rw [h0w]
  have htail :
      (∑' n : ℕ, part (n + 1) * Real.exp (-(t * ((n + 1 : ℕ) : ℝ))))
        = ∑' n : ℕ, u (n + 1) * modelWeight t (n + 1) := by
    refine tsum_congr (fun n => ?_)
    rw [weightedU_term_eq_partLaplace_term (t := t) (n := n + 1) (by omega)]
  rw [htail]
  have hpart0 : part 0 * Real.exp (-(t * (0 : ℕ))) = 1 := by rw [part_zero]; norm_num
  rw [hpart0]; ring

/-- Finite head of model mass is negligible vs the (diverging) total. -/
lemma finite_modelWeight_head_div_tendsto_zero (N : ℕ)
    (hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (fun t : ℝ => (∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  set K : ℝ := ∑ n ∈ Finset.range N, Real.exp (C * Real.sqrt (n : ℝ)) / (n : ℝ) with hK
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ‖∑ n ∈ Finset.range N, modelWeight t n‖ ≤ K := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : (0 : ℝ) < t := ht
    have hnonneg_sum : 0 ≤ ∑ n ∈ Finset.range N, modelWeight t n :=
      Finset.sum_nonneg (fun n _ => modelWeight_nonneg t n)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg_sum, hK]
    refine Finset.sum_le_sum (fun n _ => ?_)
    unfold modelWeight
    rcases Nat.eq_zero_or_pos n with h0 | hnpos_nat
    · subst h0; simp
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
      have hexp_le : Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ))
          ≤ Real.exp (C * Real.sqrt (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [htpos.le, (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
      rw [div_eq_inv_mul, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
  have hK_div : Tendsto (fun t : ℝ => K / modelSaddle t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hMS_atTop
  have hft : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ‖(∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t‖ ≤ K / modelSaddle t := by
    filter_upwards [hbound, self_mem_nhdsWithin] with t hb ht
    have htpos : (0 : ℝ) < t := ht
    have hMSpos : 0 < modelSaddle t := modelSaddle_pos htpos
    have hb' : |∑ n ∈ Finset.range N, modelWeight t n| ≤ K := by rwa [Real.norm_eq_abs] at hb
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hMSpos]
    gcongr
  have hzero := squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) hft hK_div
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hzero

/-- Abelian ratio: `(∑ u_n w_n)/modelSaddle → a`. -/
lemma weightedU_div_modelSaddle_tendsto {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto u atTop (𝓝 a))
    (hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (fun t : ℝ => weightedU t / modelSaddle t) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hdiff : Tendsto
      (fun t : ℝ => (weightedU t - a * modelSaddle t) / modelSaddle t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    have hε4 : 0 < ε / 4 := by positivity
    have htail_event : ∀ᶠ n : ℕ in atTop, |u n - a| ≤ ε / 4 := by
      have hmetric := (Metric.tendsto_nhds.mp hlim) (ε / 4) hε4
      filter_upwards [hmetric] with n hn
      simpa [dist_eq_norm, Real.norm_eq_abs] using le_of_lt hn
    obtain ⟨N, hN⟩ := eventually_atTop.1 htail_event
    obtain ⟨Mu, hMu0, hMu⟩ := u_abs_le
    set B : ℝ := Mu + a with hB
    have hB0 : 0 ≤ B := by rw [hB]; linarith [hMu0, ha.le]
    have hhead0 := finite_modelWeight_head_div_tendsto_zero N hMS_atTop
    have hhead_small : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        B * ((∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t) ≤ ε / 2 := by
      have hmul : Tendsto
          (fun t : ℝ => B * ((∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using hhead0.const_mul B
      exact hmul.eventually_le_const hε2
    filter_upwards [self_mem_nhdsWithin, hhead_small] with t ht hhead_le
    have ht : 0 < t := ht
    have hWpos : 0 < modelSaddle t := modelSaddle_pos ht
    have hsW := summable_modelWeight (t := t) ht
    have hsu := summable_weightedU (t := t) ht
    have hsaw : Summable (fun n : ℕ => a * modelWeight t n) := hsW.mul_left a
    have hdiff_eq : weightedU t - a * modelSaddle t
        = ∑' n : ℕ, (u n - a) * modelWeight t n := by
      unfold weightedU
      rw [modelSaddle_eq_tsum_modelWeight, ← tsum_mul_left, ← hsu.tsum_sub hsaw]
      refine tsum_congr (fun n => ?_); ring
    have habs_summ : Summable (fun n : ℕ => |(u n - a) * modelWeight t n|) := by
      refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_
        ((summable_modelWeight (t := t) ht).mul_left B)
      intro n
      rw [abs_mul]
      have hw : 0 ≤ modelWeight t n := modelWeight_nonneg t n
      rw [abs_of_nonneg hw]
      have hu : |u n - a| ≤ B := by
        calc |u n - a| ≤ |u n| + |a| := abs_sub _ _
          _ ≤ Mu + a := by rw [abs_of_pos ha]; exact add_le_add (hMu n) le_rfl
      exact mul_le_mul_of_nonneg_right hu hw
    have habs_tsum : |∑' n : ℕ, (u n - a) * modelWeight t n|
        ≤ ∑' n : ℕ, |(u n - a) * modelWeight t n| := by
      have h2 : Summable (fun n : ℕ => ‖(u n - a) * modelWeight t n‖) := by
        simpa [Real.norm_eq_abs] using habs_summ
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm h2
    have hsplit_abs := Summable.sum_add_tsum_nat_add N habs_summ
    have hhead_bound : (∑ n ∈ Finset.range N, |(u n - a) * modelWeight t n|)
        ≤ B * ∑ n ∈ Finset.range N, modelWeight t n := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun n _ => ?_)
      rw [abs_mul]
      have hw : 0 ≤ modelWeight t n := modelWeight_nonneg t n
      rw [abs_of_nonneg hw]
      have hu : |u n - a| ≤ B := by
        calc |u n - a| ≤ |u n| + |a| := abs_sub _ _
          _ ≤ Mu + a := by rw [abs_of_pos ha]; exact add_le_add (hMu n) le_rfl
      exact mul_le_mul_of_nonneg_right hu hw
    have htail_summ : Summable (fun k : ℕ => modelWeight t (k + N)) :=
      (summable_nat_add_iff N).mpr (summable_modelWeight (t := t) ht)
    have htail_bound : (∑' k : ℕ, |(u (k + N) - a) * modelWeight t (k + N)|)
        ≤ (ε / 4) * (∑' k : ℕ, modelWeight t (k + N)) := by
      rw [← tsum_mul_left]
      apply Summable.tsum_le_tsum
      · intro k
        rw [abs_mul]
        have hw : 0 ≤ modelWeight t (k + N) := modelWeight_nonneg t (k + N)
        rw [abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_right (hN (k + N) (by omega)) hw
      · exact habs_summ.comp_injective (fun i j hij => by omega)
      · exact htail_summ.mul_left (ε / 4)
    have htail_weight_le_total : (∑' k : ℕ, modelWeight t (k + N)) ≤ modelSaddle t := by
      have hadd := Summable.sum_add_tsum_nat_add N (summable_modelWeight (t := t) ht)
      have hcomm : (∑' k : ℕ, modelWeight t (k + N)) = ∑' k : ℕ, modelWeight t (N + k) := by
        refine tsum_congr (fun k => ?_); rw [add_comm]
      rw [hcomm, modelSaddle_eq_tsum_modelWeight]
      have hfin_nonneg : 0 ≤ ∑ n ∈ Finset.range N, modelWeight t n :=
        Finset.sum_nonneg (fun n _ => modelWeight_nonneg t n)
      linarith [hadd]
    have htotal_abs : (∑' n : ℕ, |(u n - a) * modelWeight t n|)
        ≤ B * (∑ n ∈ Finset.range N, modelWeight t n) + (ε / 4) * modelSaddle t := by
      calc (∑' n : ℕ, |(u n - a) * modelWeight t n|)
          = (∑ n ∈ Finset.range N, |(u n - a) * modelWeight t n|)
            + ∑' k : ℕ, |(u (k + N) - a) * modelWeight t (k + N)| := hsplit_abs.symm
        _ ≤ B * (∑ n ∈ Finset.range N, modelWeight t n)
            + (ε / 4) * (∑' k : ℕ, modelWeight t (k + N)) := add_le_add hhead_bound htail_bound
        _ ≤ B * (∑ n ∈ Finset.range N, modelWeight t n) + (ε / 4) * modelSaddle t := by
            gcongr
    have hratio_bound : |(weightedU t - a * modelSaddle t) / modelSaddle t| < ε := by
      rw [abs_div, abs_of_pos hWpos]
      calc |weightedU t - a * modelSaddle t| / modelSaddle t
          ≤ (∑' n : ℕ, |(u n - a) * modelWeight t n|) / modelSaddle t := by
            rw [hdiff_eq]; exact div_le_div_of_nonneg_right habs_tsum hWpos.le
        _ ≤ (B * (∑ n ∈ Finset.range N, modelWeight t n) + (ε / 4) * modelSaddle t)
              / modelSaddle t := div_le_div_of_nonneg_right htotal_abs hWpos.le
        _ = B * ((∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t) + ε / 4 := by
            field_simp [hWpos.ne']
        _ ≤ ε / 2 + ε / 4 := add_le_add hhead_le le_rfl
        _ < ε := by linarith
    rw [dist_eq_norm, Real.norm_eq_abs, sub_zero]
    exact hratio_bound
  refine hdiff.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hWpos : modelSaddle t ≠ 0 := (modelSaddle_pos ht).ne'
  field_simp [hWpos]

/-- **Brick 3.** `log P(e^{-t}) − log a − log(modelSaddle t) → 0` (given `modelSaddle → ∞`). -/
theorem partLaplace_log_sub_modelSaddle_tendsto {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto u atTop (𝓝 a))
    (hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (fun t : ℝ => Real.log (PartLaplace t) - Real.log a - Real.log (modelSaddle t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hW := weightedU_div_modelSaddle_tendsto ha hlim hMS_atTop
  have hInvW : Tendsto (fun t : ℝ => 1 / modelSaddle t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hMS_atTop
  have hratioP : Tendsto (fun t : ℝ => PartLaplace t / (a * modelSaddle t))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hsum : Tendsto (fun t : ℝ => 1 / modelSaddle t + weightedU t / modelSaddle t)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 + a)) := hInvW.add hW
    have hscaled := hsum.const_mul (1 / a)
    have htarget : Tendsto
        (fun t : ℝ => 1 / a * (1 / modelSaddle t + weightedU t / modelSaddle t))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by simpa [ha.ne'] using hscaled
    refine htarget.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hWpos : modelSaddle t ≠ 0 := (modelSaddle_pos ht).ne'
    rw [partLaplace_eq_one_add_weightedU ht]
    field_simp [ha.ne', hWpos]
  have hlog : Tendsto (fun t : ℝ => Real.log (PartLaplace t / (a * modelSaddle t)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
    simpa using hcont.comp hratioP
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hPpos : 0 < PartLaplace t := partLaplace_pos' ht
  have hWpos : 0 < modelSaddle t := modelSaddle_pos ht
  rw [Real.log_div hPpos.ne' (mul_ne_zero ha.ne' hWpos.ne'), Real.log_mul ha.ne' hWpos.ne']
  ring

end

end AnalyticCombinatorics.Ch8.Partitions
