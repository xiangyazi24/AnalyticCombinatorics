═══ BRIDGE ac | 693e0774 | 20003 chars 3242 words 555 lines | 358s | prov=network | OK ═══
═══ BRIDGE ac | 693e0774 | 20003 chars 3242 words 555 lines | 358s | prov=network | OK ═══
First, a source-detail correction: at commit `13d6af3`, `modelSaddle` is **not** in the `Erdos` namespace; it is defined in `AnalyticCombinatorics.Ch8.Partitions`, with `Erdos` only opened for `C`. The definition is
```lean
noncomputable def modelSaddle (t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ)
```
so the `n = 0` summand is totalized as `0`. fileciteturn158file0L54-L57 The repo also already has `summable_modelSaddleTerm` and `modelSaddle_pos` for `t > 0`. fileciteturn158file0L67-L97

The cleanest proof is exactly as you suggest: prove the **ratio form** first, then take logs. I would **take**
```lean
(hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop)
```
as a hypothesis of this brick. It follows from brick 4, and keeping it as a hypothesis makes brick 3 independent of the saddle proof.

Below is the Lean decomposition I recommend. It avoids proving `modelSaddle_tendsto_atTop` inside this brick.

## Imports and helper definitions

```lean
import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.ErdosRenewalConnect
import AnalyticCombinatorics.Ch8.Partitions.ErdosConstant

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators
open scoped Topology BigOperators
open AnalyticCombinatorics.Ch8.Partitions.Erdos

noncomputable section

/-- The model weight `w_n(t) = e^{C√n-tn}/n`; the `n=0` value is `0`. -/
noncomputable def modelWeight (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ)

/-- Weighted sum `∑ u_n w_n(t)`. -/
noncomputable def weightedU (t : ℝ) : ℝ :=
  ∑' n : ℕ, u n * modelWeight t n
```

## Basic positivity/summability

```lean
lemma modelWeight_nonneg (t : ℝ) (n : ℕ) :
    0 ≤ modelWeight t n := by
  unfold modelWeight
  positivity

lemma summable_modelWeight {t : ℝ} (ht : 0 < t) :
    Summable (modelWeight t) := by
  simpa [modelWeight] using summable_modelSaddleTerm (t := t) ht

lemma modelSaddle_eq_tsum_modelWeight (t : ℝ) :
    modelSaddle t = ∑' n : ℕ, modelWeight t n := by
  rfl

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
```

`u_abs_le` and `u_nonneg` are currently in `ErdosRenewalConnect.lean`; `u_abs_le` gives a global bound on `|u n|`. fileciteturn160file0L7-L22

## `PartLaplace = 1 + weightedU`

```lean
lemma part_zero_eq_one : part 0 = 1 := by
  unfold part
  norm_num
  -- If `norm_num` does not close the `Nat.Partition 0` cardinality in your env,
  -- replace this with the existing `part_pos` plus a direct `Fintype.card_eq_one`
  -- for the unique empty partition.

lemma partLaplace_pos {t : ℝ} (ht : 0 < t) :
    0 < PartLaplace t := by
  unfold PartLaplace
  have hs := partLaplace_summable (t := t) ht
  have hnonneg : ∀ n : ℕ, 0 ≤ part n * Real.exp (-(t * n)) := by
    intro n
    exact mul_nonneg (part_pos n).le (Real.exp_pos _).le
  have h0 : 0 < part 0 * Real.exp (-(t * (0 : ℕ))) := by
    simpa using mul_pos (part_pos 0) (Real.exp_pos (-(t * (0 : ℕ))))
  simpa using hs.tsum_pos hnonneg 0 h0

lemma weightedU_term_eq_partLaplace_term {t : ℝ} {n : ℕ} (hn : n ≠ 0) :
    u n * modelWeight t n = part n * Real.exp (-(t * n)) := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  unfold u modelWeight
  field_simp [hnpos.ne']
  rw [← Real.exp_add]
  congr 1
  ring

lemma partLaplace_eq_one_add_weightedU {t : ℝ} (ht : 0 < t) :
    PartLaplace t = 1 + weightedU t := by
  unfold PartLaplace weightedU
  have hp := partLaplace_summable (t := t) ht
  have hw := summable_weightedU (t := t) ht

  have hp_tail :
      Summable (fun n : ℕ => part (n + 1) * Real.exp (-(t * (n + 1)))) := by
    exact (summable_nat_add_iff 1).mpr hp

  have hw_tail :
      Summable (fun n : ℕ => u (n + 1) * modelWeight t (n + 1)) := by
    exact (summable_nat_add_iff 1).mpr hw

  rw [hp.tsum_eq_zero_add, hw.tsum_eq_zero_add]
  have h0w : u 0 * modelWeight t 0 = 0 := by
    unfold u modelWeight
    norm_num
  rw [h0w]
  have htail :
      (∑' n : ℕ, part (n + 1) * Real.exp (-(t * (n + 1))))
        =
      ∑' n : ℕ, u (n + 1) * modelWeight t (n + 1) := by
    refine tsum_congr ?_
    intro n
    rw [weightedU_term_eq_partLaplace_term (t := t) (n := n + 1) (by omega)]
  rw [htail]
  have hpart0 : part 0 * Real.exp (-(t * (0 : ℕ))) = 1 := by
    rw [part_zero_eq_one]
    norm_num
  rw [hpart0]
  ring
```

One caveat: `part_zero_eq_one` may need one local proof tweak depending on how Mathlib unfolds `Nat.Partition 0`. If `norm_num` does not close it, prove it once as a small combinatorial lemma and reuse it.

## Finite-head bound divided by `modelSaddle`

This is the key “small head / huge total mass” lemma. It only uses `modelSaddle_tendsto_atTop`.

```lean
lemma finite_modelWeight_head_div_tendsto_zero
    (N : ℕ)
    (hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto
      (fun t : ℝ =>
        (∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- Finite head is uniformly bounded for `t > 0` by its `t=0` value.
  let K : ℝ := ∑ n ∈ Finset.range N,
    Real.exp (C * Real.sqrt (n : ℝ)) / (n : ℝ)

  have hbound :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ‖∑ n ∈ Finset.range N, modelWeight t n‖ ≤ K := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hnonneg_sum : 0 ≤ ∑ n ∈ Finset.range N, modelWeight t n :=
      Finset.sum_nonneg (fun n _ => modelWeight_nonneg t n)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg_sum]
    unfold K
    refine Finset.sum_le_sum ?_
    intro n hn
    unfold modelWeight
    rcases Nat.eq_zero_or_pos n with h0 | hnpos_nat
    · subst h0
      simp
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
      have hexp_le :
          Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ))
            ≤ Real.exp (C * Real.sqrt (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [ht.le, Nat.cast_nonneg n]
      exact div_le_div_of_nonneg_right hexp_le hnpos.le

  have hK_div :
      Tendsto (fun t : ℝ => K / modelSaddle t)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop hMS_atTop

  have hzero :
      Tendsto
        (fun t : ℝ => ‖(∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t‖)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards with t
      exact norm_nonneg _
    · filter_upwards [hbound, self_mem_nhdsWithin] with t hb ht
      have hMSpos : 0 < modelSaddle t := modelSaddle_pos ht
      rw [norm_div, Real.norm_eq_abs, abs_of_pos hMSpos]
      exact div_le_div_of_nonneg_right hb hMSpos.le
    · exact hK_div

  exact tendsto_zero_iff_norm_tendsto_zero.mpr hzero
```

The confirmed name `tendsto_const_nhds.div_atTop` is used in the repo in several places, e.g. for `K / n → 0` arguments. fileciteturn87file0L26-L29

## Abelian ratio lemma

```lean
lemma weightedU_div_modelSaddle_tendsto
    {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto u atTop (𝓝 a))
    (hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto
      (fun t : ℝ => weightedU t / modelSaddle t)
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  rw [← tendsto_sub_nhds_zero_iff]

  -- It suffices to show `(weightedU - a*modelSaddle)/modelSaddle → 0`.
  have hdiff :
      Tendsto
        (fun t : ℝ =>
          (weightedU t - a * modelSaddle t) / modelSaddle t)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    have hε4 : 0 < ε / 4 := by positivity

    -- Pick `N` so the tail of `u_n` is ε/4-close to `a`.
    have htail_event : ∀ᶠ n : ℕ in atTop, |u n - a| ≤ ε / 4 := by
      have hmetric := (Metric.tendsto_nhds.mp hlim) (ε / 4) hε4
      filter_upwards [hmetric] with n hn
      simpa [dist_eq_norm, Real.norm_eq_abs] using le_of_lt hn

    obtain ⟨N, hN⟩ := eventually_atTop.1 htail_event

    obtain ⟨Mu, hMu0, hMu⟩ := u_abs_le
    let B : ℝ := Mu + a
    have hB0 : 0 ≤ B := by linarith [hMu0, ha.le]

    -- Finite-head model mass is negligible.
    have hhead0 :
        Tendsto
          (fun t : ℝ =>
            (∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t)
          (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      finite_modelWeight_head_div_tendsto_zero N hMS_atTop

    have hhead_small :
        ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
          B * ((∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t) ≤ ε / 2 := by
      have hmul :
          Tendsto
            (fun t : ℝ =>
              B * ((∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using hhead0.const_mul B
      exact hmul.eventually_le_const hε2

    filter_upwards [self_mem_nhdsWithin, hhead_small] with t ht hhead_le
    have ht : 0 < t := ht
    have hWpos : 0 < modelSaddle t := modelSaddle_pos ht
    have hsW := summable_modelWeight (t := t) ht
    have hsu := summable_weightedU (t := t) ht
    have hsaw : Summable (fun n : ℕ => a * modelWeight t n) :=
      hsW.mul_left a
    have hsdiff : Summable (fun n : ℕ => (u n - a) * modelWeight t n) := by
      have h := hsu.sub hsaw
      refine h.congr ?_
      intro n
      ring

    have hdiff_eq :
        weightedU t - a * modelSaddle t
          =
        ∑' n : ℕ, (u n - a) * modelWeight t n := by
      unfold weightedU modelSaddle modelWeight
      have h1 :
          (∑' n : ℕ, u n * (Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ)))
            -
          (∑' n : ℕ, a * (Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ)))
          =
          ∑' n : ℕ,
            (u n * (Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ))
              - a * (Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ))) := by
        rw [hsu.tsum_sub hsaw]
      rw [← h1]
      rw [tsum_mul_left]
      apply congrArg
      ext n
      ring

    have habs_summ :
        Summable (fun n : ℕ => |(u n - a) * modelWeight t n|) := by
      apply Summable.of_nonneg_of_le
        (fun n => abs_nonneg _)
        ?_
        ((summable_modelWeight (t := t) ht).mul_left B)
      intro n
      rw [abs_mul]
      have hw : 0 ≤ modelWeight t n := modelWeight_nonneg t n
      rw [abs_of_nonneg hw]
      have hu : |u n - a| ≤ B := by
        calc
          |u n - a| ≤ |u n| + |a| := abs_sub_le _ _
          _ ≤ Mu + a := by
            rw [abs_of_pos ha]
            exact add_le_add (hMu n) le_rfl
      exact mul_le_mul_of_nonneg_right hu hw

    have habs_tsum :
        |∑' n : ℕ, (u n - a) * modelWeight t n|
          ≤ ∑' n : ℕ, |(u n - a) * modelWeight t n| := by
      -- If `abs_tsum_le_tsum_abs` is unavailable in your local namespace,
      -- use the two-sided `hasSum_le` proof from `MassRateRiemannGeneral`.
      exact abs_tsum_le_tsum_abs habs_summ

    -- Split the absolute-error sum at `N`.
    have hsplit_abs :=
      Summable.sum_add_tsum_nat_add N habs_summ

    have hhead_bound :
        (∑ n ∈ Finset.range N, |(u n - a) * modelWeight t n|)
          ≤ B * ∑ n ∈ Finset.range N, modelWeight t n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul]
      have hw : 0 ≤ modelWeight t n := modelWeight_nonneg t n
      rw [abs_of_nonneg hw]
      have hu : |u n - a| ≤ B := by
        calc
          |u n - a| ≤ |u n| + |a| := abs_sub_le _ _
          _ ≤ Mu + a := by
            rw [abs_of_pos ha]
            exact add_le_add (hMu n) le_rfl
      exact mul_le_mul_of_nonneg_right hu hw

    have htail_bound :
        (∑' k : ℕ, |(u (k + N) - a) * modelWeight t (k + N)|)
          ≤ (ε / 4) * (∑' k : ℕ, modelWeight t (k + N)) := by
      have htail_summ :
          Summable (fun k : ℕ => modelWeight t (k + N)) := by
        exact (summable_nat_add_iff N).mpr (summable_modelWeight (t := t) ht)

      apply Summable.tsum_le_tsum
      · intro k
        rw [abs_mul]
        have hw : 0 ≤ modelWeight t (k + N) := modelWeight_nonneg t (k + N)
        rw [abs_of_nonneg hw]
        have hclose : |u (k + N) - a| ≤ ε / 4 := by
          exact hN (k + N) (by omega)
        exact mul_le_mul_of_nonneg_right hclose hw
      · exact (habs_summ.comp_injective (fun i j hij => by omega))
      · exact htail_summ.mul_left (ε / 4)

    have htail_weight_le_total :
        (∑' k : ℕ, modelWeight t (k + N)) ≤ modelSaddle t := by
      have hsum := summable_modelWeight (t := t) ht
      have hadd := Summable.sum_add_tsum_nat_add N hsum
      have hcomm :
          (∑' k : ℕ, modelWeight t (k + N))
            = ∑' k : ℕ, modelWeight t (N + k) := by
        apply tsum_congr
        intro k
        rw [add_comm]
      rw [hcomm]
      unfold modelSaddle modelWeight
      have hfin_nonneg : 0 ≤ ∑ n ∈ Finset.range N,
          Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ) :=
        Finset.sum_nonneg (fun n _ => by positivity)
      linarith [hadd]

    have htotal_abs :
        (∑' n : ℕ, |(u n - a) * modelWeight t n|)
          ≤ B * (∑ n ∈ Finset.range N, modelWeight t n)
              + (ε / 4) * modelSaddle t := by
      calc
        (∑' n : ℕ, |(u n - a) * modelWeight t n|)
            =
          (∑ n ∈ Finset.range N, |(u n - a) * modelWeight t n|)
            + ∑' k : ℕ, |(u (k + N) - a) * modelWeight t (k + N)| := by
              exact hsplit_abs.symm
        _ ≤ B * (∑ n ∈ Finset.range N, modelWeight t n)
              + (ε / 4) * (∑' k : ℕ, modelWeight t (k + N)) :=
              add_le_add hhead_bound htail_bound
        _ ≤ B * (∑ n ∈ Finset.range N, modelWeight t n)
              + (ε / 4) * modelSaddle t := by
              exact add_le_add_left
                (mul_le_mul_of_nonneg_left htail_weight_le_total (by positivity)) _

    have hratio_bound :
        |(weightedU t - a * modelSaddle t) / modelSaddle t| ≤ ε := by
      rw [abs_div, abs_of_pos hWpos]
      calc
        |weightedU t - a * modelSaddle t| / modelSaddle t
            ≤ (∑' n : ℕ, |(u n - a) * modelWeight t n|) / modelSaddle t := by
              rw [hdiff_eq]
              exact div_le_div_of_nonneg_right habs_tsum hWpos.le
        _ ≤
          (B * (∑ n ∈ Finset.range N, modelWeight t n)
              + (ε / 4) * modelSaddle t) / modelSaddle t := by
              exact div_le_div_of_nonneg_right htotal_abs hWpos.le
        _ =
          B * ((∑ n ∈ Finset.range N, modelWeight t n) / modelSaddle t)
            + ε / 4 := by
              field_simp [hWpos.ne']
              ring
        _ ≤ ε / 2 + ε / 4 := by
              exact add_le_add hhead_le le_rfl
        _ < ε := by linarith

    rw [dist_eq_norm, Real.norm_eq_abs, sub_zero]
    exact lt_of_le_of_lt hratio_bound (by linarith)

  refine hdiff.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hWpos : modelSaddle t ≠ 0 := (modelSaddle_pos ht).ne'
  field_simp [hWpos]
  ring
```

Uncertain name: `abs_tsum_le_tsum_abs`. If Mathlib v4.29.0 does not expose it under that name, replace that one line with the two-sided `hasSum_le` proof pattern already used in the repo’s `MassRateRiemannGeneral.lean`. That file proves
\[
|\sum' e_n|\le \sum' |e_n|
\]
using `hasSum_le` and `neg_abs_le/le_abs_self`. fileciteturn142file0L116-L135

## Log conclusion

Now the requested theorem is easy.

```lean
theorem partLaplace_log_sub_modelSaddle_tendsto_of_modelSaddle_atTop
    {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto u atTop (𝓝 a))
    (hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto
      (fun t : ℝ =>
        Real.log (PartLaplace t) - Real.log a - Real.log (modelSaddle t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hW :
      Tendsto (fun t : ℝ => weightedU t / modelSaddle t)
        (𝓝[>] (0 : ℝ)) (𝓝 a) :=
    weightedU_div_modelSaddle_tendsto ha hlim hMS_atTop

  have hInvW :
      Tendsto (fun t : ℝ => 1 / modelSaddle t)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hMS_atTop

  have hratioP :
      Tendsto
        (fun t : ℝ => PartLaplace t / (a * modelSaddle t))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hsum :
        Tendsto
          (fun t : ℝ => (1 / modelSaddle t) + weightedU t / modelSaddle t)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 + a)) :=
      hInvW.add hW
    have hscaled :
        Tendsto
          (fun t : ℝ =>
            (1 / a) * ((1 / modelSaddle t) + weightedU t / modelSaddle t))
          (𝓝[>] (0 : ℝ)) (𝓝 ((1 / a) * (0 + a))) :=
      hsum.const_mul (1 / a)
    have htarget :
        Tendsto
          (fun t : ℝ =>
            (1 / a) * ((1 / modelSaddle t) + weightedU t / modelSaddle t))
          (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa [ha.ne'] using hscaled
    refine htarget.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hWpos : modelSaddle t ≠ 0 := (modelSaddle_pos ht).ne'
    rw [partLaplace_eq_one_add_weightedU ht]
    field_simp [ha.ne', hWpos]
    ring

  have hlog :
      Tendsto
        (fun t : ℝ => Real.log (PartLaplace t / (a * modelSaddle t)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
    simpa using hcont.comp hratioP

  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hPpos : 0 < PartLaplace t := partLaplace_pos ht
  have hWpos : 0 < modelSaddle t := modelSaddle_pos ht
  rw [Real.log_div hPpos.ne' (mul_ne_zero ha.ne' hWpos.ne')]
  rw [Real.log_mul ha.ne' hWpos.ne']
  ring
```

This is the version I would actually commit first. Once brick 4 is green, derive `hMS_atTop` from the brick-4 asymptotic and wrap:

```lean
theorem partLaplace_log_sub_modelSaddle_tendsto
    {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto u atTop (𝓝 a))
    (hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto
      (fun t : ℝ =>
        Real.log (PartLaplace t) - Real.log a - Real.log (modelSaddle t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  partLaplace_log_sub_modelSaddle_tendsto_of_modelSaddle_atTop
    ha hlim hMS_atTop
```

## About `modelSaddle_tendsto_atTop`

I would not prove it in brick 3. The cleanest hypothesis is exactly:

```lean
(hMS_atTop : Tendsto modelSaddle (𝓝[>] (0 : ℝ)) atTop)
```

Brick 4 should provide it from the stronger result:

```lean
Tendsto
  (fun t : ℝ =>
    Real.log (modelSaddle t)
      - A / t
      - (1 / 2 : ℝ) * Real.log t
      - Real.log (4 * Real.sqrt Real.pi / C))
  (𝓝[>] (0 : ℝ)) (𝓝 0)
```

or, even easier, from the ratio form:

```lean
Tendsto
  (fun t : ℝ =>
    modelSaddle t /
      ((4 * Real.sqrt Real.pi / C) * Real.sqrt t * Real.exp (A / t)))
  (𝓝[>] (0 : ℝ)) (𝓝 1)
```

because the denominator tends to `atTop`. Proving it by a single floor saddle term is possible, but it duplicates saddle work and is not worth mixing into Abelian comparison.

## Answers to your questions

1. **Yes, prove the ratio form first.** The log theorem is then just continuity of `Real.log` at `1` plus `Real.log_div`/`Real.log_mul`. This is the least painful route.

2. The Abelian split is:
   \[
   \frac{\sum (u_n-a)w_n(t)}{\sum w_n(t)}
   \]
   split at `N`. The tail is bounded by `ε` times the total mass; the head is bounded by a fixed finite constant divided by `modelSaddle t`, which tends to `0`. The important tools are:
   ```lean
   Summable.sum_add_tsum_nat_add
   Summable.tsum_le_tsum
   tendsto_const_nhds.div_atTop
   squeeze_zero_norm'
   ```
   `Summable.sum_add_tsum_nat_add` is already used in the repo for shifted summable tails. fileciteturn162file0L25-L43

3. I recommend taking `modelSaddle_tendsto_atTop` as a hypothesis. If you want a standalone proof, derive it from brick 4’s ratio/log asymptotic, not from a floor lower bound.

4. The only uncertain Mathlib name above is `abs_tsum_le_tsum_abs`; if absent, use the repo’s two-sided `hasSum_le` pattern. Everything else is either already used in the repo or standard v4.29 API.
