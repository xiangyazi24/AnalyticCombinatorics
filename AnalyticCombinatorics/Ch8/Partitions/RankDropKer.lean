import AnalyticCombinatorics.Ch8.Partitions.PartitionRenewal

/-!
# T2.1 (honest restatement): the rank-drop kernel and its exponential tail majorant

The pointwise rank-drop *local limit* `rankDropKer v d → p d` is FALSE for the floor rank
`rnk v = ⌊3√v⌋` (the drop-`d` set is a `y`-window whose edges oscillate with `frac(3√v)`; see
`HANDOFF/TASK-T2-gap.md`).  The engine, however, does not consume that limit; it consumes a
one-sided pair:

* an **exponential tail majorant** of the rank-drop, uniform in `v` (this file, `Pker_rankDrop_tail_majorant`);
* a **phase-uniform per-drop minorization** `rankDropKer v 1, rankDropKer v 2 ≥ η` (the genuinely
  new analytic input; see the gap doc).

This file builds the tail majorant.  An *upper* bound on the rank-drop is unaffected by the floor
oscillation: a rank drop exceeding `A` forces a *large jump* `m ≳ (A/3)√v`, whose `erdosWeight`-mass
is exponentially small in `A` (banked block-majorant machinery `left_half_tail_sum_le_block_majorants`
for the bulk `2m ≤ v` half, and `right_half_kernel_sum_le` for the `2m > v` half).

`rankDropKer` is the rank-drop law of the predecessor kernel `Pker`; it is exactly the pushforward of
`Pker v ·` under the rank-drop `k ↦ rnk v - rnk k`.

Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Rank-drop kernel.**  `rankDropKer v d` is the `Pker`-probability that one predecessor step
from `v` drops the rank by exactly `d`: the mass of `Pker v ·` on `{k < v : rnk v − rnk k = d}`. -/
noncomputable def rankDropKer (v d : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range v).filter (fun k => rnk v - rnk k = d), Pker v k

/-- `rankDropKer` is nonnegative. -/
lemma rankDropKer_nonneg (v d : ℕ) : 0 ≤ rankDropKer v d :=
  Finset.sum_nonneg (fun k _ => Pker_nonneg v k)

/-- **Large drop ⟹ large jump.**  If the rank drops by more than `A` on a step `v → k` (`1 ≤ k < v`),
then the jump `m = v − k` exceeds `(A/3)·√v`.  (A drop bigger than `A` forces `3√k < rnk v − A ≤
3√v − A`, hence `√v − √k > A/3`, hence `v − k = (√v−√k)(√v+√k) > (A/3)√v`.)  An *upper* bound on the
drop in terms of the jump — unaffected by the floor oscillation. -/
lemma large_drop_forces_large_jump {v k A : ℕ} (hk1 : 1 ≤ k) (hkv : k < v)
    (hdrop : A < rnk v - rnk k) :
    ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < ((v - k : ℕ) : ℝ) := by
  have hkle : rnk k ≤ rnk v := rnk_mono (le_of_lt hkv)
  -- rnk k + A < rnk v in ℕ, hence in ℝ
  have hNlt : rnk k + A + 1 ≤ rnk v := by omega
  have hRlt : (rnk k : ℝ) + (A : ℝ) + 1 ≤ (rnk v : ℝ) := by exact_mod_cast hNlt
  have hvpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (by omega : 0 < v)
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hsv : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hvpos
  have hsk : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  -- 3√k < rnk k + 1 ≤ rnk v − A, and rnk v ≤ 3√v
  have h3k : (3 : ℝ) * Real.sqrt (k : ℝ) < (rnk k : ℝ) + 1 := (rnk_sqrt_bounds k).2
  have h3v : (rnk v : ℝ) ≤ 3 * Real.sqrt (v : ℝ) := (rnk_sqrt_bounds v).1
  -- 3√k < 3√v − A
  have hgap3 : 3 * Real.sqrt (k : ℝ) < 3 * Real.sqrt (v : ℝ) - (A : ℝ) := by linarith
  have hgap : Real.sqrt (v : ℝ) - Real.sqrt (k : ℝ) > (A : ℝ) / 3 := by linarith
  -- m = v − k = (√v − √k)(√v + √k)
  have hcast : ((v - k : ℕ) : ℝ) = (v : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hkv)]
  have hprod : (Real.sqrt (v : ℝ) - Real.sqrt (k : ℝ))
      * (Real.sqrt (v : ℝ) + Real.sqrt (k : ℝ)) = (v : ℝ) - (k : ℝ) := by
    have e1 : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt hvpos.le
    have e2 : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hkpos.le
    nlinarith [e1, e2]
  rw [hcast, ← hprod]
  -- (√v − √k)(√v + √k) ≥ (A/3)·√v   since (√v − √k) > A/3 ≥ 0 and (√v + √k) ≥ √v > 0
  have hApos : (0 : ℝ) ≤ (A : ℝ) / 3 := by positivity
  nlinarith [hgap, hsv, hsk, hApos]

/-- The rank-drop tail `∑_{d > A} rankDropKer v d` regroups exactly as the `Pker`-mass over the set of
predecessors `k` whose rank-drop exceeds `A`. -/
lemma rankDropKer_tail_eq_mass (v A : ℕ) :
    (∑ d ∈ (Finset.range v).filter (A < ·), rankDropKer v d)
      = ∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
          Pker v k := by
  classical
  unfold rankDropKer
  -- make both an honest double sum over range v × range v of guarded terms
  have hLHS : (∑ d ∈ (Finset.range v).filter (A < ·),
        ∑ k ∈ (Finset.range v).filter (fun k => rnk v - rnk k = d), Pker v k)
      = ∑ d ∈ Finset.range v, ∑ k ∈ Finset.range v,
          (if A < d then (if rnk v - rnk k = d then Pker v k else 0) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hAd : A < d
    · rw [if_pos hAd, Finset.sum_filter]
      exact Finset.sum_congr rfl (fun k _ => by rw [if_pos hAd])
    · rw [if_neg hAd, Finset.sum_eq_zero (fun k _ => by rw [if_neg hAd])]
  rw [hLHS, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- inner: ∑_{d ∈ range v} (if A < d then (if rnk v − rnk k = d then Pker v k else 0) else 0)
  by_cases hkv : A < rnk v - rnk k ∧ rnk v - rnk k < v
  · rw [if_pos hkv]
    rw [Finset.sum_eq_single (rnk v - rnk k)]
    · rw [if_pos hkv.1, if_pos rfl]
    · intro d _ hd
      by_cases hAd : A < d
      · rw [if_pos hAd, if_neg (by exact fun h => hd h.symm)]
      · rw [if_neg hAd]
    · intro hmem
      exact absurd (Finset.mem_range.mpr hkv.2) hmem
  · rw [if_neg hkv]
    refine Finset.sum_eq_zero (fun d hd => ?_)
    by_cases hAd : A < d
    · rw [if_pos hAd]
      by_cases hdd : rnk v - rnk k = d
      · exact absurd ⟨hdd ▸ hAd, hdd ▸ Finset.mem_range.mp hd⟩ hkv
      · rw [if_neg hdd]
    · rw [if_neg hAd]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
