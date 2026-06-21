import AnalyticCombinatorics.Ch8.Partitions.PartitionRenewal
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernelClose

/-!
# T2.1 (honest restatement): the rank-drop kernel and its exponential tail majorant

The pointwise rank-drop *local limit* `rankDropKer v d → p d` is FALSE for the floor rank
`rnk v = ⌊3√v⌋` (the drop-`d` set is a `y`-window whose edges oscillate with `frac(3√v)`).  The engine, however, does not consume that limit; it consumes a
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

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

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

/-- **Numerator mass in `m`-coordinates, dominated by a far-jump window.**  The `erdosWeight`-mass of
the predecessors with rank-drop `> A` is, after the reflection `k ↦ v − k`, dominated by the
`erdosWeight`-mass on the far window `{m : (A/3)√v < m}` (every drop-`>A` jump exceeds `(A/3)√v` by
`large_drop_forces_large_jump`). -/
lemma rankDrop_mass_le_far_window {v A : ℕ} (hv : 2 ≤ v) :
    (∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
        erdosWeight v (v - k))
      ≤ ∑ m ∈ Finset.Icc 1 (v - 1),
          (if ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ) then erdosWeight v m else 0) := by
  classical
  -- reflect k ↦ v − k onto the m-window sum, then enlarge the index set
  have hreflect :
      (∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
          erdosWeight v (v - k))
        = ∑ m ∈ Finset.Icc 1 (v - 1),
            (if A < rnk v - rnk (v - m) ∧ rnk v - rnk (v - m) < v
              then erdosWeight v m else 0) := by
    -- rewrite the filtered LHS as a masked sum over Icc 1 (v−1) in k, reflect to m
    have hLHS :
        (∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
            erdosWeight v (v - k))
          = ∑ k ∈ Finset.Icc 1 (v - 1),
              (if A < rnk v - rnk k ∧ rnk v - rnk k < v then erdosWeight v (v - k) else 0) := by
      rw [Finset.sum_filter]
      symm
      apply Finset.sum_subset_zero_on_sdiff
      · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
      · intro k hk
        rw [Finset.mem_sdiff, Finset.mem_range] at hk
        -- k ∈ range v but k ∉ Icc 1 (v−1) ⟹ k = 0
        have hk0 : k = 0 := by
          rcases Nat.eq_zero_or_pos k with h | h
          · exact h
          · exact absurd (Finset.mem_Icc.mpr ⟨h, by omega⟩) hk.2
        subst hk0
        by_cases hc : A < rnk v - rnk 0 ∧ rnk v - rnk 0 < v
        · rw [if_pos hc]
          have : rnk v - rnk 0 < v := hc.2
          -- rnk 0 = 0, so A < rnk v < v ⟹ but erdosWeight v (v−0) = erdosWeight v v = 0? not directly.
          -- instead: k = 0 means v − k = v, erdosWeight v v has (v−v)=0 divisor; use erdosWeight def
          simp only [erdosWeight, Nat.sub_zero, Nat.sub_self, Nat.cast_zero, div_zero,
            zero_mul]
        · rw [if_neg hc]
      · intro k _; rfl
    rw [hLHS, ← sum_Icc_reflect_sub v
      (fun k => if A < rnk v - rnk k ∧ rnk v - rnk k < v then erdosWeight v (v - k) else 0)]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_Icc] at hm
    by_cases hc : A < rnk v - rnk (v - m) ∧ rnk v - rnk (v - m) < v
    · rw [if_pos hc, if_pos hc, show v - (v - m) = m by omega]
    · rw [if_neg hc, if_neg hc]
  rw [hreflect]
  refine Finset.sum_le_sum (fun m hm => ?_)
  rw [Finset.mem_Icc] at hm
  by_cases hc : A < rnk v - rnk (v - m) ∧ rnk v - rnk (v - m) < v
  · rw [if_pos hc]
    -- drop > A at predecessor (v−m) forces (A/3)√v < m via large_drop_forces_large_jump
    have hm1 : 1 ≤ v - m := by omega
    have hmv : v - m < v := by omega
    have hjump := large_drop_forces_large_jump (v := v) (k := v - m) (A := A) hm1 hmv hc.1
    rw [show v - (v - m) = m by omega] at hjump
    rw [if_pos hjump]
  · rw [if_neg hc]
    by_cases hc2 : ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ)
    · rw [if_pos hc2]; exact erdosWeight_nonneg_of_mem (Finset.mem_Icc.mpr hm)
    · rw [if_neg hc2]

/-- The convergent geometric-quadratic constant `G = ∑'_j (j+1)²·exp(−C/2)^j`. -/
noncomputable def rankDropG : ℝ := ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * Real.exp (-(C / 2)) ^ j

lemma rankDropG_nonneg : 0 ≤ rankDropG :=
  tsum_nonneg (fun j => by positivity)

/-- **Far-window split bound.**  For `v` with `2 ≤ v` and the eventual poly-beats-exp slack
`(v:ℝ)³ ≤ exp((C/20)√v)`, the `erdosWeight`-mass on the far window `{m : (A/3)√v < m}` splits into a
left (`2m ≤ v`) block-majorant tail and a right (`2m > v`) half-kernel tail. -/
lemma far_window_split_le {v A : ℕ} (hv : 0 < v) :
    (∑ m ∈ Finset.Icc 1 (v - 1),
        (if ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ) then erdosWeight v m else 0))
      ≤ (∑ m ∈ Finset.Icc 1 (v - 1),
            (if (⌊(A : ℝ) / 3⌋₊ : ℝ) * Real.sqrt (v : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ v
              then erdosWeight v m else 0))
        + (∑ m ∈ Finset.Icc 1 (v - 1), (if v < 2 * m then erdosWeight v m else 0)) := by
  classical
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun m hm => ?_)
  rw [Finset.mem_Icc] at hm
  have hew : 0 ≤ erdosWeight v m := erdosWeight_nonneg_of_mem (Finset.mem_Icc.mpr hm)
  by_cases hfar : ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ)
  · rw [if_pos hfar]
    rcases le_or_gt (2 * m) v with h2 | h2
    · -- left half: ⌊A/3⌋√v ≤ (A/3)√v < m
      have hKle : (⌊(A : ℝ) / 3⌋₊ : ℝ) * Real.sqrt (v : ℝ) ≤ (m : ℝ) := by
        have hfloor : (⌊(A : ℝ) / 3⌋₊ : ℝ) ≤ (A : ℝ) / 3 := Nat.floor_le (by positivity)
        have hsv : 0 ≤ Real.sqrt (v : ℝ) := Real.sqrt_nonneg _
        nlinarith [hfar, mul_le_mul_of_nonneg_right hfloor hsv]
      rw [if_pos ⟨hKle, h2⟩, if_neg (by omega : ¬ v < 2 * m)]
      linarith
    · -- right half
      rw [if_pos h2]
      by_cases hKL : (⌊(A : ℝ) / 3⌋₊ : ℝ) * Real.sqrt (v : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ v
      · exact absurd hKL.2 (by omega)
      · rw [if_neg hKL]; linarith
  · rw [if_neg hfar]
    refine add_nonneg ?_ ?_
    · split <;> [exact hew; exact le_refl 0]
    · split <;> [exact hew; exact le_refl 0]

/-- **Left-half block-majorant bound.**  The bulk (`2m ≤ v`) far-window mass at threshold index
`K = ⌊A/3⌋` is bounded by the banked geometric-quadratic block tail. -/
lemma left_block_tail_le {v : ℕ} (hv : 0 < v) (K : ℕ) :
    (∑ m ∈ Finset.Icc 1 (v - 1),
        (if (K : ℝ) * Real.sqrt (v : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ v then erdosWeight v m else 0))
      ≤ 2 * sigmaQuadConst * ((K : ℝ) + 1) ^ 2 * rankDropG * Real.exp (-(C / 2) * (K : ℝ)) := by
  calc (∑ m ∈ Finset.Icc 1 (v - 1),
          (if (K : ℝ) * Real.sqrt (v : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ v then erdosWeight v m else 0))
      ≤ ∑ k ∈ Finset.range (numBlocks v), if K ≤ k then leftBlockMajorant k else 0 :=
        left_half_tail_sum_le_block_majorants v K hv
    _ ≤ ∑' j : ℕ, leftBlockMajorant (j + K) :=
        finite_block_majorant_tail_le_shifted_tsum (numBlocks v) K
    _ ≤ 2 * sigmaQuadConst * ((K : ℝ) + 1) ^ 2 * rankDropG * Real.exp (-(C / 2) * (K : ℝ)) :=
        leftBlockMajorant_shifted_tsum_le K

/-- Elementary sup-bound: for `c > 0` and `x ≥ 0`, `(x+1)·e^{−cx} ≤ 1/c + 1`. -/
lemma succ_mul_exp_neg_le {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    (x + 1) * Real.exp (-c * x) ≤ 1 / c + 1 := by
  have hexp : c * x + 1 ≤ Real.exp (c * x) := by
    have := Real.add_one_le_exp (c * x); linarith
  have hepos : 0 < Real.exp (c * x) := Real.exp_pos _
  have he1 : (1 : ℝ) ≤ Real.exp (c * x) :=
    Real.one_le_exp_iff.mpr (by positivity)
  -- x + 1 ≤ (1/c + 1)·e^{cx}
  have hkey : x + 1 ≤ (1 / c + 1) * Real.exp (c * x) := by
    have hcx : c * x ≤ Real.exp (c * x) - 1 := by linarith
    have hx_le : x ≤ (Real.exp (c * x) - 1) / c := by
      rw [le_div_iff₀ hc]; nlinarith [hcx]
    have hdiv : (Real.exp (c * x) - 1) / c ≤ Real.exp (c * x) / c := by
      gcongr
      linarith
    have hexpand : (1 / c + 1) * Real.exp (c * x)
        = Real.exp (c * x) / c + Real.exp (c * x) := by ring
    rw [hexpand]
    linarith [hx_le, hdiv, he1]
  -- multiply by e^{−cx}
  have hrw : Real.exp (-c * x) = (Real.exp (c * x))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [hrw, mul_inv_le_iff₀ hepos]
  exact hkey

/-- **Left-half constant bound.**  `2σQ(⌊A/3⌋+1)²·G·e^{−(C/2)⌊A/3⌋} ≤ C_L·(A+1)·e^{−(C/60)A}` with
`C_L := 4σQ·G·e^{C/3}·(20/(3C)+1)`. -/
lemma left_block_const_bound (A : ℕ) :
    2 * sigmaQuadConst * ((⌊(A : ℝ) / 3⌋₊ : ℝ) + 1) ^ 2 * rankDropG
        * Real.exp (-(C / 2) * (⌊(A : ℝ) / 3⌋₊ : ℝ))
      ≤ (2 * sigmaQuadConst * rankDropG * Real.exp (C / 2) * (20 / (3 * C) + 1))
          * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
  have hC := C_pos
  have hsQ := sigmaQuadConst_pos
  have hG := rankDropG_nonneg
  set j : ℝ := (⌊(A : ℝ) / 3⌋₊ : ℝ) with hjdef
  have hj0 : 0 ≤ j := by positivity
  have hAle : 3 * j ≥ (A : ℝ) - 3 := by
    have hfl : (A : ℝ) / 3 < j + 1 := by
      have := Nat.lt_floor_add_one ((A : ℝ) / 3); rw [← hjdef] at this; exact this
    linarith
  have hjub : j + 1 ≤ (A : ℝ) + 1 := by
    have hflub : j ≤ (A : ℝ) / 3 := Nat.floor_le (by positivity)
    have hA0 : (0 : ℝ) ≤ (A : ℝ) := by positivity
    linarith
  -- e^{−(C/2)j} ≤ e^{C/3}·e^{−(C/6)A}
  have hexpj : Real.exp (-(C / 2) * j) ≤ Real.exp (C / 2) * Real.exp (-(C / 6) * (A : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hAle, hC]
  -- (j+1)² ≤ (A+1)²
  have hsq : (j + 1) ^ 2 ≤ ((A : ℝ) + 1) ^ 2 := by
    have h0 : (0 : ℝ) ≤ j + 1 := by linarith
    nlinarith [hjub, h0]
  -- (A+1)²·e^{−(C/6)A} ≤ (20/(3C)+1)·(A+1)·e^{−(C/60)A}
  have hsucc : ((A : ℝ) + 1) * Real.exp (-(3 * C / 20) * (A : ℝ)) ≤ 20 / (3 * C) + 1 := by
    have h := succ_mul_exp_neg_le (c := 3 * C / 20) (x := (A : ℝ)) (by positivity) (by positivity)
    have hrw : (1 : ℝ) / (3 * C / 20) = 20 / (3 * C) := by
      rw [div_div_eq_mul_div, one_mul]
    rw [hrw] at h; exact h
  have hsplit : ((A : ℝ) + 1) ^ 2 * Real.exp (-(C / 6) * (A : ℝ))
      ≤ (20 / (3 * C) + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
    have hfac : Real.exp (-(C / 6) * (A : ℝ))
        = Real.exp (-(3 * C / 20) * (A : ℝ)) * Real.exp (-(C / 60) * (A : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hfac]
    have hA1 : (0 : ℝ) ≤ (A : ℝ) + 1 := by positivity
    have he : (0 : ℝ) ≤ Real.exp (-(C / 60) * (A : ℝ)) := (Real.exp_pos _).le
    calc ((A : ℝ) + 1) ^ 2 * (Real.exp (-(3 * C / 20) * (A : ℝ)) * Real.exp (-(C / 60) * (A : ℝ)))
        = (((A : ℝ) + 1) * Real.exp (-(3 * C / 20) * (A : ℝ)))
            * (((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ))) := by ring
      _ ≤ (20 / (3 * C) + 1) * (((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ))) := by
            apply mul_le_mul_of_nonneg_right hsucc
            exact mul_nonneg hA1 he
      _ = (20 / (3 * C) + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by ring
  -- assemble
  have hC0 : (0 : ℝ) ≤ 2 * sigmaQuadConst * rankDropG := by positivity
  calc 2 * sigmaQuadConst * (j + 1) ^ 2 * rankDropG * Real.exp (-(C / 2) * j)
      = (2 * sigmaQuadConst * rankDropG) * ((j + 1) ^ 2 * Real.exp (-(C / 2) * j)) := by ring
    _ ≤ (2 * sigmaQuadConst * rankDropG)
          * (((A : ℝ) + 1) ^ 2 * (Real.exp (C / 2) * Real.exp (-(C / 6) * (A : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          have hb : (0 : ℝ) ≤ ((A : ℝ) + 1) ^ 2 := by positivity
          exact mul_le_mul hsq hexpj (Real.exp_nonneg _) hb
    _ = (2 * sigmaQuadConst * rankDropG * Real.exp (C / 2))
          * (((A : ℝ) + 1) ^ 2 * Real.exp (-(C / 6) * (A : ℝ))) := by ring
    _ ≤ (2 * sigmaQuadConst * rankDropG * Real.exp (C / 2))
          * ((20 / (3 * C) + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ))) := by
          apply mul_le_mul_of_nonneg_left hsplit
          positivity
    _ = (2 * sigmaQuadConst * rankDropG * Real.exp (C / 2) * (20 / (3 * C) + 1))
          * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by ring

/-- **T2.1 tail majorant (engine input).**  The rank-drop tail beyond `A` is uniformly (eventually in
`v`) dominated by `C₀·(A+1)·e^{−γA}` with `γ = C/60 > 0`.  An upper bound on the floor-rank drop is
unaffected by the documented `frac(3√v)` oscillation: a drop `> A` forces a jump `> (A/3)√v`, whose
`erdosWeight`-mass is exponentially small in `A` (bulk via the banked block majorants; the `2m > v`
half via `right_half_kernel_sum_le` + the poly-beats-exp slack `v³ ≤ e^{(C/20)√v}`; for `A ≥ 3√v` the
far window is empty). -/
theorem Pker_rankDrop_tail_majorant :
    ∃ (γ : ℝ) (C₀ : ℝ), 0 < γ ∧ ∀ᶠ v : ℕ in atTop, ∀ A : ℕ,
        (∑ d ∈ (Finset.range v).filter (A < ·), rankDropKer v d)
          ≤ C₀ * ((A : ℝ) + 1) * Real.exp (-γ * (A : ℝ)) := by
  have hC := C_pos
  have hsQ := sigmaQuadConst_pos
  have hG := rankDropG_nonneg
  set CL : ℝ := 2 * sigmaQuadConst * rankDropG * Real.exp (C / 2) * (20 / (3 * C) + 1) with hCLdef
  have hCLnn : 0 ≤ CL := by rw [hCLdef]; positivity
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  -- eventual: kernelMass ≥ 1/2
  have hhalf : ∀ᶠ v : ℕ in atTop, K / (v : ℝ) ≤ 1 / 2 := by
    have htend : Tendsto (fun v : ℕ => K / (v : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    exact htend.eventually_le_const (by norm_num)
  -- slack: v³ e^{−(C/20)√v} ≤ 1/v ≤ 1
  have hslack := poly_mul_exp_neg_sqrt_le_inv (C / 20) (by linarith) 3
  refine ⟨C / 60, 2 * (CL + 1), by positivity, ?_⟩
  filter_upwards [hKev, hhalf, hslack, eventually_ge_atTop 2] with v hKv hhalfv hslackv hv2
  intro A
  have hv0 : 0 < v := by omega
  have hvR : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast (by omega : 1 ≤ v)
  have hvpos : (0 : ℝ) < (v : ℝ) := by linarith
  have hsv : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hvpos
  -- kernelMass ≥ 1/2
  obtain ⟨hSlo, _⟩ := abs_le.1 hKv
  have hSge : (1 : ℝ) / 2 ≤ kernelMass v := by linarith [hhalfv]
  have hSpos : (0 : ℝ) < kernelMass v := by linarith
  -- the tail = Pker-mass over drop>A ≤ 2·(erdosWeight far mass)
  rw [rankDropKer_tail_eq_mass]
  have hew_nn : ∀ m, 0 ≤ erdosWeight v m := by
    intro m
    unfold erdosWeight
    exact mul_nonneg (div_nonneg (sigmaR_nonneg m) (by positivity)) (Real.exp_nonneg _)
  have hPker_le : ∀ k, Pker v k ≤ 2 * erdosWeight v (v - k) := by
    intro k
    rcases Nat.lt_or_ge k v with hkv | hkv
    · rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · have hP0 : Pker v k = 0 := by unfold Pker; rw [if_neg (by omega)]
        rw [hP0]; linarith [hew_nn (v - k)]
      · have hPeq : Pker v k = erdosWeight v (v - k) / kernelMass v := by
          unfold Pker; rw [if_pos ⟨hk1, hkv⟩]
        rw [hPeq, div_le_iff₀ hSpos]
        nlinarith [hew_nn (v - k), hSge]
    · have hP0 : Pker v k = 0 := by unfold Pker; rw [if_neg (by omega)]
      rw [hP0]; linarith [hew_nn (v - k)]
  have hmass_le :
      (∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v), Pker v k)
        ≤ 2 * ∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
              erdosWeight v (v - k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hPker_le k)
  refine le_trans hmass_le ?_
  -- now bound 2·(erdosWeight far mass)
  set FW := ∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
              erdosWeight v (v - k) with hFWdef
  -- FW ≤ ∑_{m: (A/3)√v < m} erdosWeight
  have hFWwin : FW ≤ ∑ m ∈ Finset.Icc 1 (v - 1),
        (if ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ) then erdosWeight v m else 0) :=
    rankDrop_mass_le_far_window (by omega)
  rcases lt_or_ge (A : ℝ) (3 * Real.sqrt (v : ℝ)) with hAlt | hAge
  · -- A < 3√v : split into left + right
    have hsplit := far_window_split_le (v := v) (A := A) hv0
    -- left bound
    have hleft := left_block_tail_le (v := v) hv0 (⌊(A : ℝ) / 3⌋₊)
    have hleftconst := left_block_const_bound A
    -- right bound: v³ e^{−(C/10)√v} ≤ e^{−(C/20)√v} ≤ e^{−(C/60)A} ≤ (A+1)e^{−(C/60)A}
    have hright0 := right_half_kernel_sum_le v
    have hrwin : (v : ℝ) ^ 3 * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) ≤ 1 := by
      calc (v : ℝ) ^ 3 * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) ≤ 1 / (v : ℝ) := hslackv
        _ ≤ 1 := by rw [div_le_one hvpos]; exact hvR
    have hright1 : (v : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (v : ℝ))
        ≤ Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) := by
      have hfac : Real.exp (-(C / 10) * Real.sqrt (v : ℝ))
          = Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hfac]
      calc (v : ℝ) ^ 3 * (Real.exp (-(C / 20) * Real.sqrt (v : ℝ))
              * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)))
          = ((v : ℝ) ^ 3 * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)))
              * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) := by ring
        _ ≤ 1 * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) :=
            mul_le_mul_of_nonneg_right hrwin (Real.exp_nonneg _)
        _ = Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) := by ring
    have hright2 : Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) ≤ Real.exp (-(C / 60) * (A : ℝ)) := by
      apply Real.exp_le_exp.mpr
      -- −(C/20)√v ≤ −(C/60)A  ⟺  (C/60)A ≤ (C/20)√v  ⟸  A ≤ 3√v
      nlinarith [hAlt, hC, hsv]
    have hrightfin : (∑ m ∈ Finset.Icc 1 (v - 1), (if v < 2 * m then erdosWeight v m else 0))
        ≤ ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
      have hA1 : (1 : ℝ) ≤ (A : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (A : ℝ) := by positivity
        linarith
      calc (∑ m ∈ Finset.Icc 1 (v - 1), (if v < 2 * m then erdosWeight v m else 0))
          ≤ (v : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (v : ℝ)) := hright0
        _ ≤ Real.exp (-(C / 60) * (A : ℝ)) := le_trans hright1 hright2
        _ ≤ ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
            nlinarith [hA1, Real.exp_nonneg (-(C / 60) * (A : ℝ))]
    -- combine: FW ≤ left + right ≤ CL(A+1)e^{−γA} + (A+1)e^{−γA} = (CL+1)(A+1)e^{−γA}
    have hFWtotal : FW ≤ (CL + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
      calc FW ≤ ∑ m ∈ Finset.Icc 1 (v - 1),
                (if ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ) then erdosWeight v m else 0) := hFWwin
        _ ≤ _ := hsplit
        _ ≤ (2 * sigmaQuadConst * ((⌊(A : ℝ) / 3⌋₊ : ℝ) + 1) ^ 2 * rankDropG
                * Real.exp (-(C / 2) * (⌊(A : ℝ) / 3⌋₊ : ℝ)))
              + ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
            apply add_le_add hleft hrightfin
        _ ≤ CL * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ))
              + ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
            have hL : 2 * sigmaQuadConst * ((⌊(A : ℝ) / 3⌋₊ : ℝ) + 1) ^ 2 * rankDropG
                  * Real.exp (-(C / 2) * (⌊(A : ℝ) / 3⌋₊ : ℝ))
                ≤ CL * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
              rw [hCLdef]; exact hleftconst
            linarith [hL]
        _ = (CL + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by ring
    calc 2 * FW ≤ 2 * ((CL + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ))) := by
          linarith [hFWtotal]
      _ = 2 * (CL + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by ring
  · -- A ≥ 3√v : far window empty, FW = 0
    have hFW0 : FW ≤ 0 := by
      refine le_trans hFWwin ?_
      apply le_of_eq
      refine Finset.sum_eq_zero (fun m hm => ?_)
      rw [Finset.mem_Icc] at hm
      have hmle : (m : ℝ) ≤ (v : ℝ) - 1 := by
        have : (m : ℝ) ≤ ((v - 1 : ℕ) : ℝ) := by exact_mod_cast hm.2
        rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
      have hnot : ¬ ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ) := by
        push_neg
        -- (A/3)√v ≥ √v·√v = v > m
        have hAge3 : Real.sqrt (v : ℝ) ≤ (A : ℝ) / 3 := by linarith [hAge]
        have hvv : Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) = (v : ℝ) :=
          Real.mul_self_sqrt hvpos.le
        nlinarith [hAge3, hsv, hmle, hvv]
      rw [if_neg hnot]
    have hFWnn : 0 ≤ FW := by
      rw [hFWdef]
      exact Finset.sum_nonneg (fun k _ => hew_nn (v - k))
    have hFWzero : FW = 0 := le_antisymm hFW0 hFWnn
    rw [hFWzero, mul_zero]
    have hexpnn : (0 : ℝ) ≤ Real.exp (-(C / 60) * (A : ℝ)) := Real.exp_nonneg _
    have hA1 : (0 : ℝ) ≤ (A : ℝ) + 1 := by positivity
    have : (0 : ℝ) ≤ 2 * (CL + 1) * ((A : ℝ) + 1) :=
      mul_nonneg (by linarith [hCLnn]) hA1
    exact mul_nonneg this hexpnn

end AnalyticCombinatorics.Ch8.Partitions.Erdos
