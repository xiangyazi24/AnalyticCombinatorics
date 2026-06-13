import AnalyticCombinatorics.Ch8.Partitions.RankBandEntrance
import AnalyticCombinatorics.Ch8.Partitions.RankDropKer
import AnalyticCombinatorics.Ch8.Partitions.RankDropMinor
import AnalyticCombinatorics.Ch8.Partitions.DefectSummable

/-!
# TASK T2-ceiling, L3: the rank-only ceiling-level hit lower bound

L3 (R7 route): the first-entrance law into the down-set `ceilBand C 1 = {rnk ≤ C}` from a high start
`n` (`rnk n ≥ C`) lands at the **exact ceiling level** `{rnk = C}` (vs overshooting to `{rnk < C}`)
with mass `≥ α`, *uniformly over all heights* `rnk n ≥ C`.

This is the rank-renewal mass lower bound.  It is NOT the naive `η^gap` (which decays with the
height): holding (drop-0 mass `rankDropKer v 0 = Θ(1)`) is folded out **inline** by a strong
induction on the value `v`, and the per-level overshoot tail is absorbed by a **subsolution**
`β : ℕ → ℝ`, antitone, `β 0 ≤ 1`, `β r ≥ α > 0`, satisfying the slope condition
`η · (β (r-1) − β r) ≥ ε_r · β r`, where `η` is the banked per-drop minorizer
(`Pker_rankDrop_minorization`) and `ε_r` the banked exponential overshoot tail
(`Pker_rankDrop_tail_majorant`).

The decomposition is
`g C v ≥ ∑_{d=0}^{r} rankDropKer v d · β(r−d)`  (`r = rnk v − C`),
and the slope condition forces `g C v ≥ β r ≥ α` by strong induction.

This file proves the two reusable cores:

* `pushforward_rankDrop`: `∑_{k<v} Pker v k · f (rnk v − rnk k) = ∑_{d ≤ rnk v} rankDropKer v d · f d`
  for any `f` (the rank-drop pushforward of one `Pker` step);
* `ceilingHit_ge_of_subsolution`: the abstract subsolution ⟹ uniform lower bound (strong induction).

NEW file; imports the banked bricks, does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Exact ceiling-level hit mass.**  `ceilHit C v` is the first-entrance mass into the down-set
`ceilBand C 1 = {rnk ≤ C}` that lands at the exact ceiling level `{rnk = C}`. -/
noncomputable def ceilHit (C v : ℕ) : ℝ :=
  ∑ x ∈ (ceilBand C 1).filter (fun x => C ≤ rnk x), enterBandKer Pker (ceilBand C 1) v x

lemma ceilHit_nonneg (C v : ℕ) : 0 ≤ ceilHit C v :=
  Finset.sum_nonneg (fun x _ => enterBandKer_nonneg (fun a b => Pker_nonneg a b) v x)

/-- For a state already at the ceiling level (`rnk v = C`), the entrance is the point mass and the
exact-level hit mass is `1`. -/
lemma ceilHit_of_rnk_eq {C v : ℕ} (hv : rnk v = C) : ceilHit C v = 1 := by
  classical
  have hmem : v ∈ ceilBand C 1 := mem_ceilBand_iff.mpr (by omega)
  unfold ceilHit
  have hpt : ∀ x, enterBandKer Pker (ceilBand C 1) v x = if x = v then 1 else 0 := by
    intro x; rw [enterBandKer_eq, if_pos hmem]
  rw [Finset.sum_congr rfl (fun x _ => hpt x)]
  rw [Finset.sum_ite_eq' ((ceilBand C 1).filter (fun x => C ≤ rnk x)) v (fun _ => (1:ℝ))]
  rw [if_pos (Finset.mem_filter.mpr ⟨hmem, by omega⟩)]

/-- **Rank-drop pushforward of one step.**  For any `f : ℕ → ℝ`, summing `Pker v k · f (rnk v − rnk k)`
over predecessors `k < v` equals `∑_{d ∈ range (rnk v + 1)} rankDropKer v d · f d`.  (Every
predecessor `k < v` has `rnk k ≤ rnk v`, so the drop `rnk v − rnk k` lies in `[0, rnk v]`.) -/
lemma pushforward_rankDrop (v : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range v, Pker v k * f (rnk v - rnk k))
      = ∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d * f d := by
  classical
  -- group predecessors by their drop value
  have hgroup : (∑ k ∈ Finset.range v, Pker v k * f (rnk v - rnk k))
      = ∑ d ∈ Finset.range (rnk v + 1),
          ∑ k ∈ (Finset.range v).filter (fun k => rnk v - rnk k = d), Pker v k * f (rnk v - rnk k) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun k => rnk v - rnk k)
        (t := Finset.range (rnk v + 1))]
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    have : rnk k ≤ rnk v := rnk_mono (le_of_lt hk)
    omega
  rw [hgroup]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  -- on the fiber, rnk v − rnk k = d, so f (rnk v − rnk k) = f d; factor out
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [(Finset.mem_filter.mp hk).2])]
  rw [← Finset.sum_mul]
  rfl

/-- For a state strictly below the ceiling level (`rnk v < C`), the exact-level hit mass is `0`
(the point-mass entrance lands below `C`). -/
lemma ceilHit_of_rnk_lt {C v : ℕ} (hv : rnk v < C) : ceilHit C v = 0 := by
  classical
  have hmem : v ∈ ceilBand C 1 := mem_ceilBand_iff.mpr (by omega)
  unfold ceilHit
  refine Finset.sum_eq_zero (fun x hx => ?_)
  rw [enterBandKer_eq, if_pos hmem]
  by_cases hxv : x = v
  · exfalso
    have : C ≤ rnk x := (Finset.mem_filter.mp hx).2
    rw [hxv] at this; omega
  · rw [if_neg hxv]

/-- **Ceiling-hit one-step recursion.**  For a high state `v` above the ceiling level
(`C < rnk v`), the exact-level hit mass satisfies the linear recursion
`ceilHit C v = ∑_{k<v} Pker v k · ceilHit C k`.  (One `Pker` step then the first-entrance kernel from
each predecessor; the level filter commutes with the linear expansion.) -/
lemma ceilHit_recursion {C v : ℕ} (hv : C < rnk v) :
    ceilHit C v = ∑ k ∈ Finset.range v, Pker v k * ceilHit C k := by
  classical
  have hnotmem : v ∉ ceilBand C 1 := by
    rw [mem_ceilBand_iff]; omega
  unfold ceilHit
  -- expand each entrance, swap sums
  have hexp : ∀ x, enterBandKer Pker (ceilBand C 1) v x
      = ∑ k ∈ Finset.range v, Pker v k * enterBandKer Pker (ceilBand C 1) k x := by
    intro x; rw [enterBandKer_eq, if_neg hnotmem]
  rw [Finset.sum_congr rfl (fun x _ => hexp x), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]

/-- **Inductive expansion bound.**  Assume a rank-indexed lower bound `β` (extended by `0` below the
ceiling) is available at every predecessor.  Then for `C < rnk v` the exact-level hit mass is at
least the rank-drop pushforward of `β`:
`ceilHit C v ≥ ∑_{d ≤ rnk v} rankDropKer v d · βbar (rnk v − d)`, where `βbar r := if C ≤ r then
β (r − C) else 0`. -/
lemma ceilHit_ge_pushforward {C v : ℕ} (β : ℕ → ℝ) (hv : C < rnk v)
    (hβ0 : ∀ r, 0 ≤ β r)
    (hIH : ∀ k, k < v → (if C ≤ rnk k then β (rnk k - C) else (0:ℝ)) ≤ ceilHit C k) :
    (∑ d ∈ Finset.range (rnk v + 1),
        rankDropKer v d * (if C ≤ rnk v - d then β (rnk v - d - C) else 0))
      ≤ ceilHit C v := by
  classical
  rw [ceilHit_recursion hv]
  rw [← pushforward_rankDrop v (fun d => if C ≤ rnk v - d then β (rnk v - d - C) else 0)]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hkv : k < v := Finset.mem_range.mp hk
  have hkle : rnk k ≤ rnk v := rnk_mono (le_of_lt hkv)
  -- rnk v − (rnk v − rnk k) = rnk k
  have hsub : rnk v - (rnk v - rnk k) = rnk k := by omega
  rw [hsub]
  exact mul_le_mul_of_nonneg_left (hIH k hkv) (Pker_nonneg v k)

/-- **Closing inequality from the subsolution slope.**  Fix `r ≥ 1` and a state `v` with
`rnk v = C + r`.  If the rank-drop law from `v` is a sub-probability (`∑_{d ≤ rnk v} rankDropKer v d
≤ 1`), satisfies the drop-1 minorization `rankDropKer v 1 ≥ η`, has overshoot tail
`∑_{r < d ≤ rnk v} rankDropKer v d ≤ ε r`, and `β` is antitone with the slope condition
`η · (β (r-1) − β r) ≥ ε r · β r`, then the pushforward dominates `β r`. -/
lemma pushforward_ge_beta {C v : ℕ} {η : ℝ} (β ε : ℕ → ℝ) {r : ℕ} (hr : 1 ≤ r)
    (hrv : rnk v = C + r) (hC1 : 1 ≤ C) (hη0 : 0 ≤ η)
    (hβanti : Antitone β) (hβ0 : ∀ s, 0 ≤ β s)
    (htot : 1 ≤ ∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d)
    (hmin1 : η ≤ rankDropKer v 1)
    (htail : ∑ d ∈ (Finset.range (rnk v + 1)).filter (fun d => r < d), rankDropKer v d ≤ ε r)
    (hslope : ε r * β r ≤ η * (β (r-1) - β r)) :
    β r ≤ ∑ d ∈ Finset.range (rnk v + 1),
        rankDropKer v d * (if C ≤ rnk v - d then β (rnk v - d - C) else 0) := by
  classical
  -- abbreviate the summand's β-part as βr (r - d) for d ≤ r and 0 beyond
  set f : ℕ → ℝ := fun d => if C ≤ rnk v - d then β (rnk v - d - C) else 0 with hf
  -- on d ≤ r: f d = β (r - d); on d > r: f d = 0
  have hf_le : ∀ d, d ≤ r → f d = β (r - d) := by
    intro d hd; simp only [hf, hrv]
    rw [if_pos (by omega)]; congr 1; omega
  have hf_gt : ∀ d, r < d → f d = 0 := by
    intro d hd; simp only [hf, hrv]; rw [if_neg (show ¬ C ≤ C + r - d by omega)]
  -- f d ≥ β r for d ≤ r (β antitone), and f d = 0 ≥ 0 for d > r
  have hf_ge_βr : ∀ d, d ∈ Finset.range (rnk v + 1) → β r ≤ f d ∨ r < d := by
    intro d _; rcases le_or_gt d r with hd | hd
    · left; rw [hf_le d hd]; exact hβanti (by omega)
    · right; exact hd
  -- split the pushforward sum into d ≤ r (good) and d > r (overshoot, = 0)
  have hsplit : (∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d * f d)
      = ∑ d ∈ (Finset.range (rnk v + 1)).filter (fun d => ¬ r < d), rankDropKer v d * f d := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (rnk v + 1)) (fun d => ¬ r < d)]
    have hzero : (∑ d ∈ (Finset.range (rnk v + 1)).filter (fun d => ¬¬ r < d),
        rankDropKer v d * f d) = 0 := by
      refine Finset.sum_eq_zero (fun d hd => ?_)
      have : r < d := by have := (Finset.mem_filter.mp hd).2; omega
      rw [hf_gt d this, mul_zero]
    rw [hzero, add_zero]
  rw [hsplit]
  -- the good sum (d ≤ r): ∑ rankDropKer v d · β(r-d)
  set G := (Finset.range (rnk v + 1)).filter (fun d => ¬ r < d) with hG
  have hGval : ∀ d ∈ G, rankDropKer v d * f d = rankDropKer v d * β (r - d) := by
    intro d hd
    have hdr : d ≤ r := by have := (Finset.mem_filter.mp hd).2; omega
    rw [hf_le d hdr]
  rw [Finset.sum_congr rfl hGval]
  -- decompose ∑_{d∈G} p_d β(r-d) = β r · (∑_{d∈G} p_d) + ∑_{d∈G} p_d (β(r-d) - β r)
  have hdecomp : (∑ d ∈ G, rankDropKer v d * β (r - d))
      = β r * (∑ d ∈ G, rankDropKer v d)
        + ∑ d ∈ G, rankDropKer v d * (β (r - d) - β r) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => by ring)
  rw [hdecomp]
  -- ∑_{d∈G} p_d = total − overshoot ≥ 1 − ε r? we only need ≥ 1 − tail. Use total ≤ 1 lower side:
  -- ∑_{d∈G} p_d = total − ∑_{d∉G} p_d, and ∑_{d∉G} p_d = overshoot ≤ ε r.
  have hGmass : (∑ d ∈ G, rankDropKer v d)
      = (∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d)
        - ∑ d ∈ (Finset.range (rnk v + 1)).filter (fun d => r < d), rankDropKer v d := by
    rw [hG]
    have := Finset.sum_filter_add_sum_filter_not (Finset.range (rnk v + 1)) (fun d => r < d)
      (rankDropKer v)
    -- filter (¬ r < d) is the complement of filter (r < d)
    have hcomm : (Finset.range (rnk v + 1)).filter (fun d => ¬ r < d) =
        (Finset.range (rnk v + 1)).filter (fun d => ¬ (r < d)) := rfl
    linarith [this]
  -- excess ≥ η (β(r-1) - β r): keep only d=1 term, drop others (nonneg)
  have h1mem : (1 : ℕ) ∈ G := by
    rw [hG, Finset.mem_filter, Finset.mem_range]; refine ⟨by omega, by omega⟩
  have hexcess_nn : ∀ d ∈ G, 0 ≤ rankDropKer v d * (β (r - d) - β r) := by
    intro d hd
    have hdr : d ≤ r := by have := (Finset.mem_filter.mp hd).2; omega
    exact mul_nonneg (rankDropKer_nonneg v d) (by linarith [hβanti (show r - d ≤ r by omega)])
  have hexcess : η * (β (r-1) - β r) ≤ ∑ d ∈ G, rankDropKer v d * (β (r - d) - β r) := by
    have hsingle : rankDropKer v 1 * (β (r - 1) - β r)
        ≤ ∑ d ∈ G, rankDropKer v d * (β (r - d) - β r) :=
      Finset.single_le_sum hexcess_nn h1mem
    refine le_trans ?_ hsingle
    have hslope_nn : 0 ≤ β (r - 1) - β r := by linarith [hβanti (show r - 1 ≤ r by omega)]
    exact mul_le_mul_of_nonneg_right hmin1 hslope_nn
  -- combine
  have hmass_lb : (1 : ℝ) - ε r ≤ ∑ d ∈ G, rankDropKer v d := by
    rw [hGmass]; linarith [htot, htail]
  -- β r ≤ β r (1 − ε r) + ε r β r ≤ β r · mass + excess
  have hβr_nn : 0 ≤ β r := hβ0 r
  calc β r = β r * (1 - ε r) + ε r * β r := by ring
    _ ≤ β r * (∑ d ∈ G, rankDropKer v d) + η * (β (r-1) - β r) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hmass_lb hβr_nn
        · linarith [hslope]
    _ ≤ β r * (∑ d ∈ G, rankDropKer v d) + ∑ d ∈ G, rankDropKer v d * (β (r - d) - β r) := by
        linarith [hexcess]

/-- **Abstract subsolution comparison (strong induction).**  Suppose `β` is antitone, nonnegative,
with `β 0 ≤ 1` and the slope condition `ε r · β r ≤ η · (β (r-1) − β r)` for all `r ≥ 1`.  Suppose
moreover that at every state `v` with `C < rnk v` the rank-drop law is a (sub)probability summing to
`≥ 1`, has drop-1 mass `≥ η`, and overshoot tail `≤ ε (rnk v − C)`.  Then `β (rnk v − C) ≤ ceilHit C v`
for every `v` with `C ≤ rnk v`. -/
lemma ceilHit_ge_beta {C : ℕ} {η : ℝ} (β ε : ℕ → ℝ) (hC1 : 1 ≤ C) (hη0 : 0 ≤ η)
    (hβanti : Antitone β) (hβ0 : ∀ s, 0 ≤ β s) (hβ01 : β 0 ≤ 1)
    (hslope : ∀ r, 1 ≤ r → ε r * β r ≤ η * (β (r-1) - β r))
    (hfacts : ∀ v, C < rnk v →
        (1 ≤ ∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d)
        ∧ η ≤ rankDropKer v 1
        ∧ (∑ d ∈ (Finset.range (rnk v + 1)).filter (fun d => rnk v - C < d), rankDropKer v d
              ≤ ε (rnk v - C))) :
    ∀ v, C ≤ rnk v → β (rnk v - C) ≤ ceilHit C v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hCv
    rcases eq_or_lt_of_le hCv with heq | hlt
    · -- rnk v = C: ceilHit = 1, β (0) ≤ 1
      rw [← heq, Nat.sub_self]
      rw [ceilHit_of_rnk_eq heq.symm]
      exact hβ01
    · -- C < rnk v
      set r := rnk v - C with hr
      have hr1 : 1 ≤ r := by omega
      have hrv : rnk v = C + r := by omega
      obtain ⟨htot, hmin1, htail⟩ := hfacts v hlt
      -- the inductive hypotheses at predecessors, packaged for ceilHit_ge_pushforward
      have hIH : ∀ k, k < v →
          (if C ≤ rnk k then β (rnk k - C) else (0:ℝ)) ≤ ceilHit C k := by
        intro k hkv
        by_cases hCk : C ≤ rnk k
        · rw [if_pos hCk]; exact ih k hkv hCk
        · rw [if_neg hCk]; exact ceilHit_nonneg C k
      have hpush := ceilHit_ge_pushforward (C := C) (v := v) β hlt hβ0 hIH
      have hbeta := pushforward_ge_beta (C := C) (v := v) (η := η) β ε hr1 hrv hC1 hη0
        hβanti hβ0 htot hmin1 htail (hslope r hr1)
      exact le_trans hbeta hpush

/-! ### The product subsolution `β`

`β r := (∏_{j=1}^{r} (1 + ε j / η))⁻¹`.  Antitone (`≥ 1` factors), `β 0 = 1`, slope condition is an
*equality* `η (β (r-1) − β r) = ε r · β r`, and the uniform lower bound
`β r ≥ exp(−(∑' ε)/η) > 0` via `1 + x ≤ exp x` and `∏ exp = exp ∑`. -/

/-- The product subsolution. -/
noncomputable def betaSub (ε : ℕ → ℝ) (η : ℝ) (r : ℕ) : ℝ :=
  (∏ j ∈ Finset.Icc 1 r, (1 + ε j / η))⁻¹

lemma betaSub_factor_pos {ε : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hε : ∀ j, 0 ≤ ε j) (j : ℕ) :
    0 < 1 + ε j / η := by
  have : 0 ≤ ε j / η := div_nonneg (hε j) hη.le
  linarith

lemma betaSub_prod_pos {ε : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hε : ∀ j, 0 ≤ ε j) (r : ℕ) :
    0 < ∏ j ∈ Finset.Icc 1 r, (1 + ε j / η) :=
  Finset.prod_pos (fun j _ => betaSub_factor_pos hη hε j)

lemma betaSub_pos {ε : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hε : ∀ j, 0 ≤ ε j) (r : ℕ) :
    0 < betaSub ε η r := by
  rw [betaSub]; exact inv_pos.mpr (betaSub_prod_pos hη hε r)

lemma betaSub_zero {ε : ℕ → ℝ} {η : ℝ} : betaSub ε η 0 = 1 := by
  rw [betaSub]; simp

/-- `β` is antitone: each extra factor `≥ 1` shrinks the inverse. -/
lemma betaSub_antitone {ε : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hε : ∀ j, 0 ≤ ε j) :
    Antitone (betaSub ε η) := by
  apply antitone_nat_of_succ_le
  intro r
  rw [betaSub, betaSub]
  apply inv_anti₀ (betaSub_prod_pos hη hε r)
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1)]
  have hfac : 1 ≤ 1 + ε (r+1) / η := by
    have : 0 ≤ ε (r+1) / η := div_nonneg (hε (r+1)) hη.le; linarith
  nlinarith [betaSub_prod_pos hη hε r, hfac]

/-- The slope identity: `η · (β (r-1) − β r) = ε r · β r` for `r ≥ 1`. -/
lemma betaSub_slope {ε : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hε : ∀ j, 0 ≤ ε j) {r : ℕ} (hr : 1 ≤ r) :
    ε r * betaSub ε η r = η * (betaSub ε η (r-1) - betaSub ε η r) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- the defining ratio β(s+1) = β(s) / F, with F = 1 + ε(s+1)/η
  have hps : 0 < ∏ j ∈ Finset.Icc 1 s, (1 + ε j / η) := betaSub_prod_pos hη hε s
  have hfac : 0 < 1 + ε (s+1) / η := betaSub_factor_pos hη hε (s+1)
  set P := ∏ j ∈ Finset.Icc 1 s, (1 + ε j / η) with hP
  have hβs : betaSub ε η s = P⁻¹ := rfl
  have hβs1 : betaSub ε η (s+1) = P⁻¹ * (1 + ε (s+1)/η)⁻¹ := by
    rw [betaSub, Finset.prod_Icc_succ_top (by omega : 1 ≤ s + 1), ← hP, mul_inv]
  rw [hβs, hβs1]
  have hPne : P ≠ 0 := ne_of_gt hps
  have hFne : (1 + ε (s+1)/η) ≠ 0 := ne_of_gt hfac
  have hηne : η ≠ 0 := ne_of_gt hη
  have hsum_ne : ε (1 + s) + η ≠ 0 := by
    have := hε (1 + s); positivity
  have hsum_ne' : η + ε (s + 1) ≠ 0 := by
    have := hε (s+1); positivity
  field_simp
  ring

/-- **Uniform lower bound** `β r ≥ exp(−S/η)` where `S = ∑' ε`.  Via `1 + x ≤ exp x`,
`∏ exp = exp ∑`, and partial-sum `≤ tsum` for the nonnegative summable `ε`. -/
lemma betaSub_ge {ε : ℕ → ℝ} {η : ℝ} (hη : 0 < η) (hε : ∀ j, 0 ≤ ε j)
    (hsum : Summable ε) (r : ℕ) :
    Real.exp (-(∑' j, ε j) / η) ≤ betaSub ε η r := by
  rw [betaSub]
  have hprod_le : (∏ j ∈ Finset.Icc 1 r, (1 + ε j / η))
      ≤ Real.exp ((∑' j, ε j) / η) := by
    calc (∏ j ∈ Finset.Icc 1 r, (1 + ε j / η))
        ≤ ∏ j ∈ Finset.Icc 1 r, Real.exp (ε j / η) := by
          refine Finset.prod_le_prod (fun j _ => (betaSub_factor_pos hη hε j).le) ?_
          intro j _
          have := Real.add_one_le_exp (ε j / η); linarith
      _ = Real.exp (∑ j ∈ Finset.Icc 1 r, ε j / η) := by rw [Real.exp_sum]
      _ ≤ Real.exp ((∑' j, ε j) / η) := by
          apply Real.exp_le_exp.mpr
          rw [← Finset.sum_div]
          have hle : (∑ j ∈ Finset.Icc 1 r, ε j) ≤ ∑' j, ε j :=
            hsum.sum_le_tsum (Finset.Icc 1 r) (fun j _ => hε j)
          gcongr
  have hppos : 0 < ∏ j ∈ Finset.Icc 1 r, (1 + ε j / η) := betaSub_prod_pos hη hε r
  rw [neg_div, Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) hppos]
  exact hprod_le

/-- `rankDropKer v d = 0` for `d > rnk v` (no predecessor can drop the rank by more than `rnk v`). -/
lemma rankDropKer_eq_zero_of_gt {v d : ℕ} (hd : rnk v < d) : rankDropKer v d = 0 := by
  unfold rankDropKer
  refine Finset.sum_eq_zero (fun k hk => ?_)
  exfalso
  have hkv : k < v := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have : rnk v - rnk k = d := (Finset.mem_filter.mp hk).2
  have hkle : rnk k ≤ rnk v := rnk_mono (le_of_lt hkv)
  omega

/-- Total rank-drop mass equals the row sum of `Pker`, hence `= 1` for `2 ≤ v`, `kernelMass v ≠ 0`. -/
lemma rankDropKer_total {v : ℕ} (hv : 2 ≤ v) (hS : kernelMass v ≠ 0) :
    (∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d) = 1 := by
  have h := pushforward_rankDrop v (fun _ => (1:ℝ))
  simp only [mul_one] at h
  rw [← h, ← Pker_mass hv hS]

/-- `rnk v < v` once `10 ≤ v` (`3√v < v ⟺ v > 9`). -/
lemma rnk_lt_self {v : ℕ} (hv : 10 ≤ v) : rnk v < v := by
  have hvR : (10 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have hsqlt : 3 * Real.sqrt (v : ℝ) < (v : ℝ) := by
    have hsq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt (by positivity)
    have hspos : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr (by linarith)
    -- 3√v < v ⟺ 3 < √v (÷√v) ⟸ √v > 3 ⟸ v > 9
    have hs3 : 3 < Real.sqrt (v : ℝ) := by
      have : (3:ℝ)^2 < Real.sqrt (v:ℝ)^2 := by rw [hsq]; nlinarith
      nlinarith [hspos, this]
    nlinarith [hs3, hspos, hsq]
  have : (rnk v : ℝ) < (v : ℝ) := lt_of_le_of_lt (rnk_sqrt_bounds v).1 hsqlt
  exact_mod_cast this

/-- **L3 — rank-only ceiling-level hit lower bound.**  There is `α > 0` so that, eventually in the
ceiling floor `C`, every start `n` of rank `≥ C` hits the exact ceiling level `{rnk = C}` (rather than
overshooting below) with first-entrance mass `≥ α`, uniformly over all heights. -/
theorem Pker_hit_ceiling_level_mass_lower :
    ∃ α : ℝ, 0 < α ∧
      ∀ᶠ C in atTop, ∀ n, C ≤ rnk n →
        α ≤ ∑ x ∈ (ceilBand C 1).filter (fun x => C ≤ rnk x),
              enterBandKer Pker (ceilBand C 1) n x := by
  classical
  -- the banked minorizer η and tail majorant ε
  obtain ⟨η, hηpos, hηev⟩ := Pker_rankDrop_minorization
  obtain ⟨γ, C₀, hγpos, htailev⟩ := Pker_rankDrop_tail_majorant
  -- ε A := C₀ (A+1) e^{−γ A}; summable, nonneg
  set ε : ℕ → ℝ := fun A => C₀ * ((A : ℝ) + 1) * Real.exp (-γ * (A : ℝ)) with hεdef
  have hC₀nn : 0 ≤ C₀ := by
    obtain ⟨v, hv⟩ := htailev.exists
    have hpos : (0:ℝ) ≤ ∑ d ∈ (Finset.range v).filter (0 < ·), rankDropKer v d :=
      Finset.sum_nonneg (fun d _ => rankDropKer_nonneg v d)
    have h1 := le_trans hpos (hv 0)
    push_cast at h1
    have he : (0:ℝ) < Real.exp (-γ * (0:ℝ)) := Real.exp_pos _
    nlinarith [h1, he]
  have hεnn : ∀ A, 0 ≤ ε A := by
    intro A; rw [hεdef]
    have he : (0:ℝ) ≤ Real.exp (-γ * (A:ℝ)) := (Real.exp_pos _).le
    have hA1 : (0:ℝ) ≤ (A:ℝ) + 1 := by positivity
    positivity
  have hεsum : Summable ε := by
    rw [hεdef]
    have h1 : Summable (fun A : ℕ => ((A:ℝ) + 1) * Real.exp (-γ * (A:ℝ))) := by
      have hs := summable_pow_mul_exp_neg (c := γ) hγpos 1
      have hs0 := summable_pow_mul_exp_neg (c := γ) hγpos 0
      have : (fun A : ℕ => ((A:ℝ) + 1) * Real.exp (-γ * (A:ℝ)))
          = (fun A : ℕ => (A:ℝ)^1 * Real.exp (-γ*(A:ℝ))) + (fun A : ℕ => (A:ℝ)^0 * Real.exp (-γ*(A:ℝ))) := by
        funext A; simp [pow_one]; ring
      rw [this]; exact hs.add hs0
    exact (h1.mul_left C₀).congr (fun A => by ring)
  -- the subsolution β and its uniform floor α
  set β : ℕ → ℝ := betaSub ε η with hβ
  refine ⟨Real.exp (-(∑' j, ε j) / η), Real.exp_pos _, ?_⟩
  -- eventual-in-v facts: minorization, tail, mass
  obtain ⟨V₁, hV₁⟩ := eventually_atTop.1 hηev
  obtain ⟨V₂, hV₂⟩ := eventually_atTop.1 htailev
  obtain ⟨V₃, hV₃⟩ := eventually_atTop.1 kernelMass_pos_eventually
  set Vmax := max (max V₁ V₂) (max V₃ 10) with hVmax
  -- choose C large: any v with C < rnk v has v ≥ Vmax (via rnk_ge_of)
  refine eventually_atTop.2 ⟨max (3 * Vmax + 3) 1, fun C hC => ?_⟩
  have hC1 : 1 ≤ C := le_trans (le_max_right _ _) hC
  intro n hn
  -- the per-v hypotheses bundle
  have hfacts : ∀ v, C < rnk v →
      (1 ≤ ∑ d ∈ Finset.range (rnk v + 1), rankDropKer v d)
      ∧ η ≤ rankDropKer v 1
      ∧ (∑ d ∈ (Finset.range (rnk v + 1)).filter (fun d => rnk v - C < d), rankDropKer v d
            ≤ ε (rnk v - C)) := by
    intro v hv
    have hvge : Vmax ≤ v := by
      apply rnk_ge_of (n₀ := Vmax)
      have : 3 * Vmax + 3 ≤ C := le_trans (le_max_left _ _) hC
      omega
    have hv10 : 10 ≤ v := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hvge
    have hv2 : 2 ≤ v := by omega
    have hrltv : rnk v < v := rnk_lt_self hv10
    have hV1le : V₁ ≤ v := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hvge
    have hV2le : V₂ ≤ v := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hvge
    have hV3le : V₃ ≤ v := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hvge
    have hmin := hV₁ v hV1le
    have htail := hV₂ v hV2le (rnk v - C)
    have hSpos := hV₃ v hV3le
    refine ⟨?_, hmin.1, ?_⟩
    · rw [rankDropKer_total hv2 (ne_of_gt hSpos)]
    · -- overshoot tail over range(rnk v+1) = banked tail over range v (extra terms zero)
      refine le_trans (le_of_eq ?_) htail
      apply Finset.sum_subset
      · -- (range (rnk v+1)).filter ⊆ (range v).filter
        intro d hd
        rw [Finset.mem_filter, Finset.mem_range] at hd
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hd.2⟩
      · -- on (range v).filter \ (range (rnk v+1)).filter : rankDropKer = 0
        intro d hd hdnot
        rw [Finset.mem_filter, Finset.mem_range] at hd
        -- d ∈ range v with A < d but d ∉ range(rnk v+1).filter ⟹ rnk v < d
        have hdgt : rnk v < d := by
          by_contra hcon
          rw [not_lt] at hcon
          exact hdnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hd.2⟩)
        exact rankDropKer_eq_zero_of_gt hdgt
  -- run the subsolution comparison
  have hmain := ceilHit_ge_beta (C := C) (η := η) β ε hC1 hηpos.le
    (betaSub_antitone hηpos hεnn) (fun s => (betaSub_pos hηpos hεnn s).le)
    (by rw [hβ, betaSub_zero])
    (fun r hr => by rw [hβ]; exact le_of_eq (betaSub_slope hηpos hεnn hr))
    hfacts n hn
  -- β (rnk n − C) ≥ α
  have hβfloor : Real.exp (-(∑' j, ε j) / η) ≤ β (rnk n - C) := by
    rw [hβ]; exact betaSub_ge hηpos hεnn hεsum _
  calc Real.exp (-(∑' j, ε j) / η) ≤ β (rnk n - C) := hβfloor
    _ ≤ ceilHit C n := hmain
    _ = _ := rfl

#print axioms Pker_hit_ceiling_level_mass_lower

end AnalyticCombinatorics.Ch8.Partitions.Erdos
