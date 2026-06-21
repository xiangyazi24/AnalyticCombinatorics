import AnalyticCombinatorics.Ch8.Partitions.RankBandEntrance
import AnalyticCombinatorics.Ch8.Partitions.RankDropKer

/-!
# TASK T2-value, brick 2.1: the variable-band escape lemma (abstract conditional core)

The variable rank-band engine consumes an **escape** bound: for the first-entrance kernel into the
ceiling down-set `ceilBand R (A R)`, the mass landing strictly below rank `R` (the "overshoot") is
`≤ e R`, with `e R → 0`.

**Mathematical correction to the R6 design.**  The naive bound "overshoot `≤` the per-step rank-drop
tail `M`" is FALSE.  The overshoot is a *first-entrance* probability; a chain with high holding (small
per-step crossing probability `c(v)`) can overshoot with probability `→ 1` even when each individual
step's deep-crossing mass `a(v)` is tiny (concrete witness: `c(v)=a(v)=ε`, `s(v)=1−ε` gives
`esc = ε + (1−ε)esc = 1`).  The correct, provable, and engine-sufficient statement is **conditional**:
if at every off-band vertex the deep-crossing mass is `≤ M ·` (total crossing mass), then the
first-entrance overshoot is `≤ M`.  This `enterBand_deep_mass_le_of_conditional` closes by the clean
super-solution invariant `esc(v) ≤ M · tot(v)` with `tot ≡ 1` the certain-entrance total.

The remaining analytic input — turning the banked rank-drop tail majorant
(`Pker_rankDrop_tail_majorant`) into the *conditional* deep-crossing bound `a(v) ≤ M · c(v)` — is the
ratio `P(drop > A R | drop ≥ 1)`, which needs the embedded rank-change exit chain (brick 2.2) and the
per-drop minorization `rankDropKer v 1, v 2 ≥ η` (banked `Pker_rankDrop_minorization`) to lower-bound
`c(v) ≥ 2η`.

NEW file; imports the banked engine bricks and the banked tail majorant, does not modify them.
Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **First-entrance deep-mass bound (abstract, conditional form).**  Let `P ≥ 0` and `B` a finite
band, with a predicate `deep` on landed states and `0 ≤ M`.  Suppose at every off-band vertex `v` the
one-step *deep-crossing* mass is `≤ M` times the one-step *total-crossing* mass:

  `∑_{k∈B, deep k} P v k ≤ M · ∑_{k∈B} P v k`.

Then for every off-band start, the first-entrance overshoot (mass on deep band states) is `≤ M`
times the first-entrance total band mass.  In particular, when the chain enters the band with
probability one (`tot ≡ 1`), the overshoot is `≤ M`.

Proof: the super-solution `esc(v) ≤ M · tot(v)` is preserved by the recursion
`esc(v) = a(v) + ∑_{k∉B} P v k · esc(k)`, `tot(v) = c(v) + ∑_{k∉B} P v k · tot(k)`, using `a ≤ M·c`
on the boundary term and the inductive `esc(k) ≤ M·tot(k)` on the off-band continuation. -/
lemma enterBand_deep_mass_le_of_conditional
    {P : ℕ → ℕ → ℝ} {B : Finset ℕ} {deep : ℕ → Prop} [DecidablePred deep]
    {M : ℝ} (hM0 : 0 ≤ M) (hPnn : ∀ n k, 0 ≤ P n k)
    (hPsupp : ∀ m k, m ≤ k → P m k = 0)
    (hcond : ∀ v, v ∉ B →
        ∑ k ∈ B.filter (fun k => deep k), P v k ≤ M * ∑ k ∈ B, P v k)
    {n : ℕ} (hn : n ∉ B) :
    ∑ z ∈ B.filter (fun z => deep z), enterBandKer P B n z
      ≤ M * ∑ z ∈ B, enterBandKer P B n z := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- expansions at the off-band vertex n
    have hexpand : ∀ z, enterBandKer P B n z
        = ∑ k ∈ Finset.range n, P n k * enterBandKer P B k z := by
      intro z; rw [enterBandKer_eq, if_neg hn]
    -- g k := deep-mass from k,  t k := total band mass from k
    set g : ℕ → ℝ := fun k => ∑ z ∈ B.filter (fun z => deep z), enterBandKer P B k z with hgdef
    set t : ℕ → ℝ := fun k => ∑ z ∈ B, enterBandKer P B k z with htdef
    have hLHS : ∑ z ∈ B.filter (fun z => deep z), enterBandKer P B n z
        = ∑ k ∈ Finset.range n, P n k * g k := by
      rw [Finset.sum_congr rfl (fun z _ => hexpand z), Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => by simp only [hgdef, Finset.mul_sum])
    have hRHS : ∑ z ∈ B, enterBandKer P B n z = ∑ k ∈ Finset.range n, P n k * t k := by
      rw [Finset.sum_congr rfl (fun z _ => hexpand z), Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => by simp only [htdef, Finset.mul_sum])
    rw [hLHS, hRHS, Finset.mul_sum]
    -- For in-band predecessors k:  g k = [deep k], t k = 1.  For off-band k: g k ≤ M·t k (IH).
    -- Split the range-n sum into in-band and off-band predecessors.
    have hsplitL : ∑ k ∈ Finset.range n, P n k * g k
        = (∑ k ∈ (Finset.range n).filter (fun k => k ∈ B), P n k * g k)
          + ∑ k ∈ (Finset.range n).filter (fun k => k ∉ B), P n k * g k := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun k => k ∈ B)]
    have hsplitR : ∑ k ∈ Finset.range n, M * (P n k * t k)
        = (∑ k ∈ (Finset.range n).filter (fun k => k ∈ B), M * (P n k * t k))
          + ∑ k ∈ (Finset.range n).filter (fun k => k ∉ B), M * (P n k * t k) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun k => k ∈ B)]
    rw [hsplitL, hsplitR]
    refine add_le_add ?_ ?_
    · -- in-band part:  ∑_{k∈B} P n k · g k = a(n) ≤ M·c(n) = ∑_{k∈B} M·(P n k · 1)
      -- g k = [deep k] for k ∈ B
      have hin_g : ∀ k ∈ (Finset.range n).filter (fun k => k ∈ B),
          P n k * g k = if deep k then P n k else 0 := by
        intro k hk
        have hkB : k ∈ B := (Finset.mem_filter.mp hk).2
        have hval : ∀ z, enterBandKer P B k z = if z = k then 1 else 0 := by
          intro z; rw [enterBandKer_eq, if_pos hkB]
        have hgk : g k = if deep k then (1:ℝ) else 0 := by
          simp only [hgdef]
          rw [Finset.sum_congr rfl (fun z _ => hval z)]
          by_cases hkd : deep k
          · rw [if_pos hkd, Finset.sum_ite_eq' (B.filter (fun z => deep z)) k (fun _ => (1:ℝ)),
              if_pos (Finset.mem_filter.mpr ⟨hkB, hkd⟩)]
          · rw [if_neg hkd]
            refine Finset.sum_eq_zero (fun z hz => ?_)
            rw [if_neg]; rintro rfl; exact hkd (Finset.mem_filter.mp hz).2
        rw [hgk]; by_cases hkd : deep k <;> simp [hkd]
      have hin_t : ∀ k ∈ (Finset.range n).filter (fun k => k ∈ B),
          M * (P n k * t k) = M * P n k := by
        intro k hk
        have hkB : k ∈ B := (Finset.mem_filter.mp hk).2
        have hval : ∀ z, enterBandKer P B k z = if z = k then 1 else 0 := by
          intro z; rw [enterBandKer_eq, if_pos hkB]
        have htk1 : t k = 1 := by
          simp only [htdef]
          rw [Finset.sum_congr rfl (fun z _ => hval z),
            Finset.sum_ite_eq' B k (fun _ => (1:ℝ)), if_pos hkB]
        rw [htk1, mul_one]
      rw [Finset.sum_congr rfl hin_g, Finset.sum_congr rfl hin_t]
      -- support: P n k = 0 for k ≥ n, so band sums restrict to range-n ∩ B exactly.
      -- deep LHS over (range n ∩ B):  ∑ [deep] P n  =  ∑_{B.filter deep} P n
      have hLeq : (∑ k ∈ (Finset.range n).filter (fun k => k ∈ B), (if deep k then P n k else 0))
          = ∑ k ∈ B.filter (fun k => deep k), P n k := by
        rw [← Finset.sum_filter]
        apply Finset.sum_subset_zero_on_sdiff
        · -- (range n ∩ B).filter deep ⊆ B.filter deep
          intro k hk
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hk
          exact Finset.mem_filter.mpr ⟨hk.1.2, hk.2⟩
        · -- on the sdiff (k ∈ B.filter deep, k ∉ range n) we have k ≥ n ⟹ P n k = 0
          intro k hk
          rw [Finset.mem_sdiff, Finset.mem_filter] at hk
          have hkn : n ≤ k := by
            by_contra h; push_neg at h
            exact hk.2 (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr h, hk.1.1⟩, hk.1.2⟩)
          exact hPsupp n k hkn
        · intro k _; rfl
      -- total RHS over (range n ∩ B):  ∑ M·(P n) = M·∑_{B} P n
      have hReq : (∑ k ∈ (Finset.range n).filter (fun k => k ∈ B), M * P n k)
          = M * ∑ k ∈ B, P n k := by
        rw [← Finset.mul_sum]
        congr 1
        apply Finset.sum_subset_zero_on_sdiff
        · intro k hk
          rw [Finset.mem_filter, Finset.mem_range] at hk; exact hk.2
        · intro k hk
          rw [Finset.mem_sdiff, Finset.mem_filter] at hk
          have hkn : n ≤ k := by
            by_contra h; push_neg at h
            exact hk.2 ⟨Finset.mem_range.mpr h, hk.1⟩
          exact hPsupp n k hkn
        · intro k _; rfl
      rw [hLeq, hReq]
      exact hcond n hn
    · -- off-band part: termwise IH
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hkn : k < n := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      have hkB : k ∉ B := (Finset.mem_filter.mp hk).2
      have hih := ih k hkn hkB
      have hPk : 0 ≤ P n k := hPnn n k
      calc P n k * g k ≤ P n k * (M * t k) := mul_le_mul_of_nonneg_left hih hPk
        _ = M * (P n k * t k) := by ring

#print axioms enterBand_deep_mass_le_of_conditional

end AnalyticCombinatorics.Ch8.Partitions.Erdos
