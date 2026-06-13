import AnalyticCombinatorics.Ch8.Partitions.RankBandEntrance

/-!
# TASK T2-ceiling, L2: factoring entrance through the ceiling level

The ceiling-level regeneration route factors the first-entrance law into the growing band
`B = ceilBand R (A R)` (the down-set `{rnk < C}`, `C = R + A R`) through the **ceiling level**
`L = {rnk = C}`.  The chain from a high start `n` (`rnk n ≥ C`) descends; the first time it reaches
the *larger* set `ceilBand C 1 = {rnk ≤ C}` it lands either at the ceiling level `L` (`rnk = C`) or
*overshoots* directly into `B` (`rnk < C`).  Keeping only the level-`L` landings gives the
inequality this file proves:

  `∑_{x ∈ L} enterBandKer Pker (ceilBand C 1) n x · enterBandKer Pker B x z
      ≤ enterBandKer Pker B n z`.

The engine consumes this to write the full entrance law from `n` as a *mixture* over ceiling-level
states (weights `a x = enterBandKer Pker (ceilBand C 1) n x`, continuation kernel
`K x = enterBandKer Pker B x`), feeding the mixture-overlap bridge `L1`.

The work is the **first-entrance tower identity** `enterBandKer_tower`: for `B ⊆ B'`,
`enterBandKer P B n z = ∑_{x ∈ B'} enterBandKer P B' n x · enterBandKer P B x z`
(strong Markov at the first hit of `B'`).  Restricting the `x`-sum from `B' = ceilBand C 1` to the
level `L ⊆ B'` and discarding the nonnegative overshoot terms gives L2.

NEW file; imports the banked entrance kernel, does not modify it.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {P : ℕ → ℕ → ℝ}

/-- **First-entrance tower identity.**  If `B ⊆ B'` and `P` is a strict predecessor kernel
(`P m k = 0` for `k ≥ m`), then entering the smaller band `B` factors through the first hit of the
larger band `B'`:

  `enterBandKer P B n z = ∑_{x ∈ B'} enterBandKer P B' n x · enterBandKer P B x z`.

Strong Markov property at the first entrance time of `B'`.  Proved by strong induction on `n`:
if `n ∈ B'` the first hit is `n` itself (point mass) and the sum collapses; otherwise one `P`-step
plus the inductive hypothesis at every predecessor `k < n`. -/
lemma enterBandKer_tower {B B' : Finset ℕ} (hBB' : B ⊆ B')
    (hPsupp : ∀ m k, m ≤ k → P m k = 0) (n z : ℕ) :
    enterBandKer P B n z
      = ∑ x ∈ B', enterBandKer P B' n x * enterBandKer P B x z := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h' : n ∈ B'
    · -- first hit is n: enterBandKer P B' n x = [x = n], sum collapses
      have hpt : ∀ x, enterBandKer P B' n x * enterBandKer P B x z
          = if x = n then enterBandKer P B n z else 0 := by
        intro x
        rw [enterBandKer_eq (P := P) (B := B') n x, if_pos h']
        by_cases hx : x = n
        · rw [if_pos hx, one_mul, hx, if_pos rfl]
        · rw [if_neg hx, zero_mul, if_neg hx]
      rw [Finset.sum_congr rfl (fun x _ => hpt x),
        Finset.sum_ite_eq' B' n (fun _ => enterBandKer P B n z), if_pos h']
    · -- n ∉ B', hence n ∉ B; one P-step + IH
      have hB : n ∉ B := fun hc => h' (hBB' hc)
      -- LHS expansion
      have hLHS : enterBandKer P B n z = ∑ k ∈ Finset.range n, P n k * enterBandKer P B k z := by
        rw [enterBandKer_eq, if_neg hB]
      -- RHS: expand enterBandKer P B' n x, swap sums, apply IH per k
      have hRHS : (∑ x ∈ B', enterBandKer P B' n x * enterBandKer P B x z)
          = ∑ k ∈ Finset.range n,
              P n k * (∑ x ∈ B', enterBandKer P B' k x * enterBandKer P B x z) := by
        have hxexp : ∀ x, enterBandKer P B' n x * enterBandKer P B x z
            = ∑ k ∈ Finset.range n, P n k * enterBandKer P B' k x * enterBandKer P B x z := by
          intro x
          rw [enterBandKer_eq (P := P) (B := B') n x, if_neg h', Finset.sum_mul]
        rw [Finset.sum_congr rfl (fun x _ => hxexp x), Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => by ring)
      rw [hRHS]
      rw [hLHS]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [ih k (Finset.mem_range.mp hk)]

/-- **L2 — factor entrance through the ceiling level.**  Let `C = R + A R`, `B = ceilBand R (A R)`
(`= {rnk < C}`), and `L = (ceilBand C 1).filter (C ≤ rnk ·)` (`= {rnk = C}`).  For any high start
`n` with `C ≤ rnk n`, the part of the first-entrance law into `B` that first passes through the
ceiling level `L` is bounded by the full first-entrance law:

  `∑_{x ∈ L} enterBandKer Pker (ceilBand C 1) n x · enterBandKer Pker B x z
      ≤ enterBandKer Pker B n z`.

(Overshoot landings — where the chain jumps from `rnk ≥ C` directly into `B = {rnk < C}` — are the
discarded nonnegative terms of the tower identity over `ceilBand C 1`.) -/
theorem enterBandKer_factor_through_ceiling_level (R : ℕ) (A : ℕ → ℕ) (n z : ℕ)
    (hn : R + A R ≤ rnk n) :
    ∑ x ∈ (ceilBand (R + A R) 1).filter (fun x => R + A R ≤ rnk x),
        enterBandKer Pker (ceilBand (R + A R) 1) n x
          * enterBandKer Pker (ceilBand R (A R)) x z
      ≤ enterBandKer Pker (ceilBand R (A R)) n z := by
  classical
  set C := R + A R with hC
  -- B = ceilBand R (A R) = {rnk < C}; B' = ceilBand C 1 = {rnk < C+1} = {rnk ≤ C}; B ⊆ B'
  have hBB' : ceilBand R (A R) ⊆ ceilBand C 1 := by
    intro x hx
    rw [mem_ceilBand_iff] at hx ⊢
    omega
  -- the tower identity over B' = ceilBand C 1
  have htower := enterBandKer_tower (P := Pker) (B := ceilBand R (A R)) (B' := ceilBand C 1)
    hBB' Pker_supp n z
  rw [htower]
  -- restrict the B'-sum to its level-C filter; discard nonnegative overshoot terms
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro x _ _
    exact mul_nonneg
      (enterBandKer_nonneg (fun a b => Pker_nonneg a b) n x)
      (enterBandKer_nonneg (fun a b => Pker_nonneg a b) x z)

#print axioms enterBandKer_tower
#print axioms enterBandKer_factor_through_ceiling_level

end AnalyticCombinatorics.Ch8.Partitions.Erdos
