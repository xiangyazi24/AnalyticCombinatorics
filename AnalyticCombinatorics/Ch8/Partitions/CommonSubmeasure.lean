import Mathlib

/-!
# TASK T2-value, brick 2.0: the common-submeasure overlap bridge

The variable rank-band engine (`hitVal_cauchy_of_ceilBand_overlap_escape_variable`,
`RankBandEntrance.lean`) consumes a **value-level** overlap
`δ ≤ ∑_{z ∈ slice} min (κ n z) (κ n' z)`.  The banked `overlap_ge_of_minorization`
(`RenewalOverlap.lean`) derives this from a *single-state* minorization `κ n z ≥ η` on a fixed
finite set `S`, which is FALSE for a growing band (the first-entrance landing law spreads over the
whole band, so the per-state mass `max_z κ n z → 0`).

This brick generalizes that bridge: instead of a per-state floor, it consumes a *common submeasure*
`lam : ℕ → ℝ`, a nonnegative function dominated pointwise by *both* kernels on the slice, and
returns `∑ lam ≤ ∑ min`.  The common mass may be spread arbitrarily over the growing band; only its
total `∑ lam ≥ δ` needs to stay uniform.  Trivial: `min (κ n z) (κ n' z) ≥ lam z` pointwise on the
slice, then sum.

NEW file; imports nothing from the banked partition bricks (pure Finset algebra).  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Overlap from a common submeasure (engine-facing, abstract).**  If a nonnegative function `lam`
is dominated pointwise by both kernels `κ n` and `κ n'` on every state of a finite set `S`, then the
overlap of the two kernels over `S` is at least the total mass of `lam`.  Unlike
`overlap_ge_of_minorization`, the common mass may be spread over many states of a growing band; only
its total `∑_{z∈S} lam z` needs to stay uniform.  (We bound the slice sum below by `∑ lam`, using
`min (κ n z) (κ n' z) ≥ lam z` pointwise on `S`.) -/
lemma overlap_ge_of_common_submeasure
    {κ : ℕ → ℕ → ℝ} {S : Finset ℕ} {lam : ℕ → ℝ} {n n' : ℕ} {δ : ℝ}
    (hn : ∀ z ∈ S, lam z ≤ κ n z) (hn' : ∀ z ∈ S, lam z ≤ κ n' z)
    (hmass : δ ≤ ∑ z ∈ S, lam z) :
    δ ≤ ∑ z ∈ S, min (κ n z) (κ n' z) := by
  refine le_trans hmass ?_
  apply Finset.sum_le_sum
  intro z hz
  exact le_min (hn z hz) (hn' z hz)

#print axioms overlap_ge_of_common_submeasure

end AnalyticCombinatorics.Ch8.Partitions.Erdos
