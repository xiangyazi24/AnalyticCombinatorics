import AnalyticCombinatorics.Ch8.Partitions.DoeblinOverlap

/-!
# R7 Fact B via Doeblin: the pairwise oscillation contraction

The core contraction step: two points `i, j` whose (iterated) transition laws `Q i ·`, `Q j ·` overlap
by `≥ δ` over a common support `T`, and which are each `η`-approximately `Q`-harmonic, satisfy
`|u i − u j| ≤ (1−δ)·W + 2η`, where `W` bounds the oscillation of `u` on `T` (via a band `[lo, lo+W]`).
This is the deterministic heart of the renewal oscillation contraction; the `δ` comes from the
finite-time Doeblin overlap (the remaining hard analytic input).  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Pairwise contraction.** Overlapping-kernel averages of a banded function, each approximately
harmonic, are within `(1−δ)·W + 2η`. -/
lemma pair_contract {u : ℕ → ℝ} {Q : ℕ → ℕ → ℝ} {i j : ℕ} {T : Finset ℕ} {δ η lo W : ℝ}
    (hQi_m : ∑ k ∈ T, Q i k = 1) (hQj_m : ∑ k ∈ T, Q j k = 1)
    (hov : δ ≤ ∑ k ∈ T, min (Q i k) (Q j k))
    (hband : ∀ k ∈ T, lo ≤ u k ∧ u k ≤ lo + W) (hW : 0 ≤ W)
    (hηi : |u i - ∑ k ∈ T, Q i k * u k| ≤ η)
    (hηj : |u j - ∑ k ∈ T, Q j k * u k| ≤ η) :
    |u i - u j| ≤ (1 - δ) * W + 2 * η := by
  have hmid : |∑ k ∈ T, Q i k * u k - ∑ k ∈ T, Q j k * u k| ≤ (1 - δ) * W :=
    doeblin_average_diff_bound hQi_m hQj_m hov hband hW
  have htri1 : |u i - u j|
      ≤ |u i - ∑ k ∈ T, Q i k * u k| + |∑ k ∈ T, Q i k * u k - u j| := abs_sub_le _ _ _
  have htri2 : |∑ k ∈ T, Q i k * u k - u j|
      ≤ |∑ k ∈ T, Q i k * u k - ∑ k ∈ T, Q j k * u k|
        + |∑ k ∈ T, Q j k * u k - u j| := abs_sub_le _ _ _
  have hηj' : |∑ k ∈ T, Q j k * u k - u j| ≤ η := by rw [abs_sub_comm]; exact hηj
  linarith [hmid, hηi, hηj', htri1, htri2]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
