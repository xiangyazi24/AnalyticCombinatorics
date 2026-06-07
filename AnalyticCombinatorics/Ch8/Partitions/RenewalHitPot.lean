import Mathlib

/-!
# R7 renewal route: well-founded `Hit`/`Pot` potentials

The banked spine lemmas (`rec_iter_bound`, `pot_le_block_sum_of_leave`) take the `Hit`/`Pot`
fixed-point equations as hypotheses.  This file constructs the actual functions by well-founded
recursion on `n` (the kernel `P n k` is summed over `Finset.range n`, so every recursive call is on
`k < n`).  We sum over `(Finset.range n).attach` so each summand carries the membership proof
`k ∈ range n` (hence `k < n`) needed for termination, then recover the plain-`range` defining
equations via `Finset.sum_attach`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Harmonic extension to the cutoff: `Hit J φ n = φ n` below the cutoff `rank n < J`, else the
`P`-average of `Hit` over predecessors. -/
noncomputable def hitVal (P : ℕ → ℕ → ℝ) (rank : ℕ → ℕ) (J : ℕ) (φ : ℕ → ℝ) : ℕ → ℝ
  | n =>
    if rank n < J then φ n
    else ∑ k ∈ (Finset.range n).attach, P n k.1 * hitVal P rank J φ k.1
  termination_by n => n
  decreasing_by exact Finset.mem_range.mp k.2

/-- The accumulated residual potential along the chain to the cutoff. -/
noncomputable def potVal (P : ℕ → ℕ → ℝ) (rank : ℕ → ℕ) (J : ℕ) (e : ℕ → ℝ) : ℕ → ℝ
  | n =>
    if rank n < J then 0
    else e (rank n) + ∑ k ∈ (Finset.range n).attach, P n k.1 * potVal P rank J e k.1
  termination_by n => n
  decreasing_by exact Finset.mem_range.mp k.2

lemma hitVal_eq (P : ℕ → ℕ → ℝ) (rank : ℕ → ℕ) (J : ℕ) (φ : ℕ → ℝ) (n : ℕ) :
    hitVal P rank J φ n
      = if rank n < J then φ n
        else ∑ k ∈ Finset.range n, P n k * hitVal P rank J φ k := by
  rw [hitVal]
  by_cases h : rank n < J
  · simp [h]
  · rw [if_neg h, if_neg h, Finset.sum_attach (Finset.range n)
      (fun k => P n k * hitVal P rank J φ k)]

lemma potVal_eq (P : ℕ → ℕ → ℝ) (rank : ℕ → ℕ) (J : ℕ) (e : ℕ → ℝ) (n : ℕ) :
    potVal P rank J e n
      = if rank n < J then 0
        else e (rank n) + ∑ k ∈ Finset.range n, P n k * potVal P rank J e k := by
  rw [potVal]
  by_cases h : rank n < J
  · simp [h]
  · rw [if_neg h, if_neg h, Finset.sum_attach (Finset.range n)
      (fun k => P n k * potVal P rank J e k)]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
