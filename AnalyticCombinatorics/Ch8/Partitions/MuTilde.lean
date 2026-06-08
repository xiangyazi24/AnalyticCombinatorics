import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.PartitionRenewal
import AnalyticCombinatorics.Ch8.Partitions.MassRateApprox2

/-!
# The smooth-rank conditional drift `μ̃` and its chain-drift identity

For the killed Erdős predecessor chain (`Pker n k = erdosWeight n (n−k)/kernelMass n`), the
martingale coordinate is the smooth rank `ρ(n) = 3√n`.  The one-step conditional decrement is

  `μ̃(n) = E_{k∼Pker(n,·)}[ρ(n) − ρ(k)] = 3 ∑_k Pker(n,k)(√n − √k)`.

This file defines `μ̃` via the predecessor (decrement) sum and records the identity tying it to the
chain drift through the reflection `k ↦ n−k` (`Pker_sum_mul`).  The two-term expansion
`μ̃(n) = μ̄ + μA/√n + O(1/n)` (the input to `two_term_local_lip`) is built in subsequent files from
the banked moment asymptotics (`sigmaMoment_one_two_term`, `sigmaMoment_two_asymp_weak`,
`sigmaMoment_le_power_sharp 3`) and the kernel-mass rate (`kernelMass → 1`).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The smooth-rank drop `3(√n − √(n−m))` from state `n` to predecessor value `n−m`
(decrement `m`). -/
noncomputable def rhoDrop (n m : ℕ) : ℝ :=
  3 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))

/-- The (unnormalized) drift numerator `∑_{m=1}^{n-1} erdosWeight n m · ρ-drop`. -/
noncomputable def muNum (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * rhoDrop n m

/-- The smooth-rank conditional drift `μ̃(n) = muNum n / kernelMass n`. -/
noncomputable def muTilde (n : ℕ) : ℝ := muNum n / kernelMass n

/-- **Chain-drift identity**: `μ̃(n) = ∑_k Pker(n,k)·3(√n − √k)` — the genuine one-step
smooth-rank conditional decrement of the killed predecessor chain. -/
lemma muTilde_eq_drift {n : ℕ} (hn : 2 ≤ n) :
    muTilde n
      = ∑ k ∈ Finset.range n, Pker n k * (3 * (Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ))) := by
  rw [Pker_sum_mul n hn (fun k => 3 * (Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ)))]
  unfold muTilde muNum rhoDrop
  rfl

end AnalyticCombinatorics.Ch8.Partitions.Erdos
