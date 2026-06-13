import AnalyticCombinatorics.Ch8.Partitions.CeilingValueStep
import AnalyticCombinatorics.Ch8.Partitions.CeilingHit
import AnalyticCombinatorics.Ch8.Partitions.RenewalOverlap

/-!
# TASK L4 (R8 elementary route): same-ceiling value overlap via the divisor-self bound `σ(m) ≥ m`

The variable rank-band engine needs a positive in-band overlap (L4): for two starts `x, y` at the
same ceiling rank `T = R + A R`, the first-entrance laws into the band `ceilBand R (A R)` overlap by
`≥ β` on the in-band slice `{R ≤ rnk z}`.  By the banked one-step reduction
`min_Pker_le_min_enterBandKer_sum` this reduces to a positive overlap of the **one-step** predecessor
laws `Pker x ·`, `Pker y ·` on the slice.

R8's elementary idea (`/tmp/ac_a_uniform.txt`): a single **common value window**
`W_T = [ (T+1)²/9 − 2T , T²/9 − T ] ∩ ℕ` (length `~7T/9`) sits below every ceiling-rank value `x`,
inside the engine slice, and carries `Pker x z ≥ c/T` for EVERY same-ceiling `x` and `z ∈ W_T`.
The lower bound uses ONLY the trivial divisor-self bound `σ(x−z) ≥ x−z ≥ T` (no two-point divisor
estimate, no `KernelWindow`).  A constant minorant `η = c/T` on `S = W_T` with `|W_T| ≥ q·T` gives
overlap `≥ (c/T)(q·T) = cq =: β > 0` via the banked `overlap_ge_of_minorization`.

NEW file; imports the banked bricks, does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ## Brick 1 — the divisor-self bound `σ(m) ≥ m`. -/

/-- **Divisor-self lower bound.**  `m ≤ σ(m)` for `1 ≤ m`: the divisor `m ∣ m` is a single term of
the nonnegative divisor sum `σ(m) = ∑_{d ∣ m} d`. -/
lemma sigmaR_ge_self {m : ℕ} (hm : 1 ≤ m) : (m : ℝ) ≤ Sigma.sigmaR m := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  have hmem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have h := Finset.single_le_sum (f := fun d : ℕ => (d : ℝ))
    (fun d _ => Nat.cast_nonneg d) hmem
  simpa using h

#print axioms sigmaR_ge_self

end AnalyticCombinatorics.Ch8.Partitions.Erdos
