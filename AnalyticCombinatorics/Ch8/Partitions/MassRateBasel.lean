import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateLambert

/-!
# Mass-rate campaign: Basel-scaled sum and the kernel split (brick-22 prerequisites)

`Σ'_{k≥1} 1/(tk)² = (π²/6)/t²` and `boseKernel x = 1/x² + boseReg0 x`.  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The kernel split (definitional). -/
lemma boseKernel_eq_inv_sq_add_reg (x : ℝ) :
    boseKernel x = 1 / x ^ 2 + boseReg0 x := by
  rw [boseReg0]
  ring

/-- Basel, in the `ℕ`-indexed guarded form: `Σ'_{k≥1} 1/k² = π²/6`. -/
lemma tsum_if_inv_sq :
    (∑' k : ℕ, if k = 0 then 0 else 1 / ((k : ℝ)) ^ 2) = Real.pi ^ 2 / 6 := by
  have hb := hasSum_zeta_two
  rw [← hb.tsum_eq]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]

/-- Basel scaled: `Σ'_{k≥1} 1/(tk)² = (π²/6)/t²` for `t ≠ 0`. -/
lemma tsum_if_inv_sq_scaled {t : ℝ} (ht : t ≠ 0) :
    (∑' k : ℕ, if k = 0 then 0 else 1 / (t * (k : ℝ)) ^ 2)
      = (Real.pi ^ 2 / 6) / t ^ 2 := by
  have hfact : ∀ k : ℕ, (if k = 0 then 0 else 1 / (t * (k : ℝ)) ^ 2)
      = (1 / t ^ 2) * (if k = 0 then 0 else 1 / ((k : ℝ)) ^ 2) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp
    · rw [if_neg hk, if_neg hk]
      field_simp
  calc (∑' k : ℕ, if k = 0 then 0 else 1 / (t * (k : ℝ)) ^ 2)
      = ∑' k : ℕ, (1 / t ^ 2) * (if k = 0 then 0 else 1 / ((k : ℝ)) ^ 2) :=
        tsum_congr hfact
    _ = (1 / t ^ 2) * ∑' k : ℕ, (if k = 0 then 0 else 1 / ((k : ℝ)) ^ 2) :=
        tsum_mul_left
    _ = (Real.pi ^ 2 / 6) / t ^ 2 := by
        rw [tsum_if_inv_sq]
        ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
