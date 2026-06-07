import Mathlib

/-!
# R7 Fact B via Doeblin: the scalar recursion solver for the windowed ITER

The deterministic coupling ITER reduces the unmatched-mass `u_t` to the scalar recursion
`u_{t+1} ≤ q·u_t + δ·e_t`.  This file solves it in closed form:

  `u m ≤ q^m · u 0 + δ · ∑_{t<m} q^{m−(t+1)} · e t`.

Pure induction on `m`.  Combined with `u_0 = 1`, `q = 1 − δ`, and the overlap `≥ 1 − u_m`, this yields the
`m`-step terminal-law overlap bound `overlap ≥ 1 − (1−δ)^m − δ·∑ (1−δ)^{m−t−1} e_t`.  Opus-authored
(construction from ChatGPT R3).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Closed form for the contraction-with-forcing recursion `u (t+1) ≤ q·u t + δ·e t` (`0 ≤ q`,
`0 ≤ δ`). -/
lemma scalar_rec_solve {u e : ℕ → ℝ} {q δ : ℝ} (hq : 0 ≤ q)
    (hrec : ∀ t, u (t + 1) ≤ q * u t + δ * e t) :
    ∀ m : ℕ, u m ≤ q ^ m * u 0 + δ * ∑ t ∈ Finset.range m, q ^ (m - (t + 1)) * e t := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    set S := ∑ t ∈ Finset.range m, q ^ (m - (t + 1)) * e t with hS
    have hstep : u (m + 1) ≤ q * u m + δ * e m := hrec m
    have hmul2 : q * u m ≤ q ^ m * q * u 0 + δ * (q * S) := by
      rw [show q ^ m * q * u 0 + δ * (q * S) = q * (q ^ m * u 0 + δ * S) from by ring]
      exact mul_le_mul_of_nonneg_left ih hq
    have hsum : ∑ t ∈ Finset.range (m + 1), q ^ (m + 1 - (t + 1)) * e t = q * S + e m := by
      rw [hS, Finset.sum_range_succ]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mem_range] at ht
        have h1 : m + 1 - (t + 1) = (m - (t + 1)) + 1 := by omega
        rw [h1, pow_succ]; ring
      · simp
    rw [hsum, pow_succ, mul_add]
    linarith [hstep, hmul2]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
