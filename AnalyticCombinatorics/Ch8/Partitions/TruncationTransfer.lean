import AnalyticCombinatorics.Ch8.Partitions.OccupationTransfer

/-!
# Truncation transfer (renewal route B, Layer-2 steps A & C)

The Erdős rank-difference kernel is soft/nonlocal, but its rank-drop tail is *exponential*
(`RankDropKer.Pker_rankDrop_tail_majorant`, `γ = C/60`).  The Layer-2 block-heat lower bound is
therefore proved for a *truncated* kernel (jumps capped at `L_m ≍ log m`, mass renormalized) and
transferred back to the real kernel via the banked `OccupationTransfer.occupation_transfer`
(`L¹`-distance `t·ε` over a horizon).  This file banks the two kernel-agnostic, finite-sum bridges:

* `normalize_truncate_L1_eq_two_tail` — the per-row `L¹` distance between a probability row and its
  normalized truncation `P' = P·1_Good/q` is exactly `2·τ`, where `τ` is the truncated tail mass.
* `truncated_block_heat_transfer` — a truncated block-heat lower bound `c0/√(M+1)` transfers to the
  real kernel as `c0/(2√(M+1))`, provided the cumulative `L¹` error `(∑_{t<M} t)·ε ≤ c0/(2√(M+1))`.

(Route + constants from ChatGPT ac2 R9, verified against the repo's `occupation_transfer` /
`Pker_rankDrop_tail_majorant`.)
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Normalize-truncate `L¹` identity.**  If `P` is a probability row, `q = ∑ P·1_Good` the kept
mass, `τ = ∑ P·1_¬Good` the discarded tail, and `P' = P·1_Good/q` the renormalized truncation, then
`∑_z |P z − P' z| = 2τ`. -/
lemma normalize_truncate_L1_eq_two_tail
    (P : α → ℝ) (Good : α → Prop) [DecidablePred Good]
    (P' : α → ℝ) (τ q : ℝ)
    (hPnn : ∀ z, 0 ≤ P z) (hPsum : ∑ z, P z = 1)
    (hτ : τ = ∑ z, P z * (if Good z then 0 else 1))
    (hq : q = ∑ z, P z * (if Good z then 1 else 0))
    (hqpos : 0 < q)
    (hP' : ∀ z, P' z = if Good z then P z / q else 0) :
    (∑ z, |P z - P' z|) = 2 * τ := by
  have hqle1 : q ≤ 1 := by
    rw [hq]
    calc ∑ z, P z * (if Good z then (1 : ℝ) else 0)
        ≤ ∑ z, P z := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          have hind : (if Good z then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
          have hml := mul_le_mul_of_nonneg_left hind (hPnn z)
          linarith [hml, mul_one (P z)]
      _ = 1 := hPsum
  have hqτ : q + τ = 1 := by
    have hsum : q + τ = ∑ z, P z := by
      rw [hq, hτ, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      split_ifs <;> ring
    rw [hsum, hPsum]
  have key : (∑ z, |P z - P' z|)
      = (1 - q) / q * (∑ z, P z * (if Good z then 1 else 0))
        + (∑ z, P z * (if Good z then 0 else 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [hP' z]
    by_cases h : Good z
    · simp only [h, if_true, mul_one, mul_zero, add_zero]
      have hle : P z - P z / q ≤ 0 := by
        rw [sub_nonpos, le_div_iff₀ hqpos]; nlinarith [hPnn z, hqle1]
      rw [abs_of_nonpos hle]; field_simp; ring
    · simp only [h, if_false, mul_zero, mul_one, zero_add, sub_zero]
      exact abs_of_nonneg (hPnn z)
  rw [key, ← hq, ← hτ, div_mul_cancel₀ (1 - q) hqpos.ne']
  linarith [hqτ]

/-- **Truncated block-heat transfer.**  A truncated-kernel block-heat lower bound `c0/√(M+1)`
transfers to the real kernel as `c0/(2√(M+1))`, provided the cumulative `L¹` transfer error
`(∑_{t<M} t)·ε` is at most `c0/(2√(M+1))`.  Consumes the banked `occupation_transfer`. -/
theorem truncated_block_heat_transfer
    (K Ktr : α → α → ℝ) (μ0 : α → ℝ) (D : α → ℝ)
    (W c0 ε : ℝ) (M : ℕ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hKtrnn : ∀ x z, 0 ≤ Ktr x z) (hKtrsum : ∀ x, ∑ z, Ktr x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hclose : ∀ x, (∑ z, |K x z - Ktr x z|) ≤ ε)
    (htrunc :
      c0 / Real.sqrt ((M : ℝ) + 1)
        ≤ ∑ t ∈ Finset.range M,
            ∑ x, distPow Ktr μ0 t x * (if |D x| ≤ W then (1 : ℝ) else 0))
    (herr :
      (∑ t ∈ Finset.range M, (t : ℝ)) * ε
        ≤ c0 / (2 * Real.sqrt ((M : ℝ) + 1))) :
    c0 / (2 * Real.sqrt ((M : ℝ) + 1))
      ≤ ∑ t ∈ Finset.range M,
          ∑ x, distPow K μ0 t x * (if |D x| ≤ W then (1 : ℝ) else 0) := by
  have htrans :=
    occupation_transfer K Ktr μ0 D W ε M
      hKnn hKsum hKtrnn hKtrsum hμ0nn hμ0sum hclose
  have hsqrtpos : (0 : ℝ) < Real.sqrt ((M : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hrel : 2 * (c0 / (2 * Real.sqrt ((M : ℝ) + 1))) = c0 / Real.sqrt ((M : ℝ) + 1) := by
    field_simp
  linarith [htrunc, herr, htrans, hrel]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
