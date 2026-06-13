import AnalyticCombinatorics.Ch8.Partitions.HitValBound
import AnalyticCombinatorics.Ch8.Partitions.DoeblinOverlap
import AnalyticCombinatorics.Ch8.Partitions.TailBand
import AnalyticCombinatorics.Ch8.Partitions.StepContraction
import AnalyticCombinatorics.Ch8.Partitions.TailOscConverge
import AnalyticCombinatorics.Ch8.Partitions.ErdosConcrete

/-!
# TASK 11: the first-entrance (run-until-hit) rank-band Doeblin engine

The fixed-step-count overlap reductions (`ErdosAlignment`, `DoeblinWalls`) are *false* for far-apart
high ranks (rank drops by `O(1)` per step, so a rank-`1000R` chain and a rank-`1001R` chain have
disjoint `L`-step laws for any fixed `L`; see `HANDOFF/TASK9-gap.md`).  This file builds the correct
device: the **first-entrance kernel** `enterBandKer P B`, which runs the chain *until* it enters a
finite rank band `B` — variable hitting time, not a fixed step count.  Two chains starting from very
different heights both descend *through* the band, and their first-entrance laws overlap.

Steps A–D (this file) are deterministic and reuse the banked Doeblin contraction
(`doeblin_average_diff_bound`) and the banked tail-oscillation engine (`tailOsc`,
`tendsto_zero_of_step_contraction`, `tendsto_of_tail_osc_to_zero`); they do **not** depend on the
hard analytic overlap sublemma (Step E).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ## Step A — the first-entrance kernel -/

/-- **First-entrance kernel.**  `enterBandKer P B n z` is the probability that a `P`-chain started at
`n`, run until it first enters the finite set `B`, lands at `z`.  If `n ∈ B` the chain is already in
the band (point mass at `n`); otherwise it takes one `P`-step to a predecessor `k < n` and
continues.  Well-founded on `k < n` (same structure as `hitVal`, since `P n k` is summed over
`Finset.range n`). -/
noncomputable def enterBandKer (P : ℕ → ℕ → ℝ) (B : Finset ℕ) : ℕ → ℕ → ℝ
  | n =>
    if n ∈ B then (fun z => if z = n then 1 else 0)
    else (fun z => ∑ k ∈ (Finset.range n).attach, P n k.1 * enterBandKer P B k.1 z)
  termination_by n => n
  decreasing_by exact Finset.mem_range.mp k.2

/-- Defining equation of `enterBandKer` over the plain `Finset.range n`. -/
lemma enterBandKer_eq (P : ℕ → ℕ → ℝ) (B : Finset ℕ) (n z : ℕ) :
    enterBandKer P B n z
      = if n ∈ B then (if z = n then 1 else 0)
        else ∑ k ∈ Finset.range n, P n k * enterBandKer P B k z := by
  rw [enterBandKer]
  by_cases h : n ∈ B
  · simp [h]
  · rw [if_neg h, if_neg h, Finset.sum_attach (Finset.range n)
      (fun k => P n k * enterBandKer P B k z)]

variable {P : ℕ → ℕ → ℝ} {B : Finset ℕ}

/-- `enterBandKer` is nonnegative (given `P` nonnegative). -/
lemma enterBandKer_nonneg (hPnn : ∀ n k, 0 ≤ P n k) (n z : ℕ) :
    0 ≤ enterBandKer P B n z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [enterBandKer_eq]
    by_cases h : n ∈ B
    · rw [if_pos h]; split <;> norm_num
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun k hk =>
        mul_nonneg (hPnn n k) (ih k (Finset.mem_range.mp hk)))

/-- `enterBandKer` is supported on `B`: it vanishes off the band. -/
lemma enterBandKer_supp {z : ℕ} (hz : z ∉ B) (n : ℕ) : enterBandKer P B n z = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [enterBandKer_eq]
    by_cases h : n ∈ B
    · rw [if_pos h, if_neg]; rintro rfl; exact hz h
    · rw [if_neg h]
      refine Finset.sum_eq_zero (fun k hk => ?_)
      rw [ih k (Finset.mem_range.mp hk), mul_zero]

/-- The total entrance mass over the band is `1`, given the chain is row-stochastic at every off-band
point (`hrow`).  The chain runs until it enters `B`, and every step off `B` conserves mass. -/
lemma enterBandKer_row_sum
    (hrow : ∀ m, m ∉ B → ∑ k ∈ Finset.range m, P m k = 1) (n : ℕ) :
    ∑ z ∈ B, enterBandKer P B n z = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ∈ B
    · -- point mass at n ∈ B
      have : ∀ z, enterBandKer P B n z = if z = n then 1 else 0 := by
        intro z; rw [enterBandKer_eq, if_pos h]
      rw [Finset.sum_congr rfl (fun z _ => this z)]
      rw [Finset.sum_ite_eq' B n (fun _ => (1 : ℝ)), if_pos h]
    · -- one P-step then recurse: ∑_z ∑_k P n k · enter k z = ∑_k P n k · 1 = ∑_k P n k = 1
      have hexpand : ∀ z, enterBandKer P B n z
          = ∑ k ∈ Finset.range n, P n k * enterBandKer P B k z := by
        intro z; rw [enterBandKer_eq, if_neg h]
      rw [Finset.sum_congr rfl (fun z _ => hexpand z), Finset.sum_comm]
      have hk : ∀ k ∈ Finset.range n, ∑ z ∈ B, P n k * enterBandKer P B k z = P n k := by
        intro k hk
        rw [← Finset.mul_sum, ih k (Finset.mem_range.mp hk), mul_one]
      rw [Finset.sum_congr rfl hk]
      exact hrow n h

/-! ## Step B — the entrance decomposition for `hitVal` -/

/-- **Entrance decomposition.**  A function harmonic at every off-band point equals its first-entrance
average over the band.  When `B` is the ceiling down-set `{rnk < R+A}` with `R ≥ J`, every off-band
point has rank `≥ R+A ≥ J`, so `hitVal` is harmonic there and `hharm` is discharged. -/
lemma hitVal_eq_enterBand_average {rank : ℕ → ℕ} {J : ℕ} {φ : ℕ → ℝ}
    (hharm : ∀ m, m ∉ B → hitVal P rank J φ m
        = ∑ k ∈ Finset.range m, P m k * hitVal P rank J φ k)
    (n : ℕ) :
    hitVal P rank J φ n = ∑ z ∈ B, enterBandKer P B n z * hitVal P rank J φ z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ∈ B
    · -- enterBandKer is point mass at n; the sum collapses to hitVal n
      have hpt : ∀ z, enterBandKer P B n z * hitVal P rank J φ z
          = if z = n then hitVal P rank J φ n else 0 := by
        intro z; rw [enterBandKer_eq, if_pos h]
        by_cases hz : z = n
        · rw [if_pos hz, if_pos hz, one_mul, hz]
        · rw [if_neg hz, if_neg hz, zero_mul]
      rw [Finset.sum_congr rfl (fun z _ => hpt z)]
      rw [Finset.sum_ite_eq' B n (fun _ => hitVal P rank J φ n), if_pos h]
    · -- harmonic step + recursion: hitVal n = ∑_k P n k hitVal k = ∑_k P n k ∑_z enter k z hitVal z
      rw [hharm n h]
      have hstep : ∀ k ∈ Finset.range n,
          P n k * hitVal P rank J φ k
            = ∑ z ∈ B, P n k * (enterBandKer P B k z * hitVal P rank J φ z) := by
        intro k hk
        rw [ih k (Finset.mem_range.mp hk), Finset.mul_sum]
      rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [enterBandKer_eq (P := P) (B := B) n z, if_neg h, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => by ring)

/-! ## Step C — Doeblin contraction of the entrance average (wires `doeblin_average_diff_bound`) -/

/-- **Step C.**  Two entrance laws over `B` that overlap by `≥ δ`, averaging values that lie in the
band `[lo, lo + W]`, give averages differing by `≤ (1−δ)·W`.  Direct instance of the banked
`doeblin_average_diff_bound`. -/
lemma enterBand_average_diff_le
    {n n' : ℕ} {δ lo W : ℝ} {ψ : ℕ → ℝ}
    (hrn : ∑ z ∈ B, enterBandKer P B n z = 1)
    (hrn' : ∑ z ∈ B, enterBandKer P B n' z = 1)
    (hov : δ ≤ ∑ z ∈ B, min (enterBandKer P B n z) (enterBandKer P B n' z))
    (hband : ∀ z ∈ B, lo ≤ ψ z ∧ ψ z ≤ lo + W) (hW : 0 ≤ W) :
    |∑ z ∈ B, enterBandKer P B n z * ψ z - ∑ z ∈ B, enterBandKer P B n' z * ψ z|
      ≤ (1 - δ) * W :=
  doeblin_average_diff_bound (s := B) (p := enterBandKer P B n)
    (q := enterBandKer P B n') (f := ψ) hrn hrn' hov hband hW

/-! ## Step D — the descending-ceiling band and the abstract engine

The *band* used by the engine is the **finite ceiling down-set** `ceilBand R A` = all states of rank
`< R + A` (truncated to the recursion's finite range).  This set is **unskippable on the way down**
(the chain can only enter it, never jump over it from above), so the first-entrance decomposition
holds with the harmonic hypothesis discharged at every off-band point (rank `≥ R + A ≥ J`).  The
landed point's rank is `< R + A`; the engine then splits the band into the in-band overlap part
`[R, R+A)` and the **overshoot** part `[0, R)`, which carries an escape mass driving the residual
oscillation.  See `HANDOFF/TASK11-gap.md` for why a *fixed* band width `A` leaves a non-vanishing
escape floor (the genuine obstruction). -/

/-- The finite ceiling down-set `{k | rnk k < R + A}`, truncated to the enumeration window
`range ((R+A+2)^2)` (which contains every state of rank `< R+A`, since `rnk k < R+A ⟹ 3√k < R+A ⟹
k < (R+A)²/9 < (R+A+2)²`). -/
def ceilBand (R A : ℕ) : Finset ℕ :=
  Finset.filter (fun k => rnk k < R + A) (Finset.range ((R + A + 2) ^ 2))

/-- `rnk k < R + A` already forces `k` into the enumeration window, so membership is rank-only. -/
lemma mem_ceilBand_iff {R A k : ℕ} :
    k ∈ ceilBand R A ↔ rnk k < R + A := by
  unfold ceilBand
  rw [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro hlt
  -- rnk k < R+A ⟹ 3√k < R+A ⟹ √k < (R+A)/3 ⟹ k < (R+A)²/9 < (R+A+2)²
  have hfloor : (3 : ℝ) * Real.sqrt (k : ℝ) < (R + A : ℝ) := by
    by_contra hcon
    rw [not_lt] at hcon
    have : (R + A : ℕ) ≤ rnk k := by
      unfold rnk; exact Nat.le_floor (by push_cast; linarith)
    omega
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  have hsq : (k : ℝ) < ((R + A : ℝ) / 3) ^ 2 := by
    have hsqrtlt : Real.sqrt (k : ℝ) < (R + A : ℝ) / 3 := by linarith
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [Real.sq_sqrt hknn, hsqrtlt, hsqrtnn]
  have hub : ((R + A : ℝ) / 3) ^ 2 ≤ ((R + A + 2) ^ 2 : ℕ) := by
    push_cast
    have h0 : (0 : ℝ) ≤ (R : ℝ) + (A : ℝ) := by positivity
    nlinarith
  have : (k : ℝ) < ((R + A + 2) ^ 2 : ℕ) := lt_of_lt_of_le hsq hub
  exact_mod_cast this

/-- A point **off** the ceiling band has rank `≥ R + A`. -/
lemma not_mem_ceilBand_rank_ge {R A m : ℕ} (hm : m ∉ ceilBand R A) : R + A ≤ rnk m := by
  by_contra hcon
  exact hm (mem_ceilBand_iff.mpr (Nat.not_le.mp hcon))

end AnalyticCombinatorics.Ch8.Partitions.Erdos
