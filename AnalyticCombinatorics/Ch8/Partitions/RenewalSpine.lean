import Mathlib

/-!
# R7 renewal route: the abstract convergence engine (Layer 5 spine)

The renewal / harmonic-Markov-chain route to `u_n → L` (ChatGPT b0f6ab89; replaces the refuted
record-cover whose `1/μ` amplification was proven intrinsic) reduces convergence to a uniform
hit-approximation: for every cutoff `J` the sequence is uniformly close to a convergent "hit value"
`Hit_J`, with error a `J`-tail that vanishes:

  `|u n − Hit_J n| ≤ B·tail J`  eventually,   `Hit_J n → L_J` as `n→∞`,   `tail J → 0`.

Then `limsup u − liminf u ≤ 2 B·tail J` for every `J`, so `u` converges.  This file proves that
engine, design-independent (it takes `Hit`, `Pot`/bound, `tail` abstractly).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Uniform hit-approximation ⟹ convergence.** If `u` is bounded and, for every cutoff `J`,
eventually `|u n − Hit J n| ≤ B·tail J` with `Hit J · → L_J` and `tail J → 0`, then `u` converges. -/
theorem tendsto_of_uniform_hit_approx
    {u : ℕ → ℝ} {Hit : ℕ → ℕ → ℝ} {tail : ℕ → ℝ} {B : ℝ}
    (hu_bddA : BddAbove (Set.range u)) (hu_bddB : BddBelow (Set.range u))
    (hbound : ∀ J, ∀ᶠ n in atTop, |u n - Hit J n| ≤ B * tail J)
    (hhit : ∀ J, ∃ L, Tendsto (fun n => Hit J n) atTop (𝓝 L))
    (htail : Tendsto tail atTop (𝓝 0)) :
    ∃ L : ℝ, Tendsto u atTop (𝓝 L) := by
  have hbddU : IsBoundedUnder (· ≤ ·) atTop u := hu_bddA.isBoundedUnder_of_range
  have hbddL : IsBoundedUnder (· ≥ ·) atTop u := hu_bddB.isBoundedUnder_of_range
  have hcobddU : IsCoboundedUnder (· ≤ ·) atTop u := hbddL.isCoboundedUnder_le
  have hcobddL : IsCoboundedUnder (· ≥ ·) atTop u := hbddU.isCoboundedUnder_ge
  -- For every J, `limsup u - liminf u ≤ 2 B tail J`.
  have hosc : ∀ J : ℕ, limsup u atTop - liminf u atTop ≤ 2 * (B * tail J) := by
    intro J
    obtain ⟨L, hL⟩ := hhit J
    have hbJ := hbound J
    -- eventually `u n ≤ Hit J n + B tail J` and `Hit J n - B tail J ≤ u n`
    have hup : ∀ᶠ n in atTop, u n ≤ Hit J n + B * tail J := by
      filter_upwards [hbJ] with n hn
      have := (abs_le.1 hn).2; linarith
    have hlo : ∀ᶠ n in atTop, Hit J n - B * tail J ≤ u n := by
      filter_upwards [hbJ] with n hn
      have := (abs_le.1 hn).1; linarith
    -- limsup u ≤ L + B tail J
    have hHitU : IsBoundedUnder (· ≤ ·) atTop (fun n => Hit J n + B * tail J) :=
      (hL.add_const _).isBoundedUnder_le
    have hHitL : IsBoundedUnder (· ≥ ·) atTop (fun n => Hit J n - B * tail J) :=
      (hL.sub_const _).isBoundedUnder_ge
    have hlimsup : limsup u atTop ≤ L + B * tail J := by
      have h1 : limsup u atTop ≤ limsup (fun n => Hit J n + B * tail J) atTop :=
        limsup_le_limsup hup hcobddU hHitU
      have h2 : limsup (fun n => Hit J n + B * tail J) atTop = L + B * tail J := by
        have := (hL.add_const (B * tail J))
        exact this.limsup_eq
      linarith [h1, h2.le]
    have hliminf : L - B * tail J ≤ liminf u atTop := by
      have h1 : liminf (fun n => Hit J n - B * tail J) atTop ≤ liminf u atTop :=
        liminf_le_liminf hlo hHitL hcobddL
      have h2 : liminf (fun n => Hit J n - B * tail J) atTop = L - B * tail J := by
        have := (hL.sub_const (B * tail J))
        exact this.liminf_eq
      linarith [h1, h2.ge]
    linarith
  -- limsup u - liminf u ≤ 0 by letting tail J → 0.
  have hle : limsup u atTop - liminf u atTop ≤ 0 := by
    have htends : Tendsto (fun J => 2 * (B * tail J)) atTop (𝓝 0) := by
      have : Tendsto (fun J => 2 * (B * tail J)) atTop (𝓝 (2 * (B * 0))) :=
        (htail.const_mul B).const_mul 2
      simpa using this
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htends (Eventually.of_forall hosc)
  have hge : liminf u atTop ≤ limsup u atTop := liminf_le_limsup hbddU hbddL
  have heq : liminf u atTop = limsup u atTop := le_antisymm hge (by linarith)
  exact ⟨limsup u atTop, tendsto_of_liminf_eq_limsup heq rfl hbddU hbddL⟩

/-- **Layer 2: potential bound (`rec_iter_bound`).** With `Hit`/`Pot` satisfying their fixed-point
equations over the predecessor kernel `P` (probability on `Finset.range n` above the cutoff), and the
recurrence `u n = Σ P·u + d n` with `|d n| ≤ e (rank n)`, the hit-approximation error is controlled
by the potential: `|u n − Hit n| ≤ Pot n`.  Proof by strong induction on `n` (predecessors `k < n`).
Design-independent; the concrete `Hit`/`Pot` are constructed in the kernel layer. -/
theorem rec_iter_bound
    {P : ℕ → ℕ → ℝ} {rank : ℕ → ℕ} {u d e Hit Pot : ℕ → ℝ} {J : ℕ}
    (hP_nonneg : ∀ n k, 0 ≤ P n k)
    (hrec : ∀ n, J ≤ rank n → u n = (∑ k ∈ Finset.range n, P n k * u k) + d n)
    (herr : ∀ n, |d n| ≤ e (rank n))
    (hHit : ∀ n, Hit n = if rank n < J then u n
              else ∑ k ∈ Finset.range n, P n k * Hit k)
    (hPot : ∀ n, Pot n = if rank n < J then 0
              else e (rank n) + ∑ k ∈ Finset.range n, P n k * Pot k) :
    ∀ n, |u n - Hit n| ≤ Pot n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hJ : rank n < J
    · rw [hHit n, hPot n, if_pos hJ, if_pos hJ]; simp
    · have hJ' : J ≤ rank n := not_lt.mp hJ
      rw [hHit n, hPot n, if_neg hJ, if_neg hJ, hrec n hJ', add_comm (e (rank n))]
      have hrw : (∑ k ∈ Finset.range n, P n k * u k) + d n
            - ∑ k ∈ Finset.range n, P n k * Hit k
          = (∑ k ∈ Finset.range n, P n k * (u k - Hit k)) + d n := by
        rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
        congr 1
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [hrw]
      calc |(∑ k ∈ Finset.range n, P n k * (u k - Hit k)) + d n|
          ≤ |∑ k ∈ Finset.range n, P n k * (u k - Hit k)| + |d n| := abs_add_le _ _
        _ ≤ (∑ k ∈ Finset.range n, P n k * Pot k) + e (rank n) := by
            gcongr
            · calc |∑ k ∈ Finset.range n, P n k * (u k - Hit k)|
                  ≤ ∑ k ∈ Finset.range n, |P n k * (u k - Hit k)| :=
                    Finset.abs_sum_le_sum_abs _ _
                _ = ∑ k ∈ Finset.range n, P n k * |u k - Hit k| :=
                    Finset.sum_congr rfl (fun k _ => by
                      rw [abs_mul, abs_of_nonneg (hP_nonneg n k)])
                _ ≤ ∑ k ∈ Finset.range n, P n k * Pot k :=
                    Finset.sum_le_sum (fun k hk =>
                      mul_le_mul_of_nonneg_left (ih k (Finset.mem_range.mp hk)) (hP_nonneg n k))
            · exact herr n

/-- **Layer 3: potential ≤ block tail (`pot_le_block_sum`).** *Fact A is elementary*: when each
kernel step strictly decreases `rank` (true for `rank n = ⌊ρ√n⌋`, `ρ > 2/α`, since `m > α√n` forces
`√n − √(n−m) > α/2`), each rank block is visited at most once along the backward chain, so the
potential is bounded by the block tail `Σ_{j=J}^{rank n} e j`.  No renewal-density theory.  Proof by
strong induction on `n`. -/
theorem pot_le_block_sum
    {P : ℕ → ℕ → ℝ} {rank : ℕ → ℕ} {e Pot : ℕ → ℝ} {J : ℕ}
    (hJ1 : 1 ≤ J)
    (he_nonneg : ∀ j, 0 ≤ e j)
    (hP_nonneg : ∀ n k, 0 ≤ P n k)
    (hP_mass : ∀ n, J ≤ rank n → ∑ k ∈ Finset.range n, P n k = 1)
    (hP_drop : ∀ n k, J ≤ rank n → k ∈ Finset.range n → P n k ≠ 0 → rank k < rank n)
    (hPot : ∀ n, Pot n = if rank n < J then 0
              else e (rank n) + ∑ k ∈ Finset.range n, P n k * Pot k) :
    ∀ n, Pot n ≤ ∑ j ∈ Finset.Icc J (rank n), e j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [hPot n]
    by_cases hJ : rank n < J
    · rw [if_pos hJ, Finset.Icc_eq_empty (by omega)]; simp
    · rw [if_neg hJ]
      have hJ' : J ≤ rank n := not_lt.mp hJ
      have hsub : ∑ k ∈ Finset.range n, P n k * Pot k
          ≤ ∑ j ∈ Finset.Icc J (rank n - 1), e j := by
        calc ∑ k ∈ Finset.range n, P n k * Pot k
            ≤ ∑ k ∈ Finset.range n, P n k * (∑ j ∈ Finset.Icc J (rank n - 1), e j) := by
              apply Finset.sum_le_sum
              intro k hk
              by_cases hPk : P n k = 0
              · rw [hPk]; simp
              · have hdrop := hP_drop n k hJ' hk hPk
                have hmono : ∑ j ∈ Finset.Icc J (rank k), e j
                    ≤ ∑ j ∈ Finset.Icc J (rank n - 1), e j :=
                  Finset.sum_le_sum_of_subset_of_nonneg
                    (Finset.Icc_subset_Icc_right (by omega))
                    (fun j _ _ => he_nonneg j)
                exact mul_le_mul_of_nonneg_left
                  (le_trans (ih k (Finset.mem_range.mp hk)) hmono) (hP_nonneg n k)
          _ = (∑ k ∈ Finset.range n, P n k) * (∑ j ∈ Finset.Icc J (rank n - 1), e j) := by
              rw [Finset.sum_mul]
          _ = ∑ j ∈ Finset.Icc J (rank n - 1), e j := by rw [hP_mass n hJ']; ring
      have hrn : rank n = (rank n - 1) + 1 := by omega
      have hsplit : ∑ j ∈ Finset.Icc J (rank n), e j
          = (∑ j ∈ Finset.Icc J (rank n - 1), e j) + e (rank n) := by
        conv_lhs => rw [hrn]
        rw [Finset.sum_Icc_succ_top (by omega : J ≤ (rank n - 1) + 1), ← hrn]
      rw [hsplit]
      linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
