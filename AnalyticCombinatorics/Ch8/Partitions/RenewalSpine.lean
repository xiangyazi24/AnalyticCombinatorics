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
    (hbound : ∀ᶠ J in atTop, ∀ᶠ n in atTop, |u n - Hit J n| ≤ B * tail J)
    (hhit : ∀ᶠ J in atTop, ∃ L, Tendsto (fun n => Hit J n) atTop (𝓝 L))
    (htail : Tendsto tail atTop (𝓝 0)) :
    ∃ L : ℝ, Tendsto u atTop (𝓝 L) := by
  have hbddU : IsBoundedUnder (· ≤ ·) atTop u := hu_bddA.isBoundedUnder_of_range
  have hbddL : IsBoundedUnder (· ≥ ·) atTop u := hu_bddB.isBoundedUnder_of_range
  have hcobddU : IsCoboundedUnder (· ≤ ·) atTop u := hbddL.isCoboundedUnder_le
  have hcobddL : IsCoboundedUnder (· ≥ ·) atTop u := hbddU.isCoboundedUnder_ge
  -- For all large `J`, `limsup u - liminf u ≤ 2 B tail J`.
  have hosc : ∀ᶠ J in atTop, limsup u atTop - liminf u atTop ≤ 2 * (B * tail J) := by
    filter_upwards [hbound, hhit] with J hbJ hhJ
    obtain ⟨L, hL⟩ := hhJ
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
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htends hosc
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
    (herr : ∀ n, J ≤ rank n → |d n| ≤ e (rank n))
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
            · exact herr n hJ'

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

/-- A finite rank-block sum is bounded by the `J`-tail `(∑' e) − ∑_{range J} e`. -/
lemma block_sum_le_tail {e : ℕ → ℝ} (he_nonneg : ∀ j, 0 ≤ e j) (he : Summable e) (J m : ℕ) :
    ∑ j ∈ Finset.Icc J m, e j ≤ (∑' j, e j) - ∑ j ∈ Finset.range J, e j := by
  have hdisj : Disjoint (Finset.Icc J m) (Finset.range J) := by
    rw [Finset.disjoint_left]
    intro a ha hr
    rw [Finset.mem_Icc] at ha; rw [Finset.mem_range] at hr; omega
  have hunion : ∑ j ∈ Finset.Icc J m, e j + ∑ j ∈ Finset.range J, e j
      = ∑ j ∈ Finset.Icc J m ∪ Finset.range J, e j := (Finset.sum_union hdisj).symm
  have hle : ∑ j ∈ Finset.Icc J m ∪ Finset.range J, e j ≤ ∑' j, e j :=
    sum_le_hasSum _ (fun i _ => he_nonneg i) he.hasSum
  linarith [hunion, hle]

/-- **Layer 3 (general, `pot_le_block_sum_of_leave`).** *Fact A for the full kernel.* The full
normalized kernel has small steps, so strict rank-drop fails; but every block is *left downward with
probability ≥ μ* (a window step `m∈[√n,2√n]` drops `rank=⌊ρ√n⌋`, and that mass is `≥μ`). The
contraction-style induction gives `μ·Pot ≤ block-sum`, i.e. `Pot ≤ (1/μ)·tail`.  The `1/μ` is a
single constant on the summable tail — NOT the per-step `μ^{−√N}` compounding that killed the record
route.  `rank` monotone, `P` a probability kernel on `range n`. -/
theorem pot_le_block_sum_of_leave
    {P : ℕ → ℕ → ℝ} {rank : ℕ → ℕ} {e Pot : ℕ → ℝ} {J : ℕ} {μ : ℝ}
    (hJ1 : 1 ≤ J)
    (he_nonneg : ∀ j, 0 ≤ e j)
    (hP_nonneg : ∀ n k, 0 ≤ P n k)
    (hrank_mono : Monotone rank)
    (hP_mass : ∀ n, J ≤ rank n → ∑ k ∈ Finset.range n, P n k = 1)
    (hP_leave : ∀ n, J ≤ rank n →
        μ ≤ ∑ k ∈ (Finset.range n).filter (fun k => rank k < rank n), P n k)
    (hPot : ∀ n, Pot n = if rank n < J then 0
              else e (rank n) + ∑ k ∈ Finset.range n, P n k * Pot k) :
    ∀ n, μ * Pot n ≤ ∑ j ∈ Finset.Icc J (rank n), e j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [hPot n]
    by_cases hJ : rank n < J
    · rw [if_pos hJ, Finset.Icc_eq_empty (by omega)]; simp
    · rw [if_neg hJ]
      have hJ' : J ≤ rank n := not_lt.mp hJ
      set T := ∑ j ∈ Finset.Icc J (rank n), e j with hT
      set Tm := ∑ j ∈ Finset.Icc J (rank n - 1), e j with hTm
      have hTm_nonneg : 0 ≤ Tm := Finset.sum_nonneg (fun j _ => he_nonneg j)
      have hTsplit : T = Tm + e (rank n) := by
        rw [hT, hTm]
        have hrn : rank n = (rank n - 1) + 1 := by omega
        conv_lhs => rw [hrn]
        rw [Finset.sum_Icc_succ_top (by omega : J ≤ (rank n - 1) + 1), ← hrn]
      -- `μ · Σ P·Pot ≤ Σ P·T_k`
      have hμPot : μ * (∑ k ∈ Finset.range n, P n k * Pot k)
          ≤ ∑ k ∈ Finset.range n, P n k * (∑ j ∈ Finset.Icc J (rank k), e j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [show μ * (P n k * Pot k) = P n k * (μ * Pot k) by ring]
        exact mul_le_mul_of_nonneg_left (ih k (Finset.mem_range.mp hk)) (hP_nonneg n k)
      -- split `range n` into rank-drop and rank-stay parts
      have hfP := Finset.sum_filter_add_sum_filter_not (Finset.range n)
        (fun k => rank k < rank n) (fun k => P n k)
      have hff := Finset.sum_filter_add_sum_filter_not (Finset.range n)
        (fun k => rank k < rank n) (fun k => P n k * (∑ j ∈ Finset.Icc J (rank k), e j))
      rw [hP_mass n hJ'] at hfP
      set Ddrop := ∑ k ∈ (Finset.range n).filter (fun k => rank k < rank n), P n k with hDdrop
      set Dsame := ∑ k ∈ (Finset.range n).filter (fun k => ¬ rank k < rank n), P n k with hDsame
      have hDsame_nonneg : 0 ≤ Dsame := Finset.sum_nonneg (fun k _ => hP_nonneg n k)
      have hDleave : μ ≤ Ddrop := hP_leave n hJ'
      -- `Σ P·T_k ≤ Ddrop·Tm + Dsame·T`
      have hbound : ∑ k ∈ Finset.range n, P n k * (∑ j ∈ Finset.Icc J (rank k), e j)
          ≤ Ddrop * Tm + Dsame * T := by
        rw [← hff, hDdrop, hDsame, Finset.sum_mul, Finset.sum_mul]
        refine add_le_add (Finset.sum_le_sum (fun k hk => ?_))
          (Finset.sum_le_sum (fun k hk => ?_))
        · rw [Finset.mem_filter, Finset.mem_range] at hk
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_right (by omega)) (fun j _ _ => he_nonneg j))
            (hP_nonneg n k)
        · rw [Finset.mem_filter, Finset.mem_range] at hk
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_right (hrank_mono hk.1.le)) (fun j _ _ => he_nonneg j))
            (hP_nonneg n k)
      -- assemble: μ·Pot n = μ·e + μ·ΣPPot ≤ μ·e + Ddrop·Tm + Dsame·T ≤ T
      rw [mul_add]
      have he := he_nonneg (rank n)
      have hkey : μ * e (rank n) + (Ddrop * Tm + Dsame * T) ≤ T := by
        have hDd : Ddrop = 1 - Dsame := by linarith [hfP]
        have hDsame_le : Dsame ≤ 1 - μ := by linarith [hfP, hDleave]
        rw [hTsplit, hDd]
        nlinarith [mul_nonneg (sub_nonneg.mpr hDsame_le) he, he, hTm_nonneg, hDsame_nonneg]
      linarith [hμPot, hbound, hkey]

/-- The `J`-tail `(∑' e) − ∑_{range J} e` of a summable series tends to `0`. -/
lemma tail_tendsto_zero {e : ℕ → ℝ} (he : Summable e) :
    Tendsto (fun J => (∑' j, e j) - ∑ j ∈ Finset.range J, e j) atTop (𝓝 0) := by
  have h := he.hasSum.tendsto_sum_nat
  have hlim : Tendsto (fun J => (∑' j, e j) - ∑ j ∈ Finset.range J, e j) atTop
      (𝓝 ((∑' j, e j) - ∑' j, e j)) := tendsto_const_nhds.sub h
  simpa using hlim

end AnalyticCombinatorics.Ch8.Partitions.Erdos
