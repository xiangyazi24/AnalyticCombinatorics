import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.PartitionRenewal

/-!
# R7 assembly: `erdos_partition_limit_exists` modulo the hard core (Fact B)

Instantiates the renewal spine to the partition kernel: with all Layer-1 kernel facts proven
(`Pker_mass`, `dres_block_bound`, `hP_leave_partition`) plus the well-founded `hitVal`/`potVal`,
`rec_iter_bound` + `pot_le_block_sum_of_leave` + `block_sum_le_tail` give the uniform
hit-approximation `|u n − hitVal_J n| ≤ (1/μ)·tail_J`, and the convergence engine
`tendsto_of_uniform_hit_approx` then yields convergence — *modulo* the single hard analytic
hypothesis (Fact B): for cofinitely many cutoffs `J`, the hit value `hitVal Pker rnk J u` converges.
Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Convergence modulo Fact B.** If the harmonic hit values converge for cofinitely many cutoffs,
the normalized partition sequence `u` converges to a positive limit. -/
theorem erdos_partition_limit_exists_of_hit
    (hhit : ∀ᶠ J : ℕ in atTop,
        ∃ L : ℝ, Tendsto (fun n => hitVal Pker rnk J u n) atTop (𝓝 L)) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) := by
  obtain ⟨M, hMpos, hMev⟩ := u_limsup_finite
  obtain ⟨c, hcpos, hcev⟩ := u_liminf_positive
  obtain ⟨errFn, herr_nn, herr_sum, herr_ev⟩ := dres_block_bound
  obtain ⟨μ, hμpos, hμ_ev⟩ := hP_leave_partition
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  -- `u` is globally bounded
  have hBddA : BddAbove (Set.range u) := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hMev
    refine ⟨max M (∑ k ∈ Finset.range N, |u k|), ?_⟩
    rintro y ⟨n, rfl⟩
    by_cases h : n < N
    · refine le_trans (le_trans (le_abs_self (u n)) ?_) (le_max_right _ _)
      exact Finset.single_le_sum (f := fun k => |u k|) (fun k _ => abs_nonneg (u k))
        (Finset.mem_range.mpr h)
    · exact le_trans (hN n (by omega)) (le_max_left _ _)
  have hBddB : BddBelow (Set.range u) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [u]
    · exact (u_pos hpos).le
  -- combined eventual kernel facts
  have hhalf : ∀ᶠ n : ℕ in atTop, K / (n : ℝ) ≤ 1 / 2 := by
    have htend : Filter.Tendsto (fun n : ℕ => K / (n : ℝ)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    exact htend.eventually_le_const (by norm_num)
  have hcomb : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ (1 : ℝ) / 2 ≤ kernelMass n
      ∧ |dres n| ≤ errFn (rnk n)
      ∧ μ ≤ ∑ k ∈ (Finset.range n).filter (fun k => rnk k < rnk n), Pker n k := by
    filter_upwards [herr_ev, hμ_ev, hKev, hhalf, eventually_ge_atTop 2]
      with n h1 h2 h3 h4 h5
    refine ⟨h5, ?_, h1, h2⟩
    obtain ⟨hlo, _⟩ := abs_le.1 h3
    linarith [h4]
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hcomb
  -- the uniform hit-approximation `|u n − hitVal_J n| ≤ (1/μ)·tail_J`
  have hbound : ∀ᶠ J : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      |u n - hitVal Pker rnk J u n|
        ≤ 1 / μ * ((∑' j, errFn j) - ∑ j ∈ Finset.range J, errFn j) := by
    filter_upwards [eventually_ge_atTop (3 * N0 + 3), eventually_ge_atTop 1] with J hJ hJ1
    apply Eventually.of_forall
    intro n
    have hfact : ∀ m, J ≤ rnk m → 2 ≤ m ∧ (1 : ℝ) / 2 ≤ kernelMass m
        ∧ |dres m| ≤ errFn (rnk m)
        ∧ μ ≤ ∑ k ∈ (Finset.range m).filter (fun k => rnk k < rnk m), Pker m k := by
      intro m hm
      exact hN0 m (rnk_ge_of (by omega))
    have hrib := rec_iter_bound (P := Pker) (rank := rnk) (u := u) (d := dres) (e := errFn)
      (Hit := hitVal Pker rnk J u) (Pot := potVal Pker rnk J errFn) (J := J)
      (fun n k => Pker_nonneg n k)
      (fun m _ => u_eq_Pker_sum_add_dres m)
      (fun m hm => (hfact m hm).2.2.1)
      (hitVal_eq Pker rnk J u)
      (potVal_eq Pker rnk J errFn)
    have hple := pot_le_block_sum_of_leave (P := Pker) (rank := rnk) (e := errFn)
      (Pot := potVal Pker rnk J errFn) (J := J) (μ := μ) (by omega)
      herr_nn (fun n k => Pker_nonneg n k) rnk_mono
      (fun m hm => Pker_mass (hfact m hm).1
        (ne_of_gt (lt_of_lt_of_le (by norm_num) (hfact m hm).2.1)))
      (fun m hm => (hfact m hm).2.2.2)
      (potVal_eq Pker rnk J errFn)
    have hb1 := hrib n
    have hb2 := hple n
    have hb3 := block_sum_le_tail herr_nn herr_sum J (rnk n)
    have hmul : μ * potVal Pker rnk J errFn n
        ≤ (∑' j, errFn j) - ∑ j ∈ Finset.range J, errFn j := le_trans hb2 hb3
    have hPotle : potVal Pker rnk J errFn n
        ≤ ((∑' j, errFn j) - ∑ j ∈ Finset.range J, errFn j) / μ := by
      rw [le_div_iff₀ hμpos]; nlinarith [hmul]
    calc |u n - hitVal Pker rnk J u n| ≤ potVal Pker rnk J errFn n := hb1
      _ ≤ ((∑' j, errFn j) - ∑ j ∈ Finset.range J, errFn j) / μ := hPotle
      _ = 1 / μ * ((∑' j, errFn j) - ∑ j ∈ Finset.range J, errFn j) := by ring
  obtain ⟨a, ha⟩ := tendsto_of_uniform_hit_approx (u := u)
    (Hit := fun J n => hitVal Pker rnk J u n)
    (tail := fun J => (∑' j, errFn j) - ∑ j ∈ Finset.range J, errFn j)
    (B := 1 / μ) hBddA hBddB hbound hhit (tail_tendsto_zero herr_sum)
  refine ⟨a, ?_, ha⟩
  have hca : c ≤ a := ge_of_tendsto ha hcev
  linarith [hcpos]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
