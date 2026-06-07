import AnalyticCombinatorics.Ch8.Partitions.RenewalAssembly
import AnalyticCombinatorics.Ch8.Partitions.HitValBound
import AnalyticCombinatorics.Ch8.Partitions.ErdosConcrete
import AnalyticCombinatorics.Ch8.Partitions.ErdosLimit

/-!
# R7 Fact B via Doeblin: the connection to `erdos_partition_limit_exists`

Instantiates the abstract `tendsto_of_killed_doeblin` for the concrete Erdős predecessor kernel
`killedKer Pker rnk J`, producing the full reduction:

  if the **Doeblin walls** hold for cofinitely many cutoffs `J` (finite-time overlap `δ > 0` on the
  high-rank band + vanishing escape mass), then the normalized partition sequence `u` converges to a
  positive limit — the existence of the Hardy–Ramanujan constant.

Every step here is mechanical (boundedness of `hitVal`, substochasticity of `Pker`, `rnk → atTop`,
row-stochasticity of the killed kernel for large `J`, the `KPowK L P̃`-harmonic identity); the two walls
bundled in `DoeblinWalls` are the only remaining analytic content (the Γ(2,C) convolution local-limit
wall — see HANDOFF UPDATE 8).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `u` is nonnegative (`n · p(n) · e^{…} ≥ 0`). -/
lemma u_nonneg (n : ℕ) : 0 ≤ u n := by
  unfold u
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (by unfold part; exact Nat.cast_nonneg _))
    (Real.exp_pos _).le

/-- `u` is globally bounded (eventual `limsup` bound padded by the finitely many initial terms). -/
lemma u_abs_le : ∃ Mu : ℝ, 0 ≤ Mu ∧ ∀ n, |u n| ≤ Mu := by
  obtain ⟨M, hMpos, hMev⟩ := u_limsup_finite
  obtain ⟨N, hN⟩ := eventually_atTop.1 hMev
  refine ⟨max M (∑ k ∈ Finset.range N, |u k|), le_trans hMpos.le (le_max_left _ _), fun n => ?_⟩
  by_cases h : n < N
  · exact le_trans (Finset.single_le_sum (f := fun k => |u k|) (fun k _ => abs_nonneg (u k))
      (Finset.mem_range.mpr h)) (le_max_right _ _)
  · rw [abs_of_nonneg (u_nonneg n)]
    exact le_trans (hN n (by omega)) (le_max_left _ _)

/-- The killed Erdős kernel is nonnegative. -/
lemma killedKer_Pker_nonneg (J n k : ℕ) : 0 ≤ killedKer Pker rnk J n k := by
  unfold killedKer
  by_cases h : rnk n < J
  · simp only [if_pos h]; split <;> norm_num
  · simp only [if_neg h]; exact Pker_nonneg n k

/-- `Pker` is supported on strict predecessors (`n ≤ k → Pker n k = 0`). -/
lemma Pker_supp (n k : ℕ) (h : n ≤ k) : Pker n k = 0 := by
  unfold Pker; rw [if_neg (by omega)]

/-- For `J` large enough, `rnk n ≥ J` forces `n` into the region where `Pker` is row-stochastic. -/
lemma Pker_rowsum_rank {N₀ : ℕ} (hN₀2 : 2 ≤ N₀) (hkm : ∀ n, N₀ ≤ n → kernelMass n ≠ 0)
    {J : ℕ} (hJ : 3 * N₀ + 3 ≤ J) {n : ℕ} (hn : J ≤ rnk n) :
    ∑ k ∈ Finset.range n, Pker n k = 1 := by
  have hge : N₀ ≤ n := rnk_ge_of (le_trans hJ hn)
  exact Pker_mass (by omega) (hkm n hge)

/-- The **Doeblin walls** at cutoff `J`: a finite-time overlap `δ > 0` on the high-rank band and a
vanishing escape mass below the band, for the `L`-step killed Erdős kernel. -/
def DoeblinWalls (J : ℕ) : Prop :=
  ∃ (δ : ℝ) (B R₀ L : ℕ) (e : ℕ → ℝ),
    0 < δ ∧ δ ≤ 1 ∧ (∀ n, 0 ≤ e n) ∧ Tendsto e atTop (𝓝 0) ∧
    (∀ R, R₀ ≤ R → ∀ i j, R ≤ rnk i → R ≤ rnk j →
       δ ≤ ∑ k ∈ (Finset.range (max i j + 1)).filter (fun k => R - B ≤ rnk k),
              min (KPowK L (killedKer Pker rnk J) i k) (KPowK L (killedKer Pker rnk J) j k)) ∧
    (∀ R, R₀ ≤ R → ∀ i, R ≤ rnk i →
       ∑ k ∈ (Finset.range (i + 1)).filter (fun k => ¬ (R - B ≤ rnk k)),
              KPowK L (killedKer Pker rnk J) i k ≤ e R)

/-- **The Hardy–Ramanujan reduction.** If the Doeblin walls hold for cofinitely many cutoffs `J`, the
normalized partition sequence converges to a positive limit. -/
theorem erdos_partition_limit_exists_of_walls
    (hwalls : ∀ᶠ J : ℕ in atTop, DoeblinWalls J) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) := by
  obtain ⟨Mu, hMu0, hMu⟩ := u_abs_le
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 kernelMass_pos_eventually
  set N₀ := max N₁ 2 with hN₀def
  have hkm : ∀ n, N₀ ≤ n → kernelMass n ≠ 0 := fun n hn =>
    ne_of_gt (hN₁ n (le_trans (le_max_left _ _) hn))
  have hN₀2 : 2 ≤ N₀ := le_max_right _ _
  apply erdos_partition_limit_exists_of_hit
  filter_upwards [hwalls, eventually_ge_atTop (3 * N₀ + 3)] with J hWJ hJ
  obtain ⟨δ, B, R₀, L, e, hδ0, hδ1, he0, hetend, hoverlap, hescape⟩ := hWJ
  refine tendsto_of_killed_doeblin (M := Mu) (rank := rnk) (Pt := killedKer Pker rnk J)
    (δ := δ) (B := B) (R₀ := R₀) (L := L) (e := e)
    (hitVal_abs_le hMu0 hMu Pker_nonneg (fun n _ => Pker_sum_le_one n))
    rnk_tendsto_atTop
    (killedKer_Pker_nonneg J)
    (fun m => killedKer_row_sum (fun n hn => Pker_rowsum_rank hN₀2 hkm hJ hn) Pker_supp m)
    (fun n => killed_harmonic_pow Pker_supp (hitVal_eq Pker rnk J u) L n)
    hδ0 hδ1 he0 hetend hoverlap hescape

end AnalyticCombinatorics.Ch8.Partitions.Erdos
