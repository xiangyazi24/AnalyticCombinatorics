import AnalyticCombinatorics.Ch8.Partitions.RenewalAlign
import AnalyticCombinatorics.Ch8.Partitions.ErdosRenewalConnect

/-!
# R7 Fact B via Doeblin: the renewal-alignment connection to `erdos_partition_limit_exists`

The correct (satisfiable) Hardy–Ramanujan reduction.  Instantiates `tendsto_of_renewal_alignment` for the
concrete killed Erdős kernel: if the **renewal-alignment** holds for cofinitely many cutoffs `J` — the
`m`-step terminal laws of any two high-rank starts overlap by `≥ 1 − (1−δ)^m − ε` — then the normalized
partition sequence `u` converges to a positive limit.  Unlike the all-pairs single-step overlap (which is
false for far-rank pairs), the alignment input is genuinely satisfiable: two descending chains synchronize
at the shared lower rank levels they both pass through.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The **renewal-alignment** at cutoff `J`: for some `δ>0`, the `m`-step terminal laws of any two
high-rank starts overlap by `≥ 1 − (1−δ)^m − ε`. -/
def ErdosAlignment (J : ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ R₀ : ℕ, ∀ i j, R₀ ≤ rnk i → R₀ ≤ rnk j →
      1 - (1 - δ) ^ m - ε ≤ ∑ k ∈ Finset.range (max i j + 1),
          min (KPowK m (killedKer Pker rnk J) i k) (KPowK m (killedKer Pker rnk J) j k)

/-- **The Hardy–Ramanujan reduction (renewal-alignment form).** If the renewal-alignment holds for
cofinitely many cutoffs, `u` converges to a positive limit. -/
theorem erdos_partition_limit_exists_of_alignment
    (ha : ∀ᶠ J : ℕ in atTop, ErdosAlignment J) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) := by
  obtain ⟨Mu, hMu0, hMu⟩ := u_abs_le
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 kernelMass_pos_eventually
  set N₀ := max N₁ 2 with hN₀def
  have hkm : ∀ n, N₀ ≤ n → kernelMass n ≠ 0 := fun n hn =>
    ne_of_gt (hN₁ n (le_trans (le_max_left _ _) hn))
  have hN₀2 : 2 ≤ N₀ := le_max_right _ _
  apply erdos_partition_limit_exists_of_hit
  filter_upwards [ha, eventually_ge_atTop (3 * N₀ + 3)] with J hJa hJ
  obtain ⟨δ, hδ0, hδ1, halign⟩ := hJa
  exact tendsto_of_renewal_alignment (M := Mu) (rank := rnk)
    (Pt := killedKer Pker rnk J) (δ := δ)
    (hitVal_abs_le hMu0 hMu Pker_nonneg (fun n _ => Pker_sum_le_one n))
    rnk_tendsto_atTop
    (killedKer_Pker_nonneg J)
    (fun m => killedKer_row_sum (fun n hn => Pker_rowsum_rank hN₀2 hkm hJ hn) Pker_supp m)
    hδ0 hδ1
    (fun m n => killed_harmonic_pow Pker_supp (hitVal_eq Pker rnk J u) m n)
    halign

end AnalyticCombinatorics.Ch8.Partitions.Erdos
