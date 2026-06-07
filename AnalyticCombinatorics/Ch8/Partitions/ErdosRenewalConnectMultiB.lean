import AnalyticCombinatorics.Ch8.Partitions.RenewalMultiB
import AnalyticCombinatorics.Ch8.Partitions.ErdosRenewalConnect

/-!
# R7 Fact B via Doeblin: the multi-scale connection to `erdos_partition_limit_exists`

The correct (multi-scale) Hardy–Ramanujan reduction for the Erdős kernel.  The walls are B-indexed:
for each band width `B` a finite-time overlap `δ_B > 0` on `{rnk ≥ R−B}` and an escape mass `≤ ε_B`
below it, with `ε_B / δ_B → 0`.  (Unlike the fixed-band escape-split version, the escape here need not
vanish at any single `B`; the *family* with `ε_B/δ_B → 0` drives the tail oscillation to `0`.)  This is
the satisfiable form of `DoeblinWalls`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The **multi-scale Doeblin walls** at cutoff `J`: Skolemized overlaps `δ_B > 0` on the band
`{rnk ≥ R−B}` and escape masses `≤ ε_B` below it (for the `L_B`-step killed kernel), with
`ε_B / δ_B → 0`. -/
def DoeblinWallsMultiB (J : ℕ) : Prop :=
  ∃ (δ ε : ℕ → ℝ) (L R₀ : ℕ → ℕ),
    (∀ B, 0 < δ B) ∧ (∀ B, δ B ≤ 1) ∧ (∀ B, 0 ≤ ε B) ∧
    Tendsto (fun B => ε B / δ B) atTop (𝓝 0) ∧
    (∀ B R, R₀ B ≤ R → ∀ i j, R ≤ rnk i → R ≤ rnk j →
       δ B ≤ ∑ k ∈ (Finset.range (max i j + 1)).filter (fun k => R - B ≤ rnk k),
              min (KPowK (L B) (killedKer Pker rnk J) i k)
                  (KPowK (L B) (killedKer Pker rnk J) j k)) ∧
    (∀ B R, R₀ B ≤ R → ∀ i, R ≤ rnk i →
       ∑ k ∈ (Finset.range (i + 1)).filter (fun k => ¬ (R - B ≤ rnk k)),
              KPowK (L B) (killedKer Pker rnk J) i k ≤ ε B)

/-- **The Hardy–Ramanujan reduction (multi-scale).** If the multi-scale Doeblin walls hold for
cofinitely many cutoffs `J`, the normalized partition sequence converges to a positive limit. -/
theorem erdos_partition_limit_exists_of_walls_multiB
    (hwalls : ∀ᶠ J : ℕ in atTop, DoeblinWallsMultiB J) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) := by
  obtain ⟨Mu, hMu0, hMu⟩ := u_abs_le
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 kernelMass_pos_eventually
  set N₀ := max N₁ 2 with hN₀def
  have hkm : ∀ n, N₀ ≤ n → kernelMass n ≠ 0 := fun n hn =>
    ne_of_gt (hN₁ n (le_trans (le_max_left _ _) hn))
  have hN₀2 : 2 ≤ N₀ := le_max_right _ _
  have h3Mu : (0 : ℝ) < 3 * Mu + 1 := by linarith
  apply erdos_partition_limit_exists_of_hit
  filter_upwards [hwalls, eventually_ge_atTop (3 * N₀ + 3)] with J hWJ hJ
  obtain ⟨δ, ε, L, R₀, hδ0, hδ1, hε0, hεδ, hoverlap, hescape⟩ := hWJ
  set bnd := fun B => (3 * Mu + 1) * (ε B / δ B) with hbnddef
  have hbnd0 : ∀ B, 0 ≤ bnd B := fun B => by
    rw [hbnddef]; exact mul_nonneg h3Mu.le (div_nonneg (hε0 B) (hδ0 B).le)
  have hbnd : Tendsto bnd atTop (𝓝 0) := by
    have := hεδ.const_mul (3 * Mu + 1)
    simpa [hbnddef] using this
  refine tendsto_of_killed_doeblin_multiB (M := Mu) (rank := rnk)
    (Pt := killedKer Pker rnk J) (bnd := bnd)
    (hitVal_abs_le hMu0 hMu Pker_nonneg (fun n _ => Pker_sum_le_one n))
    rnk_tendsto_atTop
    (killedKer_Pker_nonneg J)
    (fun m => killedKer_row_sum (fun n hn => Pker_rowsum_rank hN₀2 hkm hJ hn) Pker_supp m)
    hbnd0 hbnd
    (fun B => ⟨δ B, R₀ B, L B, hδ0 B, hδ1 B,
      (fun n => killed_harmonic_pow Pker_supp (hitVal_eq Pker rnk J u) (L B) n),
      hoverlap B, fun R hR i hi => ?_⟩)
  -- escape ≤ ε B = δ B · bnd B / (3 Mu + 1)
  refine (hescape B R hR i hi).trans (le_of_eq ?_)
  have hδne : δ B ≠ 0 := (hδ0 B).ne'
  have h3ne : (3 * Mu + 1) ≠ 0 := h3Mu.ne'
  simp only [hbnddef]
  field_simp
end AnalyticCombinatorics.Ch8.Partitions.Erdos
