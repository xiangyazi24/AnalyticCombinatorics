import AnalyticCombinatorics.Ch8.Partitions.CeilingCompose
import AnalyticCombinatorics.Ch8.Partitions.ErdosRenewalConnect
import AnalyticCombinatorics.Ch8.Partitions.ErdosLimit

/-!
# TASK L5 (part 2): the ceiling-route assembly into `erdos_partition_limit_exists`

This file wires the ceiling-level regeneration route through the variable rank-band engine
`hitVal_cauchy_of_ceilBand_overlap_escape_variable`.  The growing band width is
`A R = 1 + ⌊√(R+1)⌋` (unbounded, sublinear, positive).  The engine's overlap input is the banked
composed in-band overlap `Pker_ceilBand_inband_overlap` (δ = α·β, R8 elementary route via σ≥m).

The engine's remaining input is the **escape** (overshoot below the band floor `R` vanishes):

  `∀ᶠ R, ∀ n n', R + A R ≤ rnk n → R + A R ≤ rnk n' →
      (∑_{z ∈ B, rnk z < R} enterBandKer Pker B n z ≤ e R)
    ∧ (∑_{z ∈ B, rnk z < R} enterBandKer Pker B n' z ≤ e R)`,   `B = ceilBand R (A R)`, `e R → 0`.

`erdos_partition_limit_exists_of_escape` produces the unconditional limit **from** this escape pair;
the escape itself is the single genuine remaining analytic input (a matching-constant geometric
rank-drop tail two-sided bound).

NEW file; imports the banked bricks, does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The growing band width `A R = 1 + ⌊√(R+1)⌋`. -/
def ceilA (R : ℕ) : ℕ := 1 + Nat.sqrt (R + 1)

lemma ceilA_pos (R : ℕ) : 1 ≤ ceilA R := by unfold ceilA; omega

lemma ceilA_tendsto : Tendsto ceilA atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b * b, fun R hR => ?_⟩
  unfold ceilA
  have hsq : b ≤ Nat.sqrt (R + 1) := by
    rw [Nat.le_sqrt]; omega
  omega

lemma ceilA_unbounded : Tendsto ceilA atTop atTop := ceilA_tendsto

/-- `A R = 1 + ⌊√(R+1)⌋ ≤ R/2` eventually (√ grows sublinearly). -/
lemma ceilA_sublinear : ∀ᶠ R in atTop, ceilA R ≤ R / 2 := by
  filter_upwards [eventually_ge_atTop 64] with R hR
  unfold ceilA
  -- √(R+1) ≤ R/4 (since (R/4)² ≥ R+1 for R ≥ 64), then 1 + R/4 ≤ R/2
  have hsqr_lb : R + 1 ≤ (R / 4) * (R / 4) := by
    have h1 : 16 ≤ R / 4 := by omega
    have h2 : 4 * (R / 4) + 3 ≥ R := by omega
    nlinarith [h1, h2]
  have hsqrt : Nat.sqrt (R + 1) ≤ R / 4 := by
    have h := Nat.sqrt_le_sqrt hsqr_lb
    rwa [Nat.sqrt_eq] at h
  omega

lemma ceilA_pos_eventually : ∀ᶠ R in atTop, 1 ≤ ceilA R :=
  Eventually.of_forall ceilA_pos

/-- **The ceiling-route escape hypothesis.**  The first-entrance overshoot below the band floor `R`
into `B = ceilBand R (A R)` vanishes: there is `e R → 0` (nonneg) bounding the deep mass from any two
high starts.  This is the single genuine remaining analytic input of the ceiling route (L5-escape). -/
def CeilingEscape : Prop :=
  ∃ e : ℕ → ℝ, (∀ R, 0 ≤ e R) ∧ Tendsto e atTop (𝓝 0) ∧
    ∀ᶠ R in atTop, ∀ n n', R + ceilA R ≤ rnk n → R + ceilA R ≤ rnk n' →
      (∑ z ∈ (ceilBand R (ceilA R)).filter (fun z => ¬ R ≤ rnk z),
            enterBandKer Pker (ceilBand R (ceilA R)) n z ≤ e R)
      ∧ (∑ z ∈ (ceilBand R (ceilA R)).filter (fun z => ¬ R ≤ rnk z),
            enterBandKer Pker (ceilBand R (ceilA R)) n' z ≤ e R)

/-- **The Hardy–Ramanujan partition-ratio limit, modulo the ceiling escape.**  If the first-entrance
overshoot below the band floor vanishes (`CeilingEscape`), then the normalized partition sequence `u`
converges to a positive limit.  Everything else — the in-band overlap `δ = α·β` (R8 elementary route,
`Pker_ceilBand_inband_overlap`), the variable-band Doeblin engine, and the harmonic-hit reduction —
is banked clean-3. -/
theorem erdos_partition_limit_exists_of_escape (hesc : CeilingEscape) :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) := by
  obtain ⟨e, he0, hetend, hescev⟩ := hesc
  obtain ⟨Mu, hMu0, hMu⟩ := u_abs_le
  obtain ⟨δ, hδpos, hδev⟩ := Pker_ceilBand_inband_overlap ceilA ceilA_tendsto
  -- normalize δ ≤ 1 for the engine (cap at 1)
  set δ' := min δ 1 with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'le : δ' ≤ δ := min_le_left _ _
  -- kernelMass ≠ 0 for high rank
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 kernelMass_pos_eventually
  set N₀ := max N₁ 2 with hN₀def
  have hkmR : ∀ {J : ℕ}, 3 * N₀ + 3 ≤ J → ∀ m, J ≤ rnk m → kernelMass m ≠ 0 := by
    intro J hJ m hm
    have hge : N₀ ≤ m := rnk_ge_of (le_trans hJ hm)
    exact ne_of_gt (hN₁ m (le_trans (le_max_left _ _) hge))
  -- the engine's combined overlap+escape, for the fixed band width A = ceilA
  have hcombined : ∀ᶠ R in atTop, ∀ n n', R + ceilA R ≤ rnk n → R + ceilA R ≤ rnk n' →
      (δ' ≤ ∑ z ∈ (ceilBand R (ceilA R)).filter (fun z => R ≤ rnk z),
              min (enterBandKer Pker (ceilBand R (ceilA R)) n z)
                  (enterBandKer Pker (ceilBand R (ceilA R)) n' z))
      ∧ (∑ z ∈ (ceilBand R (ceilA R)).filter (fun z => ¬ R ≤ rnk z),
              enterBandKer Pker (ceilBand R (ceilA R)) n z ≤ e R)
      ∧ (∑ z ∈ (ceilBand R (ceilA R)).filter (fun z => ¬ R ≤ rnk z),
              enterBandKer Pker (ceilBand R (ceilA R)) n' z ≤ e R) := by
    filter_upwards [hδev, hescev] with R hov hesc
    intro n n' hn hn'
    obtain ⟨hesc1, hesc2⟩ := hesc n n' hn hn'
    exact ⟨le_trans hδ'le (hov n n' hn hn'), hesc1, hesc2⟩
  -- feed the variable engine for every cutoff J ≥ 3 N₀ + 3 ⟹ hhit
  apply erdos_partition_limit_exists_of_hit
  filter_upwards [eventually_ge_atTop (3 * N₀ + 3)] with J hJ
  refine hitVal_cauchy_of_ceilBand_overlap_escape_variable
    (J := J) (φ := u) (δ := δ') (Mφ := Mu) (e := e) (A := ceilA)
    ceilA_tendsto ceilA_sublinear ceilA_pos_eventually
    hδ'pos hδ'1 hMu0 hMu he0 hetend ?_ ?_ hcombined
  · -- hharm : J ≤ rnk m ⟹ hitVal harmonic at m
    intro m hm
    rw [hitVal_eq, if_neg (by omega)]
  · -- hkm : J ≤ rnk m ⟹ kernelMass m ≠ 0
    intro m hm
    exact hkmR hJ m hm

#print axioms erdos_partition_limit_exists_of_escape

end AnalyticCombinatorics.Ch8.Partitions.Erdos
