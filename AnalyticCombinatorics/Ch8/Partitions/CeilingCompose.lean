import AnalyticCombinatorics.Ch8.Partitions.CeilingValueWindow
import AnalyticCombinatorics.Ch8.Partitions.CeilingFactor
import AnalyticCombinatorics.Ch8.Partitions.MixtureOverlap

/-!
# TASK L5 (part 1): the composed in-band overlap `δ = α·β`

Composes the banked ceiling-level regeneration bricks into the **in-band overlap** required by the
variable rank-band engine (`hitVal_cauchy_of_ceilBand_overlap_escape_variable`):

  `α·β ≤ ∑_{z ∈ slice} min (enterBandKer Pker B n z) (enterBandKer Pker B n' z)`,

for `B = ceilBand R (A R)`, `C := R + A R`, `slice = B.filter (R ≤ rnk ·)`, and any two starts
`n, n'` of rank `≥ C`.

Mechanism (ChatGPT R7 ceiling route):
* **L3** (`Pker_hit_ceiling_level_mass_lower`): each start hits the ceiling **level** `{rnk = C}` with
  first-entrance mass `≥ α` (`ceilHit C n ≥ α`).
* **L2** (`enterBandKer_factor_through_ceiling_level`): the level-mixture
  `∑_{x ∈ L} (enterBandKer (ceilBand C 1) n x) · (enterBandKer B x z)` lower-bounds the true entrance
  law `enterBandKer B n z`.
* **L4** (`same_ceiling_enterBand_overlap`): any two level states `x, y` (both `rnk = C`) overlap by
  `≥ β` on the slice.
* **L1** (`overlap_of_mixtures_of_pairwise_overlap`): the two level-mixtures overlap by `≥ α·β`;
  since each mixture lower-bounds the true entrance law, so does the min — `δ = α·β`.

NEW file; imports the banked bricks, does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

set_option maxHeartbeats 1000000 in
/-- **Composed in-band overlap (`δ = α·β`).**  There is `δ > 0` so that eventually in `R`, for any two
starts `n, n'` of rank `≥ R + A R`, the first-entrance laws into `B = ceilBand R (A R)` overlap by
`≥ δ` on the in-band slice `{R ≤ rnk z}`.  Composition of L1–L4. -/
lemma Pker_ceilBand_inband_overlap (A : ℕ → ℕ) (hA : Tendsto A atTop atTop) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ R in atTop, ∀ n n', R + A R ≤ rnk n → R + A R ≤ rnk n' →
        δ ≤ ∑ z ∈ (ceilBand R (A R)).filter (fun z => R ≤ rnk z),
              min (enterBandKer Pker (ceilBand R (A R)) n z)
                  (enterBandKer Pker (ceilBand R (A R)) n' z) := by
  obtain ⟨α, hαpos, hαev⟩ := Pker_hit_ceiling_level_mass_lower
  obtain ⟨β, hβpos, hβev⟩ := same_ceiling_enterBand_overlap A hA
  refine ⟨α * β, by positivity, ?_⟩
  have htend := ceilRank_tendsto A
  -- L3 pulled to R (ceiling floor C = R + A R)
  have hαR : ∀ᶠ R in atTop, ∀ n, (R + A R) ≤ rnk n →
      α ≤ ∑ x ∈ (ceilBand (R + A R) 1).filter (fun x => (R + A R) ≤ rnk x),
            enterBandKer Pker (ceilBand (R + A R) 1) n x := htend.eventually hαev
  filter_upwards [hαR, hβev] with R hα hβ
  intro n n' hn hn'
  set C := R + A R with hCdef
  set B := ceilBand R (A R) with hBdef
  set L := (ceilBand C 1).filter (fun x => C ≤ rnk x) with hLdef
  -- weights a, b (ceiling-level entrance from n, n') and continuation kernel K
  set a : ℕ → ℝ := fun x => enterBandKer Pker (ceilBand C 1) n x with hadef
  set b : ℕ → ℝ := fun x => enterBandKer Pker (ceilBand C 1) n' x with hbdef
  set K : ℕ → ℕ → ℝ := fun x z => enterBandKer Pker B x z with hKdef
  -- L3: total level mass ≥ α
  have haL : α ≤ ∑ x ∈ L, a x := hα n hn
  have hbL : α ≤ ∑ x ∈ L, b x := hα n' hn'
  -- nonnegativity
  have ha0 : ∀ x, 0 ≤ a x := fun x => enterBandKer_nonneg (fun p q => Pker_nonneg p q) n x
  have hb0 : ∀ x, 0 ≤ b x := fun x => enterBandKer_nonneg (fun p q => Pker_nonneg p q) n' x
  have hK0 : ∀ x z, 0 ≤ K x z := fun x z => enterBandKer_nonneg (fun p q => Pker_nonneg p q) x z
  -- L4: pairwise overlap on slice for any two level states (rnk = C)
  have hpair : ∀ x ∈ L, ∀ y ∈ L,
      β ≤ ∑ z ∈ B.filter (fun z => R ≤ rnk z), min (K x z) (K y z) := by
    intro x hx y hy
    have hxrnk : rnk x = C := by
      have := Finset.mem_filter.mp hx
      have hlt := mem_ceilBand_iff.mp this.1
      have hge := this.2
      omega
    have hyrnk : rnk y = C := by
      have := Finset.mem_filter.mp hy
      have hlt := mem_ceilBand_iff.mp this.1
      have hge := this.2
      omega
    exact hβ x y hxrnk hyrnk
  -- L1: mixture overlap ≥ α·β
  have hmix := overlap_of_mixtures_of_pairwise_overlap
    (L := L) (slice := B.filter (fun z => R ≤ rnk z)) (a := a) (b := b) (K := K)
    (α := α) (β := β) hαpos.le ha0 hb0 haL hbL hK0 hpair
  -- L2: each mixture lower-bounds the true entrance law, pointwise on the slice
  refine le_trans hmix ?_
  apply Finset.sum_le_sum
  intro z _hz
  apply min_le_min
  · -- ∑_{x∈L} a x · K x z ≤ enterBandKer B n z
    exact enterBandKer_factor_through_ceiling_level R A n z hn
  · exact enterBandKer_factor_through_ceiling_level R A n' z hn'

#print axioms Pker_ceilBand_inband_overlap

end AnalyticCombinatorics.Ch8.Partitions.Erdos
