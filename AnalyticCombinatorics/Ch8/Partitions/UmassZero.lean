import AnalyticCombinatorics.Ch8.Partitions.EnergyBridge

/-!
# R7 Fact B via Doeblin: the unmatched mass tends to zero

Combining the D²-energy occupation control (`energy_controls_goodMass`) with the window-occupation bound
(`umass_le_one_sub_occupation`, giving `δ·∑goodMass ≤ 1`) shows the cumulative unmatched mass
`∑_{t<M} umass t ≤ K₀` is bounded uniformly in `M`.  Since `umass` is nonincreasing, `M·umass M ≤
∑_{t<M} umass t ≤ K₀`, so `umass M ≤ K₀/M → 0`.  This is the coalescence conclusion: the two coupled
killed chains' overlap → 1.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

include hPnn hPmass in
/-- `umass` is antitone. -/
lemma umass_antitone : Antitone (umass P rnk W i j) := by
  refine antitone_nat_of_succ_le (fun s => ?_)
  rw [umass_succ_eq P rnk W hPnn hPmass i j s]
  have : 0 ≤ ∑ x, ∑ y, Umat P rnk W i j s x y * cmass P rnk W x y :=
    Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
      mul_nonneg (Umat_nonneg P rnk W hPnn hPmass i j s x y) (cmass_nonneg P rnk W hPnn x y)))
  linarith

include hPnn hPmass in
lemma umass_nonneg (t : ℕ) : 0 ≤ umass P rnk W i j t :=
  Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
    Umat_nonneg P rnk W hPnn hPmass i j t x y))

include hPnn hPmass in
/-- **Coalescence: the unmatched mass tends to zero.** -/
theorem umass_tendsto_zero (D : α → α → ℝ) (c R δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hD : ∀ a b, (D a b) ^ 2 ≤ R ^ 2)
    (hrow_off : ∀ x y, ¬ GoodW rnk W x y →
        c ≤ (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) - (D x y) ^ 2)
    (hminor : ∀ x y, GoodW rnk W x y → δ ≤ cmass P rnk W x y) :
    Tendsto (umass P rnk W i j) atTop (𝓝 0) := by
  set K0 := (R ^ 2 + (c + R ^ 2) / δ) / c with hK0
  -- δ·∑goodMass ≤ 1  (from brick 81 and umass ≥ 0)
  have hgm : ∀ M, δ * ∑ t ∈ Finset.range M, goodMass P rnk W i j t ≤ 1 := by
    intro M
    have h81 := umass_le_one_sub_occupation P rnk W hPnn hPmass i j M δ hδ.le hminor
    linarith [umass_nonneg P rnk W hPnn hPmass i j M, h81]
  -- ∑ umass ≤ K0
  have hcR : 0 ≤ c + R ^ 2 := by nlinarith [hc, sq_nonneg R]
  have hsum : ∀ M, ∑ t ∈ Finset.range M, umass P rnk W i j t ≤ K0 := by
    intro M
    have he := energy_controls_goodMass P rnk W hPnn hPmass i j D c R hD hrow_off M
    have hgmle : ∑ t ∈ Finset.range M, goodMass P rnk W i j t ≤ 1 / δ := by
      rw [le_div_iff₀ hδ]; linarith [hgm M]
    have hg : (c + R ^ 2) * ∑ t ∈ Finset.range M, goodMass P rnk W i j t ≤ (c + R ^ 2) / δ := by
      rw [← mul_one_div]; exact mul_le_mul_of_nonneg_left hgmle hcR
    have hcK0 : c * K0 = R ^ 2 + (c + R ^ 2) / δ := by
      rw [hK0]; field_simp
    have hKle : c * ∑ t ∈ Finset.range M, umass P rnk W i j t ≤ c * K0 := by
      rw [hcK0]; linarith [he, hg]
    exact le_of_mul_le_mul_left hKle hc
  -- M · umass M ≤ ∑ umass ≤ K0
  have hMu : ∀ M : ℕ, (M : ℝ) * umass P rnk W i j M ≤ K0 := by
    intro M
    have hge : (M : ℝ) * umass P rnk W i j M ≤ ∑ t ∈ Finset.range M, umass P rnk W i j t := by
      have hle : ∑ t ∈ Finset.range M, umass P rnk W i j M
          ≤ ∑ t ∈ Finset.range M, umass P rnk W i j t :=
        Finset.sum_le_sum (fun t ht =>
          umass_antitone P rnk W hPnn hPmass i j (le_of_lt (Finset.mem_range.1 ht)))
      rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    exact le_trans hge (hsum M)
  -- squeeze: 0 ≤ umass M ≤ K0/M → 0
  have hg0 : Tendsto (fun n : ℕ => K0 / (n : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfg : ∀ᶠ M : ℕ in atTop, umass P rnk W i j M ≤ K0 / (M : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    rw [le_div_iff₀ (by exact_mod_cast hM : (0 : ℝ) < (M : ℝ))]
    linarith [hMu M]
  exact squeeze_zero' (Eventually.of_forall (umass_nonneg P rnk W hPnn hPmass i j)) hfg hg0

end AnalyticCombinatorics.Ch8.Partitions.Erdos
