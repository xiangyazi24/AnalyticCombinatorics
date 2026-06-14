import AnalyticCombinatorics.Ch8.Partitions.ErdosCeilingLimit
import AnalyticCombinatorics.Ch8.Partitions.EnterBandAdditiveEscape
import AnalyticCombinatorics.Ch8.Partitions.RankDropDeepMass
import AnalyticCombinatorics.Ch8.Partitions.RankDropTailMaj

/-!
# Ceiling-escape brick 5 (FINAL): `CeilingEscape` ⟹ the unconditional Hardy–Ramanujan limit

This is the last brick of the unconditional partition-ratio limit.  We instantiate the abstract
additive super-solution (`enterBand_deep_mass_le_of_tail_forcing_drop_one`, brick 4) with

* `U = rankDropTailMaj γ C₀` (banked deep-mass tail majorant, brick 2),
* `η` the banked drop-1 minorization (brick 3),
* band width `A = ceilA R`,

and set the escape bound `e R = (1/η)·∑'_i U(ceilA R + i)`.  Then:

* `e R ≥ 0`;
* `e R → 0`, because `ceilA R → ∞` and the shifted tail of `U` vanishes (`rankDropTailMaj_tail_tendsto_zero`);
* the deep first-entrance overshoot from any high start is `≤ e R` (brick 4 at floor `R`, whose
  off-band hypotheses are supplied by the eventual-in-`v` analytics: every off-band `v` has rank
  `≥ R + ceilA R`, hence `v` is large once `R` is large).

This produces `CeilingEscape`, and `erdos_partition_limit_exists_of_escape` concludes the
unconditional `erdos_partition_limit_exists`.

NEW file; imports the banked bricks; does not modify them.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Brick 5 — `CeilingEscape` from the banked analytics.** -/
theorem CeilingEscape_of_rankDropTail_dropOne : CeilingEscape := by
  classical
  -- banked analytics
  obtain ⟨γ, C₀, hγ, hC₀nn, hdeepev⟩ := oneStep_deep_mass_le_rankDropTail
  obtain ⟨η, hη, hdrop1ev⟩ := rankDrop_one_mass_offBand_ge
  set U : ℕ → ℝ := rankDropTailMaj γ C₀ with hUdef
  -- abstract U-facts (so the elaborator never unfolds the concrete majorant downstream)
  have hUnn : ∀ t, 0 ≤ U t := fun t => rankDropTailMaj_nonneg hC₀nn t
  have hUsummable : Summable U := rankDropTailMaj_summable hγ
  have hUtail : Tendsto (fun A : ℕ => ∑' i : ℕ, U (A + i)) atTop (𝓝 0) :=
    rankDropTailMaj_tail_tendsto_zero hC₀nn hγ
  clear_value U
  -- the escape bound e R = (1/η)·∑'_i U(ceilA R + i)
  set e : ℕ → ℝ := fun R => (1 / η) * ∑' i : ℕ, U (ceilA R + i) with hedef
  refine ⟨e, ?_, ?_, ?_⟩
  · -- e R ≥ 0
    intro R
    rw [hedef]
    apply mul_nonneg (by positivity)
    exact tsum_nonneg (fun i => hUnn _)
  · -- e R → 0
    rw [hedef]
    have hcomp : Tendsto (fun R : ℕ => ∑' i : ℕ, U (ceilA R + i)) atTop (𝓝 0) :=
      hUtail.comp ceilA_tendsto
    have := hcomp.const_mul (1 / η)
    simpa using this
  · -- the escape inequality eventually in R
    -- thresholds for the eventual-in-v facts (bricks 2,3) and kernelMass positivity
    obtain ⟨Vd, hVd⟩ := eventually_atTop.1 hdeepev
    obtain ⟨V1, hV1⟩ := eventually_atTop.1 hdrop1ev
    obtain ⟨Vk, hVk⟩ := eventually_atTop.1 kernelMass_pos_eventually
    set N := max (max Vd V1) (max Vk 2) with hNdef
    -- pick R so that R + ceilA R ≥ 3N+3 (then off-band v ⟹ v ≥ N)
    filter_upwards [eventually_ge_atTop (3 * N + 3)] with R hR
    intro n n' hn hn'
    -- abbreviations
    set A := ceilA R with hAdef
    set B := ceilBand R A with hBdef
    -- conversion: off-band v ⟹ v ≥ N (uses rnk v ≥ R + A ≥ 3N+3)
    have hvbig : ∀ v, v ∉ B → N ≤ v := by
      intro v hv
      have hrkge : R + A ≤ rnk v := not_mem_ceilBand_rank_ge hv
      have : 3 * N + 3 ≤ rnk v := le_trans (by omega) hrkge
      exact rnk_ge_of this
    -- brick-4 hypotheses, universally over off-band v
    have hPnn : ∀ a b, 0 ≤ Pker a b := Pker_nonneg
    have hPsupp : ∀ a b, a ≤ b → Pker a b = 0 := Pker_supp
    have hrow : ∀ v, v ∉ B → ∑ k ∈ Finset.range v, Pker v k = 1 := by
      intro v hv
      have hvN := hvbig v hv
      have hv2 : 2 ≤ v := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hvN
      have hvk : Vk ≤ v := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hvN
      exact Pker_mass hv2 (ne_of_gt (hVk v hvk))
    have hdeep : ∀ v, v ∉ B →
        (∑ k ∈ B.filter (fun k => ¬ R ≤ rnk k), Pker v k) ≤ U (A + (rnk v - (R + A))) := by
      intro v hv
      have hvN := hvbig v hv
      have hvd : Vd ≤ v := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hvN
      have hrkge : R + A ≤ rnk v := not_mem_ceilBand_rank_ge hv
      have h := hVd v hvd R A hrkge
      rwa [add_comm (rnk v - (R + A)) A] at h
    have hdrop1 : ∀ v, v ∉ B →
        η ≤ ∑ k ∈ (Finset.range v).filter (fun k => rnk v - rnk k = 1), Pker v k := by
      intro v hv
      have hvN := hvbig v hv
      have hv1 : V1 ≤ v := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hvN
      -- rankDropKer v 1 = the drop-1 mass by definition
      have hrk := hV1 v hv1
      rw [rankDropKer] at hrk
      exact hrk
    -- off-band membership from rank lower bounds
    have hnB : n ∉ B := by
      rw [hBdef]; intro hcon; have := mem_ceilBand_iff.mp hcon; omega
    have hn'B : n' ∉ B := by
      rw [hBdef]; intro hcon; have := mem_ceilBand_iff.mp hcon; omega
    -- apply brick 4 to n and n'
    have hesc_n := enterBand_deep_mass_le_of_tail_forcing_drop_one
      (P := Pker) (R := R) (A := A) (U := U) (η := η)
      hη hUnn hPnn hPsupp hrow hdeep hdrop1 n hnB
    have hesc_n' := enterBand_deep_mass_le_of_tail_forcing_drop_one
      (P := Pker) (R := R) (A := A) (U := U) (η := η)
      hη hUnn hPnn hPsupp hrow hdeep hdrop1 n' hn'B
    -- finite sum ≤ full tsum (1/η factor), giving ≤ e R
    have hsumA : Summable (fun i : ℕ => U (A + i)) := by
      have h := (summable_nat_add_iff A).mpr hUsummable
      apply h.congr; intro i; rw [add_comm]
    have hηinv : (0 : ℝ) ≤ 1 / η := by positivity
    have heR_eq : e R = (1 / η) * ∑' i : ℕ, U (A + i) := by
      rw [hedef, hAdef]
    have hfin_le_e : ∀ m : ℕ,
        (1 / η) * ∑ i ∈ Finset.range (m + 1), U (A + i) ≤ e R := by
      intro m
      rw [heR_eq]
      have hle : ∑ i ∈ Finset.range (m + 1), U (A + i) ≤ ∑' i : ℕ, U (A + i) :=
        hsumA.sum_le_tsum _ (fun i _ => hUnn _)
      exact mul_le_mul_of_nonneg_left hle hηinv
    have hgoal1 : ∑ z ∈ B.filter (fun z => ¬ R ≤ rnk z), enterBandKer Pker B n z ≤ e R := by
      rw [hBdef]; exact le_trans hesc_n (hfin_le_e _)
    have hgoal2 : ∑ z ∈ B.filter (fun z => ¬ R ≤ rnk z), enterBandKer Pker B n' z ≤ e R := by
      rw [hBdef]; exact le_trans hesc_n' (hfin_le_e _)
    exact ⟨hgoal1, hgoal2⟩

/-- **The unconditional Hardy–Ramanujan partition limit.**  The normalized partition sequence
`u n = n · p(n) · exp(-C·√n)`, `C = π√(2/3)`, `p n = card (Nat.Partition n)` (the repo's `u`, see
`ErdosKernel.lean`), converges to a positive limit.  Fully unconditional:
`CeilingEscape` is now banked clean-3 via the elementary additive escape route (R9), so the only
inputs are the banked rank-drop tail majorant and drop-1 minorization. -/
theorem erdos_partition_limit_exists :
    ∃ a : ℝ, 0 < a ∧ Tendsto u atTop (𝓝 a) :=
  erdos_partition_limit_exists_of_escape CeilingEscape_of_rankDropTail_dropOne

#print axioms CeilingEscape_of_rankDropTail_dropOne
#print axioms erdos_partition_limit_exists

end AnalyticCombinatorics.Ch8.Partitions.Erdos
