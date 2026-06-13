import AnalyticCombinatorics.Ch8.Partitions.RankDropKer
import AnalyticCombinatorics.Ch8.Partitions.RankDropMinor
import AnalyticCombinatorics.Ch8.Partitions.RankDropTailMaj
import AnalyticCombinatorics.Ch8.Partitions.RankBandEntrance

/-!
# Ceiling-escape bricks 2 & 3: deep one-step mass ≤ tail majorant, and drop-1 minorization off-band

Two `∀ᶠ v` facts wiring the banked analytics into the abstract super-solution form needed by the
escape brick:

* `oneStep_deep_mass_le_rankDropTail`: for every off-band predecessor `v` (rank `≥ R + A`), the
  one-step *deep-crossing* mass `∑_{k ∈ ceilBand R A, rnk k < R} Pker v k` is `≤ rankDropTailMaj γ C₀
  (g + A)`, `g = rnk v − (R + A)`.  A deep landing `k` has rank drop `> g + A`, so the deep mass is
  bounded by the rank-drop tail beyond `g + A`, hence by the banked tail majorant.

* `rankDrop_one_mass_offBand_ge`: the drop-1 mass `∑_{k < v, rnk v − rnk k = 1} Pker v k = rankDropKer
  v 1 ≥ η` for every off-band `v`, directly from `Pker_rankDrop_minorization`.

NEW file; imports the banked bricks (tail majorant, minorization, kernel) and does not modify them.
Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Brick 2 — deep one-step mass ≤ rank-drop tail majorant (eventual in `v`).**

There are `γ > 0`, `C₀ ≥ 0` such that, eventually in `v`, for every floor `R` and band width `A` with
`R + A ≤ rnk v`, the deep one-step crossing mass (mass landing in `ceilBand R A` strictly below rank
`R`) is bounded by `rankDropTailMaj γ C₀ (g + A)`, where `g = rnk v − (R + A)`.

A deep landing `k` (rank `< R`, so `rnk v − rnk k > rnk v − R = g + A`) is a rank drop `> g + A`; so
the deep mass is `≤` the rank-drop tail beyond `g + A`, hence `≤` the banked majorant. -/
theorem oneStep_deep_mass_le_rankDropTail :
    ∃ (γ C₀ : ℝ), 0 < γ ∧ 0 ≤ C₀ ∧ ∀ᶠ v : ℕ in atTop, ∀ R A : ℕ,
        R + A ≤ rnk v →
        (∑ k ∈ (ceilBand R A).filter (fun k => ¬ R ≤ rnk k), Pker v k)
          ≤ rankDropTailMaj γ C₀ ((rnk v - (R + A)) + A) := by
  classical
  obtain ⟨γ, C₀, hγ, htail⟩ := Pker_rankDrop_tail_majorant
  -- bump C₀ to be nonnegative without weakening the bound (max C₀ 0)
  set C₀' : ℝ := max C₀ 0 with hC₀'def
  have hC₀'nn : 0 ≤ C₀' := le_max_right _ _
  have hC₀le : C₀ ≤ C₀' := le_max_left _ _
  refine ⟨γ, C₀', hγ, hC₀'nn, ?_⟩
  filter_upwards [htail, eventually_ge_atTop 100] with v htailv hv100
  intro R A hRAle
  set g : ℕ := rnk v - (R + A) with hgdef
  -- the deep mass is a sub-sum of Pker v · over predecessors with rank-drop > g + A
  have hsub :
      (∑ k ∈ (ceilBand R A).filter (fun k => ¬ R ≤ rnk k), Pker v k)
        ≤ ∑ k ∈ (Finset.range v).filter
              (fun k => (g + A) < rnk v - rnk k ∧ rnk v - rnk k < v), Pker v k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · -- deep ⊆ {drop > g+A ∧ drop < v}, as subsets of range v
      intro k hk
      rw [Finset.mem_filter, mem_ceilBand_iff] at hk
      obtain ⟨hkband, hkdeep⟩ := hk
      rw [not_le] at hkdeep
      -- k < v: rnk k < R ≤ R + A ≤ rnk v, and rnk strictly mono enough? use rnk_mono contrapositive
      have hkltv : k < v := by
        by_contra h
        push_neg at h
        have : rnk v ≤ rnk k := rnk_mono h
        omega
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨hkltv, ?_, ?_⟩
      · -- drop = rnk v − rnk k > g + A
        have hrnkv : rnk v = R + A + g := by omega
        have hkle : rnk k ≤ rnk v := rnk_mono hkltv.le
        omega
      · -- drop < v: rnk v − rnk k ≤ rnk v < v? not always; use drop ≤ rnk v and rnk v < v eventually.
        have hkle : rnk k ≤ rnk v := rnk_mono hkltv.le
        -- rnk v − rnk k ≤ rnk v ≤ 3√v < v for v ≥ 10; but to be safe bound by < v via k ≥ 1? Instead:
        -- the drop is < v because rnk v − rnk k ≤ rnk v and rnk v < v for v large; we have v large.
        have hrnkv_lt : rnk v < v := by
          -- rnk v = ⌊3√v⌋ ≤ 3√v < v for v ≥ 100
          have hbd := (rnk_sqrt_bounds v).1
          have hvR : (100 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv100
          have hvpos : (0 : ℝ) < (v : ℝ) := by linarith
          have hsv : Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) = (v : ℝ) :=
            Real.mul_self_sqrt hvpos.le
          have hsvpos : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hvpos
          have hsvge : (10 : ℝ) ≤ Real.sqrt (v : ℝ) := by
            nlinarith [hsv, hsvpos, hvR]
          have h3sv : 3 * Real.sqrt (v : ℝ) < (v : ℝ) := by nlinarith [hsv, hsvge, hsvpos]
          have : (rnk v : ℝ) < (v : ℝ) := by linarith
          exact_mod_cast this
        omega
    · intro k _ _; exact Pker_nonneg v k
  -- regroup that sub-sum as the rank-drop tail beyond g+A, then bound by the majorant
  have hmasseq :
      (∑ k ∈ (Finset.range v).filter
            (fun k => (g + A) < rnk v - rnk k ∧ rnk v - rnk k < v), Pker v k)
        = ∑ d ∈ (Finset.range v).filter ((g + A) < ·), rankDropKer v d :=
    (rankDropKer_tail_eq_mass v (g + A)).symm
  rw [hmasseq] at hsub
  refine le_trans hsub ?_
  refine le_trans (htailv (g + A)) ?_
  -- C₀·(g+A+1)·e^{−γ(g+A)} ≤ C₀'·(g+A+1)·e^{−γ(g+A)} = rankDropTailMaj γ C₀' (g+A)
  unfold rankDropTailMaj
  have hb : (0 : ℝ) ≤ ((g + A : ℕ) : ℝ) + 1 := by positivity
  have he : (0 : ℝ) ≤ Real.exp (-γ * ((g + A : ℕ) : ℝ)) := (Real.exp_pos _).le
  have hbe : (0 : ℝ) ≤ (((g + A : ℕ) : ℝ) + 1) * Real.exp (-γ * ((g + A : ℕ) : ℝ)) :=
    mul_nonneg hb he
  calc C₀ * (((g + A : ℕ) : ℝ) + 1) * Real.exp (-γ * ((g + A : ℕ) : ℝ))
      = C₀ * ((((g + A : ℕ) : ℝ) + 1) * Real.exp (-γ * ((g + A : ℕ) : ℝ))) := by ring
    _ ≤ C₀' * ((((g + A : ℕ) : ℝ) + 1) * Real.exp (-γ * ((g + A : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right hC₀le hbe
    _ = C₀' * (((g + A : ℕ) : ℝ) + 1) * Real.exp (-γ * ((g + A : ℕ) : ℝ)) := by ring

/-- **Brick 3 — drop-1 minorization off-band.**  There is `η > 0` so that, eventually in `v`, the
drop-1 mass `rankDropKer v 1 ≥ η`.  Direct use of `Pker_rankDrop_minorization` (drop-1 half). -/
theorem rankDrop_one_mass_offBand_ge :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ v : ℕ in atTop, η ≤ rankDropKer v 1 := by
  obtain ⟨η, hη, hminor⟩ := Pker_rankDrop_minorization
  refine ⟨η, hη, ?_⟩
  filter_upwards [hminor] with v hv
  exact hv.1

#print axioms oneStep_deep_mass_le_rankDropTail
#print axioms rankDrop_one_mass_offBand_ge

end AnalyticCombinatorics.Ch8.Partitions.Erdos
