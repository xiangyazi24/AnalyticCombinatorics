import AnalyticCombinatorics.Ch1.OGF.Pset
import AnalyticCombinatorics.Ch1.OGF.Sequence

/-!
# Ch1 §I.3 — Partitions into distinct parts (PSET flagship)

Flajolet & Sedgewick, Part A, Chapter I, §I.3. A partition of `n` into *distinct*
parts is a set of distinct positive integers summing to `n` — an object of
`PSET(ℙ)` of size `n`. Specializing the general powerset transfer `ogf_pset` to the
positive-integer class `ℙ` (`Cₘ=1`, `choose 1 k` supported on `{0,1}`) gives the
classical generating function

  `D(z) = ∏_{m≥1} (1 + z^m)`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

section
open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

local instance instTopRatDistinct : TopologicalSpace ℚ := ⊥
local instance instDiscRatDistinct : DiscreteTopology ℚ := ⟨rfl⟩

/-- **The generating function of partitions into distinct parts** (F&S §I.3):
`PSET(ℙ)(z) = ∏_{m≥1} (1 + z^m)`. -/
theorem CombClass.ogf_pset_posInt :
    CombClass.posInt.pset.ogf = ∏' i, (1 + (X : ℚ⟦X⟧) ^ (i + 1)) := by
  rw [CombClass.ogf_pset]
  refine tprod_congr fun i => ?_
  have hc : CombClass.posInt.counts (i + 1) = 1 := by simp [CombClass.counts_posInt]
  rw [hc, tsum_eq_sum (s := {0, 1}) (fun k hk => ?_)]
  · rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
    simp
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]

end

end AnalyticCombinatorics.Ch1
