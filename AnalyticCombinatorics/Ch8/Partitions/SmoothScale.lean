import AnalyticCombinatorics.Ch8.Partitions.PartitionRenewal

/-!
# R7 Fact B via Doeblin: smooth scale vs floored rank

The floored rank `rnk n = ⌊3√n⌋` is NOT an approximate martingale (the fractional part `frac(3√n)`
contributes an `Θ(1)` phase obstruction).  The smooth scale `3√n` IS, so the occupation/Tanaka argument
runs on the smooth difference `3√x − 3√y`; the window is transferred back to the `rnk`-window with a
constant `+1` slack, since `|3√x − 3√y| ≤ |rnk x − rnk y| + 1`.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Window transfer:** the smooth scale `3√n` is within `1` of the floored rank `rnk = ⌊3√n⌋`, so a
`rnk`-window of width `W` becomes a smooth window of width `W + 1`. -/
lemma abs_smooth_sub_le_rnk_add_one (x y : ℕ) :
    |3 * Real.sqrt x - 3 * Real.sqrt y|
      ≤ ((Int.natAbs ((rnk x : ℤ) - (rnk y : ℤ))) : ℝ) + 1 := by
  have hax1 : (rnk x : ℝ) ≤ 3 * Real.sqrt x := by
    rw [rnk]; exact_mod_cast Nat.floor_le (by positivity)
  have hax2 : 3 * Real.sqrt x < (rnk x : ℝ) + 1 := by
    rw [rnk]; exact_mod_cast Nat.lt_floor_add_one (3 * Real.sqrt x)
  have hay1 : (rnk y : ℝ) ≤ 3 * Real.sqrt y := by
    rw [rnk]; exact_mod_cast Nat.floor_le (by positivity)
  have hay2 : 3 * Real.sqrt y < (rnk y : ℝ) + 1 := by
    rw [rnk]; exact_mod_cast Nat.lt_floor_add_one (3 * Real.sqrt y)
  have hnat : ((Int.natAbs ((rnk x : ℤ) - (rnk y : ℤ))) : ℝ)
      = |(rnk x : ℝ) - (rnk y : ℝ)| := by
    rw [Int.cast_natAbs]; push_cast; rfl
  rw [hnat, abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [hay2, hax1, neg_abs_le ((rnk x : ℝ) - (rnk y : ℝ))]
  · nlinarith [hax2, hay1, le_abs_self ((rnk x : ℝ) - (rnk y : ℝ))]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
