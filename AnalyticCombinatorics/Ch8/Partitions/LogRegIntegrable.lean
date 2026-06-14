import AnalyticCombinatorics.Ch8.Partitions.LogRegLipschitz

/-!
# `log1mexpReg` is continuous (hence integrable) on `[0,2]` (HR constant, brick 2)

`log1mexpReg` extends continuously to `0` (value `0`, by `log1mexpReg_tendsto_zero`)
and is continuous on `(0,2]`, so it is `ContinuousOn (Icc 0 2)` and interval-integrable
on every subinterval — discharging the integrability hypothesis of the head theorem.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology
open scoped Topology Interval

noncomputable section

/-- `log1mexpReg` is continuous on `[0,2]` (continuous from the right at `0`,
value `0 = log1mexpReg 0`). -/
lemma log1mexpReg_continuousOn_Icc02 : ContinuousOn log1mexpReg (Set.Icc 0 2) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
  · subst hx0
    have hz : log1mexpReg 0 = 0 := by simp [log1mexpReg, log1mexp]
    rw [← Set.Ioc_insert_left (by norm_num : (0 : ℝ) ≤ 2), continuousWithinAt_insert_self,
      ContinuousWithinAt, hz]
    exact log1mexpReg_tendsto_zero.mono_left (nhdsWithin_mono 0 Set.Ioc_subset_Ioi_self)
  · exact (log1mexpReg_continuousAt_pos hxpos).continuousWithinAt

/-- Interval-integrability of `log1mexpReg` on subintervals of `[0,2]` (`a ≤ b`). -/
lemma log1mexpReg_intervalIntegrable_of_le {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    IntervalIntegrable log1mexpReg MeasureTheory.volume a b := by
  have h : ContinuousOn log1mexpReg (Set.Icc a b) :=
    log1mexpReg_continuousOn_Icc02.mono (Set.Icc_subset_Icc ha hb)
  rw [← Set.uIcc_of_le hab] at h
  exact h.intervalIntegrable

end

end AnalyticCombinatorics.Ch8.Partitions
