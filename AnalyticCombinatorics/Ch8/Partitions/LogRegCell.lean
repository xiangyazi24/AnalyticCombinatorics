import AnalyticCombinatorics.Ch8.Partitions.LogRegLipschitz
import AnalyticCombinatorics.Ch8.Partitions.TrapezoidCellIoc

/-!
# Per-cell trapezoid bound for `log1mexpReg` (HR constant, brick 2)

Combines `LogRegLipschitz` (`log1mexpReg' = boseAntideriv`, 5-Lipschitz on `(0,2]`)
with the open-left per-cell producer `cell_trapezoid_bound_of_lipschitz_deriv_Ioc`:
on every cell `[a,a+h] ⊆ (0,2]`, `|trap avg − integral avg| ≤ 5 h²`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open scoped Interval

noncomputable section

/-- Per-cell trapezoid bound for `log1mexpReg` on cells `[a,a+h]` with `a > 0`. -/
theorem log1mexpReg_cell_trapezoid_bound_pos :
    ∀ ⦃a h : ℝ⦄, 0 < h → 0 < a → a + h ≤ 2 →
      |((log1mexpReg a + log1mexpReg (a + h)) / 2)
          - (1 / h) * ∫ x in a..(a + h), log1mexpReg x| ≤ (5 : ℝ) * h ^ 2 := by
  refine cell_trapezoid_bound_of_lipschitz_deriv_Ioc (g := log1mexpReg)
    (gp := Erdos.boseAntideriv) (M := 5) (by norm_num) ?_ ?_ ?_ ?_
  · intro z hz; exact log1mexpReg_hasDerivAt_pos hz.1
  · intro u v hu huv _hv; exact log1mexpReg_intervalIntegrable_pos hu huv
  · intro u v hu huv _hv; exact boseAntideriv_intervalIntegrable_pos hu huv
  · exact boseAntideriv_lipschitz_Ioc02

end

end AnalyticCombinatorics.Ch8.Partitions
