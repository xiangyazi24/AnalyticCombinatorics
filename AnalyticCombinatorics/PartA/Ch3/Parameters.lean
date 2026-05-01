import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

open PowerSeries CombinatorialClass

/-! # Ch III — Combinatorial Parameters and Multivariate Generating Functions
    F&S Chapter III. -/

/-- A combinatorial parameter on `A` is a function `χ : A.Obj → ℕ`. -/
abbrev Parameter (A : CombinatorialClass) : Type _ := A.Obj → ℕ

namespace CombinatorialClass

/-- Joint count: number of objects of size `n` with parameter value `k`. -/
noncomputable def jointCount (A : CombinatorialClass) (χ : Parameter A) (n k : ℕ) : ℕ :=
  ((A.level n).filter (fun a => χ a = k)).card

/-- Each parameter fiber has cardinality at most the whole level. -/
theorem jointCount_le_count
    (A : CombinatorialClass) (χ : Parameter A) (n k : ℕ) :
    A.jointCount χ n k ≤ A.count n := by
  simpa [jointCount, count] using
    (Finset.card_filter_le (A.level n) (fun a => χ a = k))

/-- Sanity: summing over all parameter values present at size `n` recovers the size-only count. -/
theorem jointCount_sum_eq_count
    (A : CombinatorialClass) (χ : Parameter A) (n : ℕ) :
    ∑ k ∈ (A.level n).image χ, A.jointCount χ n k = A.count n := by
  simpa [jointCount, count] using
    (Finset.card_eq_sum_card_image χ (A.level n)).symm

end CombinatorialClass
