import AnalyticCombinatorics.Ch8.Partitions.TailSum
import AnalyticCombinatorics.Ch8.Partitions.LogOneMinusExpTail

/-!
# Concrete `log1mexp` tail trapezoid theorem (HR constant, brick 2 tail)

Instantiates the generic infinite-cell tail summation
`tail_trapezoid_bound_of_exp_cell_errors` at `a = trapR t`, `h = t`, `C = 4`,
`f = log1mexp`, and squeezes the geometric `O(t)` majorant to zero:

`∑_{j≥0} log1mexp((N+1+j)t) − (1/t)∫_{R}^{∞} log1mexp + ½·log1mexp(R) → 0`
as `t → 0⁺` (where `N = trapN t`, `R = trapR t = N·t`).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open scoped Topology BigOperators Interval

noncomputable section

/-- Near `0⁺`, the head cutoff `R(t) = N(t)·t` is eventually `≥ log 2`
(since `R → 1 > log 2`). -/
lemma eventually_log_two_le_trapR :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), Real.log 2 ≤ trapR t := by
  have h2e : (2 : ℝ) < Real.exp 1 := lt_of_lt_of_le (by norm_num) Real.exp_one_gt_d9.le
  have hlt : Real.log 2 < 1 := by
    calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) h2e
      _ = 1 := Real.log_exp 1
  exact trapR_tendsto_one.eventually (eventually_ge_nhds hlt)

/--
**Tail trapezoid theorem for `log1mexp`.**

The right-endpoint infinite tail after the head cutoff vanishes as `t → 0⁺`:
`∑_{j≥0} log1mexp((N+1+j)t) − (1/t)∫_{R}^{∞} log1mexp + ½·log1mexp(R) → 0`.
-/
theorem log1mexp_tail_trapezoid :
    Tendsto
      (fun t : ℝ =>
        (∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
          - (1 / t) * (∫ x in Set.Ioi (trapR t), log1mexp x)
          + (1 / 2 : ℝ) * log1mexp (trapR t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hbound :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ‖(∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
          - (1 / t) * (∫ x in Set.Ioi (trapR t), log1mexp x)
          + (1 / 2 : ℝ) * log1mexp (trapR t)‖
        ≤ (4 : ℝ) * t ^ 2 * (Real.exp (-(trapR t)) / (1 - Real.exp (-t))) := by
    filter_upwards [self_mem_nhdsWithin, eventually_log_two_le_trapR]
      with t ht hRlog2
    have htpos : 0 < t := ht
    have hcell : ∀ j : ℕ,
        |tailTrapErr log1mexp (trapR t) t j|
          ≤ 4 * Real.exp (-(trapR t + t * (j : ℝ))) * t ^ 2 := by
      intro j
      have haj : Real.log 2 ≤ trapR t + t * (j : ℝ) := by
        have hnon : 0 ≤ t * (j : ℝ) := by positivity
        linarith
      have hcellj := log1mexp_tail_cell_bound (a := trapR t + t * (j : ℝ))
        (h := t) htpos haj
      -- the j-th cell starts at `R + t·j`; its `(j+1)` upper endpoint is `R + t·j + t`
      have hcast : trapR t + t * ((j + 1 : ℕ) : ℝ) = trapR t + t * (j : ℝ) + t := by
        push_cast; ring
      unfold tailTrapErr
      rw [hcast]
      exact hcellj
    have htail :=
      tail_trapezoid_bound_of_exp_cell_errors
        (f := log1mexp) (a := trapR t) (h := t) (C := (4 : ℝ))
        htpos (by norm_num)
        (log1mexp_integrableOn_Ioi_tail hRlog2)
        (summable_log1mexp_tail_samples hRlog2 htpos)
        (log1mexp_tail_samples_tendsto_zero hRlog2 htpos)
        hcell
    have hsum_eq :
        (∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
          =
        ∑' j : ℕ, log1mexp (trapR t + t * ((j + 1 : ℕ) : ℝ)) := by
      apply tsum_congr
      intro j
      rw [trapR]
      congr 1
      push_cast
      ring
    rw [Real.norm_eq_abs, hsum_eq]
    exact htail
  exact squeeze_zero_norm' hbound tail_geometric_error_tendsto_zero

end

end AnalyticCombinatorics.Ch8.Partitions
