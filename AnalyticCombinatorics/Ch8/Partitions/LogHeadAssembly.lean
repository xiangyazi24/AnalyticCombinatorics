import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.TrapezoidHeadPos
import AnalyticCombinatorics.Ch8.Partitions.StirlingHead
import AnalyticCombinatorics.Ch8.Partitions.LogRegIntegrable

/-!
# Head asymptotic for `log1mexp` (HR constant, brick 2)

Combines the regularized head (`TrapezoidHeadPos`, integrability discharged via
`LogRegIntegrable`) with the singular Stirling head (`StirlingHead`, the `2π`
source), using `log1mexp = log1mexpReg - log` and `∫₀ᴿ log = R log R - R`:

  `headLog1mexp t - (1/t)∫₀ᴿ log1mexp - ½log(t/2π) - ½ log1mexpReg(R) → 0`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators Real
open scoped Topology BigOperators Interval

noncomputable section

/-- `headLog1mexp t = ∑_{k=1}^{N t} log1mexp(k·t)`. -/
noncomputable def headLog1mexp (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (trapN t), log1mexp ((k : ℝ) * t)

/-- The regularized head, integrability discharged via `LogRegIntegrable`. -/
lemma log1mexpReg_head_unconditional :
    Tendsto (fun t : ℝ =>
        (∑ k ∈ Finset.Icc 1 (trapN t), log1mexpReg ((k : ℝ) * t))
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), log1mexpReg x)
          - (1 / 2 : ℝ) * (log1mexpReg (trapR t) - log1mexpReg 0))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  log1mexpReg_head_trapezoid_tendsto_zero
    (fun _a _b ha hab hb => log1mexpReg_intervalIntegrable_of_le ha hab hb)

/-- **Head asymptotic for `log1mexp`** (the `2π` enters here via `singularHead_stirling`). -/
theorem log1mexp_head_asymp :
    Tendsto (fun t : ℝ =>
        headLog1mexp t
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), log1mexp x)
          - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))
          - (1 / 2 : ℝ) * log1mexpReg (trapR t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcomb := log1mexpReg_head_unconditional.add singularHead_stirling
  rw [add_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have hRle : trapR t ≤ 1 := by
    rw [trapR]
    calc ((trapN t : ℝ)) * t ≤ (1 / t) * t :=
          mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) htpos.le
      _ = 1 := by field_simp
  have hRnn : 0 ≤ trapR t := by rw [trapR]; positivity
  -- (A) sum identity:  Σ log1mexpReg(kt) + singularHead = headLog1mexp
  have hA : (∑ k ∈ Finset.Icc 1 (trapN t), log1mexpReg ((k : ℝ) * t)) + singularHead t
      = headLog1mexp t := by
    unfold singularHead headLog1mexp
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [log1mexpReg, mul_comm t (k : ℝ)]; ring
  -- (B) integral identity:  ∫ log1mexp = ∫ log1mexpReg - ∫ log
  have hII_reg : IntervalIntegrable log1mexpReg MeasureTheory.volume 0 (trapR t) :=
    log1mexpReg_intervalIntegrable_of_le le_rfl hRnn (le_trans hRle (by norm_num))
  have hII_log : IntervalIntegrable Real.log MeasureTheory.volume 0 (trapR t) :=
    intervalIntegral.intervalIntegrable_log'
  have hB : (∫ x in (0 : ℝ)..(trapR t), log1mexp x)
      = (∫ x in (0 : ℝ)..(trapR t), log1mexpReg x) - (∫ x in (0 : ℝ)..(trapR t), Real.log x) := by
    rw [← intervalIntegral.integral_sub hII_reg hII_log]
    apply intervalIntegral.integral_congr
    intro x _hx
    simp only [log1mexpReg]; ring
  -- (C) ∫₀ᴿ log = R log R - R
  have hlogint : (∫ x in (0 : ℝ)..(trapR t), Real.log x)
      = trapR t * Real.log (trapR t) - trapR t := by
    rw [integral_log]; simp
  have hC : log1mexpReg 0 = 0 := by simp [log1mexpReg, log1mexp]
  -- assemble
  unfold singularHeadMain
  rw [hC, hB, hlogint, ← hA]
  field_simp
  ring

end

end AnalyticCombinatorics.Ch8.Partitions
