import AnalyticCombinatorics.Ch8.Partitions.LogOneMinusExpTail
import AnalyticCombinatorics.Ch8.Partitions.LogRegIntegrable

/-!
# `log1mexp` integrability and integral split on `(0,∞)` (HR constant, brick 2 assembly)

`log1mexp` is integrable on `Ioi 0` (singularity at `0` dissolved via
`log1mexp = log1mexpReg - log` on `(0,1]`, exponential tail on `(1,∞)`), and the
integral splits at any `R ≥ 0`: `∫₀ᴿ + ∫_{Ioi R} = ∫_{Ioi 0}`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory
open scoped Topology BigOperators Interval

noncomputable section

/-- `log1mexp` is integrable on `(0,∞)`. -/
lemma log1mexp_integrableOn_Ioi_zero :
    IntegrableOn log1mexp (Set.Ioi (0 : ℝ)) := by
  have hlog2_le_one : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  -- regularized part on `(0,1]`
  have hregII : IntervalIntegrable log1mexpReg MeasureTheory.volume (0 : ℝ) 1 :=
    log1mexpReg_intervalIntegrable_of_le
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
  have hreg : IntegrableOn log1mexpReg (Set.Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hregII
  -- `Real.log` interval-integrable through `0`
  have hlogII : IntervalIntegrable Real.log MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegral.intervalIntegrable_log'
  have hlog : IntegrableOn Real.log (Set.Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hlogII
  have hnear_sub : IntegrableOn (fun x : ℝ => log1mexpReg x - Real.log x) (Set.Ioc (0 : ℝ) 1) :=
    hreg.sub hlog
  have hnear : IntegrableOn log1mexp (Set.Ioc (0 : ℝ) 1) := by
    refine hnear_sub.congr_fun ?_ measurableSet_Ioc
    intro x hx
    simp [log1mexpReg]
  -- exponential tail on `(1,∞)`
  have htail : IntegrableOn log1mexp (Set.Ioi (1 : ℝ)) :=
    log1mexp_integrableOn_Ioi_tail hlog2_le_one
  have hsplit : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)
  rw [← hsplit]
  exact hnear.union htail

/-- Split the integral over `(0,∞)` at `R ≥ 0`:
`∫₀ᴿ log1mexp + ∫_{Ioi R} log1mexp = ∫_{Ioi 0} log1mexp`. -/
lemma log1mexp_integral_split {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in (0 : ℝ)..R, log1mexp x) + (∫ x in Set.Ioi R, log1mexp x)
      = ∫ x in Set.Ioi (0 : ℝ), log1mexp x := by
  have hglob : IntegrableOn log1mexp (Set.Ioi (0 : ℝ)) := log1mexp_integrableOn_Ioi_zero
  have hIoc : IntegrableOn log1mexp (Set.Ioc (0 : ℝ) R) :=
    hglob.mono_set (by intro x hx; exact hx.1)
  have hIoi : IntegrableOn log1mexp (Set.Ioi R) :=
    hglob.mono_set (by intro x hx; exact lt_of_le_of_lt hR hx)
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) R) (Set.Ioi R) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxIoc hxIoi
    have h1 := hxIoc.2
    have h2 := hxIoi
    simp only [Set.mem_Ioi] at h2
    linarith
  have hsplit : Set.Ioc (0 : ℝ) R ∪ Set.Ioi R = Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hR
  have hunion := MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIoc hIoi
  rw [hsplit] at hunion
  rw [intervalIntegral.integral_of_le hR]
  exact hunion.symm

end

end AnalyticCombinatorics.Ch8.Partitions
