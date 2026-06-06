import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateDerivZero

/-!
# Mass-rate campaign: integrability of the derivative (R10 brick 18)

`boseReg0′` is integrable on `(0,∞)`: bounded by 32 on `(0,1]`, dominated by
`16e^{−x/2} + 2/x³` beyond 1.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `boseReg0Deriv` is globally measurable. -/
lemma boseReg0Deriv_measurable : Measurable boseReg0Deriv := by
  unfold boseReg0Deriv
  measurability

/-- Integrability of `boseReg0′` on `(0,1]`. -/
lemma boseReg0Deriv_integrableOn_Ioc01 : IntegrableOn boseReg0Deriv (Set.Ioc 0 1) := by
  have hmeas : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
  apply Measure.integrableOn_of_bounded (M := 32)
  · rw [Real.volume_Ioc]
    norm_num
  · exact boseReg0Deriv_measurable.aestronglyMeasurable
  · rw [ae_restrict_iff' hmeas]
    filter_upwards with x hx
    rw [Real.norm_eq_abs]
    exact boseReg0Deriv_bdd_near_zero hx.1 hx.2

/-- Integrability of `boseReg0′` on `(1,∞)`. -/
lemma boseReg0Deriv_integrableOn_Ioi1 : IntegrableOn boseReg0Deriv (Set.Ioi 1) := by
  have hmeas : MeasurableSet (Set.Ioi (1:ℝ)) := measurableSet_Ioi
  have hg1 : IntegrableOn (fun x : ℝ => 16 * Real.exp (-x / 2)) (Set.Ioi 1) := by
    have hbase : IntegrableOn (fun x : ℝ => Real.exp (-(1/2) * x)) (Set.Ioi 1) :=
      exp_neg_integrableOn_Ioi 1 (by norm_num : (0:ℝ) < 1/2)
    have hbase2 : IntegrableOn (fun x : ℝ => Real.exp (-x / 2)) (Set.Ioi 1) := by
      refine hbase.congr_fun (fun x _hx => ?_) hmeas
      ring_nf
    exact hbase2.const_mul (16 : ℝ)
  have hg2 : IntegrableOn (fun x : ℝ => 1 / x ^ 3) (Set.Ioi 1) := by
    have hr := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) (by norm_num : (0:ℝ) < 1)
    refine hr.congr_fun (fun x hx => ?_) hmeas
    have hxpos : (0:ℝ) < x := lt_trans zero_lt_one hx
    rw [Real.rpow_neg hxpos.le, one_div,
      show ((3:ℝ)) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hg2' := hg2.const_mul (2 : ℝ)
  have hg := hg1.add hg2'
  apply Integrable.mono' hg boseReg0Deriv_measurable.aestronglyMeasurable
  rw [ae_restrict_iff' hmeas]
  filter_upwards with x hx
  rw [Real.norm_eq_abs]
  have hb := boseReg0Deriv_tail_bound hx.le
  have heq : (2 : ℝ) / x ^ 3 = 2 * (1 / x ^ 3) := by ring
  linarith [le_of_eq heq]

/-- **Integrability of `boseReg0′` on `(0,∞)`** (R10 brick 18). -/
lemma boseReg0Deriv_integrable_Ioi : IntegrableOn boseReg0Deriv (Set.Ioi 0) := by
  have hsplit : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hsplit]
  exact boseReg0Deriv_integrableOn_Ioc01.union boseReg0Deriv_integrableOn_Ioi1

end AnalyticCombinatorics.Ch8.Partitions.Erdos
