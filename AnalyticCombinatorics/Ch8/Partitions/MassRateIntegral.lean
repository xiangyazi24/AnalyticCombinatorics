import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateAntideriv

/-!
# Mass-rate campaign: the boseReg0 integral (R10 bricks 7, 13)

`boseReg0` is integrable on `(0,∞)` (bounded by 4 on `(0,1]`, dominated by
`4e^{−x} + 1/x²` beyond 1) and

  `∫_{(0,∞)} boseReg0 = −1/2`,

via the antiderivative, the `ε → 0⁺` cut (`|∫_{(0,ε]}| ≤ 4ε`), and `F(0⁺) = 1/2`,
`F(∞) = 0`.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `boseReg0` is a.e. strongly measurable on `(0,∞)`-subsets. -/
lemma boseReg0_continuousOn_Ioi : ContinuousOn boseReg0 (Set.Ioi 0) :=
  fun x hx => (boseReg0_continuousAt hx).continuousWithinAt

/-- `boseReg0` is globally measurable (as a total formula). -/
lemma boseReg0_measurable : Measurable boseReg0 := by
  unfold boseReg0 boseKernel
  measurability

/-- Integrability on `(0,1]`. -/
lemma boseReg0_integrableOn_Ioc01 : IntegrableOn boseReg0 (Set.Ioc 0 1) := by
  have hmeas : MeasurableSet (Set.Ioc (0:ℝ) 1) := measurableSet_Ioc
  apply Measure.integrableOn_of_bounded (M := 4)
  · rw [Real.volume_Ioc]
    norm_num
  · exact boseReg0_measurable.aestronglyMeasurable
  · rw [ae_restrict_iff' hmeas]
    filter_upwards with x hx
    rw [Real.norm_eq_abs]
    exact boseReg0_bdd_near_zero hx.1 hx.2

/-- Integrability on `(1,∞)`. -/
lemma boseReg0_integrableOn_Ioi1 : IntegrableOn boseReg0 (Set.Ioi 1) := by
  have hmeas : MeasurableSet (Set.Ioi (1:ℝ)) := measurableSet_Ioi
  have haesm : AEStronglyMeasurable boseReg0 (volume.restrict (Set.Ioi (1:ℝ))) :=
    boseReg0_measurable.aestronglyMeasurable
  -- dominating function
  have hg1 : IntegrableOn (fun x : ℝ => 4 * Real.exp (-x)) (Set.Ioi 1) := by
    have hbase : IntegrableOn (fun x : ℝ => Real.exp (-1 * x)) (Set.Ioi 1) :=
      exp_neg_integrableOn_Ioi 1 one_pos
    have hbase2 : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 1) := by
      refine hbase.congr_fun (fun x _hx => ?_) hmeas
      norm_num
    have hfinal := hbase2.const_mul (4 : ℝ)
    exact hfinal
  have hg2 : IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Set.Ioi 1) := by
    have hr := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) (by norm_num : (0:ℝ) < 1)
    refine hr.congr_fun (fun x hx => ?_) hmeas
    have hxpos : (0:ℝ) < x := lt_trans zero_lt_one hx
    rw [Real.rpow_neg hxpos.le, one_div,
      show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hg := hg1.add hg2
  apply Integrable.mono' hg haesm
  rw [ae_restrict_iff' hmeas]
  filter_upwards with x hx
  rw [Real.norm_eq_abs]
  exact boseReg0_tail_bound hx.le

/-- **Integrability of `boseReg0` on `(0,∞)`** (R10 brick 7). -/
lemma boseReg0_integrable_Ioi : IntegrableOn boseReg0 (Set.Ioi 0) := by
  have hsplit : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hsplit]
  exact boseReg0_integrableOn_Ioc01.union boseReg0_integrableOn_Ioi1

/-- The tail integral: `∫_{(1,∞)} boseReg0 = −F(1)`. -/
lemma integral_Ioi_one_boseReg0 :
    ∫ x in Set.Ioi 1, boseReg0 x = -boseAntideriv 1 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := boseAntideriv) (f' := boseReg0) (a := 1)
    (fun x hx => boseAntideriv_hasDerivAt (lt_of_lt_of_le zero_lt_one hx))
    boseReg0_integrableOn_Ioi1
    boseAntideriv_tendsto_atTop
  rw [h]
  ring

/-- The near-zero piece: `∫_{(0,1]} boseReg0 = F(1) − 1/2`. -/
lemma integral_Ioc_zero_one_boseReg0 :
    ∫ x in Set.Ioc (0:ℝ) 1, boseReg0 x = boseAntideriv 1 - 1 / 2 := by
  -- for every ε ∈ (0,1]: ∫_{(0,1]} = ∫_{(0,ε]} + (F 1 − F ε)
  have hkey : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∫ x in Set.Ioc (0:ℝ) 1, boseReg0 x
        = (∫ x in Set.Ioc (0:ℝ) ε, boseReg0 x) + (boseAntideriv 1 - boseAntideriv ε) := by
    intro ε hε hε1
    have hsplit : Set.Ioc (0:ℝ) ε ∪ Set.Ioc ε 1 = Set.Ioc 0 1 :=
      Set.Ioc_union_Ioc_eq_Ioc hε.le hε1
    have hdisj : Disjoint (Set.Ioc (0:ℝ) ε) (Set.Ioc ε 1) :=
      Set.Ioc_disjoint_Ioc_of_le le_rfl
    have hint1 : IntegrableOn boseReg0 (Set.Ioc (0:ℝ) ε) :=
      boseReg0_integrableOn_Ioc01.mono_set
        (Set.Ioc_subset_Ioc le_rfl hε1)
    have hint2 : IntegrableOn boseReg0 (Set.Ioc ε 1) :=
      boseReg0_integrableOn_Ioc01.mono_set
        (Set.Ioc_subset_Ioc hε.le le_rfl)
    have hunion := MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2
    rw [hsplit] at hunion
    rw [hunion]
    congr 1
    -- ∫_{(ε,1]} = F 1 − F ε via the interval FTC
    have hftc := intervalIntegral_boseReg0_eq hε hε1
    rw [← hftc, intervalIntegral.integral_of_le hε1]
  -- the near-zero piece is O(ε)
  have hsmall : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |∫ x in Set.Ioc (0:ℝ) ε, boseReg0 x| ≤ 4 * ε := by
    intro ε hε hε1
    have hbound : ∀ x ∈ Set.Ioc (0:ℝ) ε, ‖boseReg0 x‖ ≤ 4 := by
      intro x hx
      rw [Real.norm_eq_abs]
      exact boseReg0_bdd_near_zero hx.1 (le_trans hx.2 hε1)
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Ioc (0:ℝ) ε) (C := 4)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) hbound
    rw [Real.norm_eq_abs] at h
    calc |∫ x in Set.Ioc (0:ℝ) ε, boseReg0 x|
        ≤ 4 * (volume (Set.Ioc (0:ℝ) ε)).toReal := h
      _ = 4 * ε := by
          rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
          ring
  -- pass to the limit ε → 0⁺
  have htend : Tendsto
      (fun ε : ℝ => (∫ x in Set.Ioc (0:ℝ) ε, boseReg0 x) + (boseAntideriv 1 - boseAntideriv ε))
      (𝓝[>] (0:ℝ)) (𝓝 (0 + (boseAntideriv 1 - 1 / 2))) := by
    apply Tendsto.add
    · -- the small piece → 0 by squeeze
      have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
          ‖∫ x in Set.Ioc (0:ℝ) ε, boseReg0 x‖ ≤ 4 * ε := by
        have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
          rw [mem_nhdsWithin]
          exact ⟨Set.Iio 1, isOpen_Iio, by norm_num,
            fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩
        filter_upwards [hmem] with ε hε
        rw [Real.norm_eq_abs]
        exact hsmall ε hε.1 hε.2
      have hgten : Tendsto (fun ε : ℝ => 4 * ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have hx0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        have h4 := hx0.const_mul (4:ℝ)
        rwa [mul_zero] at h4
      exact squeeze_zero_norm' hb hgten
    · apply Tendsto.sub tendsto_const_nhds
      exact boseAntideriv_tendsto_zero_right
  rw [zero_add] at htend
  -- the function is eventually constant = ∫_{(0,1]}
  have hconst : Tendsto
      (fun ε : ℝ => (∫ x in Set.Ioc (0:ℝ) ε, boseReg0 x) + (boseAntideriv 1 - boseAntideriv ε))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x in Set.Ioc (0:ℝ) 1, boseReg0 x)) := by
    have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio 1, isOpen_Iio, by norm_num,
        fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hmem] with ε hε
    exact (hkey ε hε.1 hε.2)
  exact tendsto_nhds_unique hconst htend

/-- **`∫_{(0,∞)} boseReg0 = −1/2`** (R10 brick 13). -/
theorem integral_boseReg0_Ioi :
    ∫ x in Set.Ioi (0:ℝ), boseReg0 x = -(1 / 2 : ℝ) := by
  have hsplit : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  have hdisj : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioi 1) :=
    Set.Ioc_disjoint_Ioi le_rfl
  have hunion := MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
    boseReg0_integrableOn_Ioc01 boseReg0_integrableOn_Ioi1
  rw [hsplit] at hunion
  rw [hunion, integral_Ioc_zero_one_boseReg0, integral_Ioi_one_boseReg0]
  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
