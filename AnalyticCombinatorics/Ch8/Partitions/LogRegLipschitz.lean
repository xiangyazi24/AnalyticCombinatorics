import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.LogOneMinusExp
import AnalyticCombinatorics.Ch8.Partitions.MassRateAntideriv

/-!
# `log1mexpReg` has a Lipschitz derivative on `(0,2]` (HR constant, brick 2)

Key reuse (ChatGPT R5): the derivative of `log1mexpReg` on `(0,∞)` is exactly the
repo's Bose antiderivative `boseAntideriv x = 1/x - 1/(e^x-1)`, whose own derivative
is `boseReg0`. The mass-rate development ALREADY proved the hard removable-singularity
bound `|boseReg0| ≤ 4` near `0` (`boseReg0_bdd_near_zero`) plus a tail bound
(`boseReg0_tail_bound`). So `log1mexpReg`'s derivative is `5`-Lipschitz on `(0,2]`
with no new singularity analysis — exactly the `hcell` input the trapezoid machinery
needs (applied on cells `[a,a+h]` with `a > 0`, the head sum starting at `k=1`).
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators
open scoped Topology BigOperators Interval

noncomputable section

/-- Positive-side derivative of `log1mexpReg` is the Bose antiderivative. -/
lemma log1mexpReg_hasDerivAt_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt log1mexpReg (Erdos.boseAntideriv x) x := by
  have hf := log1mexp_hasDerivAt hx
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx.ne'
  have hraw : HasDerivAt log1mexpReg
      ((-Real.exp (-x) / (1 - Real.exp (-x))) + 1 / x) x := by
    simpa [log1mexpReg] using hf.add hlog
  convert hraw using 1
  rw [Erdos.boseAntideriv, Real.exp_neg]
  have hexp : Real.exp x ≠ 0 := Real.exp_ne_zero x
  have hden : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hx).ne'
  field_simp
  ring

/-- `log1mexpReg` is continuous at positive points. -/
lemma log1mexpReg_continuousAt_pos {x : ℝ} (hx : 0 < x) :
    ContinuousAt log1mexpReg x :=
  (log1mexpReg_hasDerivAt_pos hx).continuousAt

/-- Positive interval-integrability of `log1mexpReg`. -/
lemma log1mexpReg_intervalIntegrable_pos {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable log1mexpReg MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le huv] at hx
  exact (log1mexpReg_continuousAt_pos (lt_of_lt_of_le hu hx.1)).continuousWithinAt

/-- Positive interval-integrability of the derivative `boseAntideriv`. -/
lemma boseAntideriv_intervalIntegrable_pos {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable Erdos.boseAntideriv MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le huv] at hx
  exact (Erdos.boseAntideriv_hasDerivAt
    (lt_of_lt_of_le hu hx.1)).continuousAt.continuousWithinAt

/-- Uniform bound `|boseReg0| ≤ 5` on `(0,2]` (near-zero `≤ 4` + tail `≤ 5`). -/
lemma boseReg0_abs_le_five_Ioc02 {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 2) :
    |Erdos.boseReg0 x| ≤ 5 := by
  by_cases hx1 : x ≤ 1
  · exact le_trans (Erdos.boseReg0_bdd_near_zero hx.1 hx1) (by norm_num)
  · have h1x : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
    have htail := Erdos.boseReg0_tail_bound h1x
    have hexp_le_one : Real.exp (-x) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith [hx.1]
    have hexp_pos : 0 < Real.exp (-x) := Real.exp_pos _
    have hinv_le_one : 1 / x ^ 2 ≤ 1 := by
      have hx2pos : 0 < x ^ 2 := by positivity
      rw [div_le_iff₀ hx2pos]; nlinarith [h1x]
    calc |Erdos.boseReg0 x| ≤ 4 * Real.exp (-x) + 1 / x ^ 2 := htail
      _ ≤ 5 := by nlinarith [hexp_le_one, hinv_le_one, hexp_pos]

/-- `boseAntideriv` (= `log1mexpReg'`) is `5`-Lipschitz on `(0,2]`. -/
lemma boseAntideriv_lipschitz_Ioc02 :
    ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∀ w ∈ Set.Ioc (0 : ℝ) 2,
      |Erdos.boseAntideriv z - Erdos.boseAntideriv w| ≤ 5 * |z - w| := by
  intro z hz w hw
  have hderiv : ∀ x ∈ Set.uIcc z w, HasDerivAt Erdos.boseAntideriv (Erdos.boseReg0 x) x := by
    intro x hx
    have hxpos : 0 < x := by
      rcases le_total z w with hzw | hwz
      · rw [Set.uIcc_of_le hzw] at hx; exact lt_of_lt_of_le hz.1 hx.1
      · rw [Set.uIcc_comm, Set.uIcc_of_le hwz] at hx; exact lt_of_lt_of_le hw.1 hx.1
    exact Erdos.boseAntideriv_hasDerivAt hxpos
  have hcont : ContinuousOn Erdos.boseReg0 (Set.uIcc z w) := by
    intro x hx
    have hxpos : 0 < x := by
      rcases le_total z w with hzw | hwz
      · rw [Set.uIcc_of_le hzw] at hx; exact lt_of_lt_of_le hz.1 hx.1
      · rw [Set.uIcc_comm, Set.uIcc_of_le hwz] at hx; exact lt_of_lt_of_le hw.1 hx.1
    exact (Erdos.boseReg0_continuousAt hxpos).continuousWithinAt
  have hint : IntervalIntegrable Erdos.boseReg0 MeasureTheory.volume z w :=
    hcont.intervalIntegrable
  have hFTC : (∫ x in z..w, Erdos.boseReg0 x) = Erdos.boseAntideriv w - Erdos.boseAntideriv z :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hpoint : ∀ x ∈ Set.uIoc z w, ‖Erdos.boseReg0 x‖ ≤ (5 : ℝ) := by
    intro x hx
    have hxI : x ∈ Set.Ioc (0 : ℝ) 2 := by
      rcases le_total z w with hzw | hwz
      · rw [Set.uIoc_of_le hzw] at hx
        exact ⟨lt_of_lt_of_le hz.1 (le_of_lt hx.1), le_trans hx.2 hw.2⟩
      · rw [Set.uIoc_comm, Set.uIoc_of_le hwz] at hx
        exact ⟨lt_of_lt_of_le hw.1 (le_of_lt hx.1), le_trans hx.2 hz.2⟩
    rw [Real.norm_eq_abs]; exact boseReg0_abs_le_five_Ioc02 hxI
  have hnorm : ‖∫ x in z..w, Erdos.boseReg0 x‖ ≤ (5 : ℝ) * |w - z| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc |Erdos.boseAntideriv z - Erdos.boseAntideriv w|
        = ‖∫ x in z..w, Erdos.boseReg0 x‖ := by rw [hFTC, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ (5 : ℝ) * |w - z| := hnorm
    _ = (5 : ℝ) * |z - w| := by rw [abs_sub_comm]

end

end AnalyticCombinatorics.Ch8.Partitions
