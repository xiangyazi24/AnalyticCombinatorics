import AnalyticCombinatorics.Ch4.Analytic.Bridge
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic

open Filter
open scoped PowerSeries Topology

noncomputable section

namespace PowerSeries

def pole1 : PowerSeries ℂ := invUnitsSub (1 : ℂˣ)
def pole2 : PowerSeries ℂ := (invOneSubPow ℂ 2).val

lemma coeff_pole1 (n : ℕ) : coeff (R := ℂ) n pole1 = 1 := by
  simp [pole1]

lemma coeff_pole2_choose (n : ℕ) :
    coeff (R := ℂ) n pole2 = (Nat.choose (1 + n) 1 : ℂ) := by
  rw [pole2, invOneSubPow_val_succ_eq_mk_add_choose (S := ℂ) (d := 1)]
  simp

lemma coeff_pole2 (n : ℕ) : coeff (R := ℂ) n pole2 = (n + 1 : ℂ) := by
  rw [coeff_pole2_choose]
  simp [Nat.choose_one_right]
  ring

lemma one_sub_X_isUnit : IsUnit (1 - X : ℂ⟦X⟧) := by
  rw [isUnit_iff_constantCoeff]
  simp

lemma pole1_eq_inv_one_sub_X : pole1 = (1 - X : ℂ⟦X⟧)⁻¹ := by
  rw [pole1, eq_inv_iff_mul_eq_one]
  · simpa only [Units.val_one] using (invUnitsSub_mul_sub (u := (1 : ℂˣ)))
  · simp

lemma pole2_eq_inv_one_sub_X_sq : pole2 = (1 - X : ℂ⟦X⟧)⁻¹ ^ 2 := by
  rw [pole2]
  calc
    (invOneSubPow ℂ 2).val = ((1 - X : ℂ⟦X⟧) ^ 2)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      · exact (invOneSubPow ℂ 2).val_inv
      · simp
    _ = (1 - X : ℂ⟦X⟧)⁻¹ ^ 2 := by
      simp [pow_two]

lemma mapℂ_pole1 : mapℂ (invUnitsSub (1 : ℚˣ)) = pole1 := by
  rw [pole1]
  simpa [mapℂ] using
    (map_invUnitsSub (f := algebraMap ℚ ℂ) (u := (1 : ℚˣ)))

lemma mapℂ_pole2 : mapℂ ((invOneSubPow ℚ 2).val) = pole2 := by
  rw [pole2]
  ext n
  rw [coeff_mapℂ]
  rw [invOneSubPow_val_succ_eq_mk_add_choose (S := ℚ) (d := 1)]
  rw [invOneSubPow_val_succ_eq_mk_add_choose (S := ℂ) (d := 1)]
  simp

lemma analyticSum_pole1_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    analyticSum pole1 z = (1 - z)⁻¹ := by
  rw [analyticSum_eq_tsum]
  simpa [pole1] using (tsum_geometric_of_norm_lt_one (ξ := z) hz)

lemma analyticSum_pole2_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    analyticSum pole2 z = 1 / (1 - z) ^ 2 := by
  rw [analyticSum_eq_tsum]
  simpa [pole2, invOneSubPow_val_succ_eq_mk_add_choose, add_comm]
    using (tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) 1 (r := z) hz)

lemma analyticSum_pole2_inv_sq_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    analyticSum pole2 z = (1 - z)⁻¹ ^ 2 := by
  rw [analyticSum_eq_tsum]
  simpa [pole2, invOneSubPow_val_succ_eq_mk_add_choose, add_comm, div_eq_mul_inv]
    using (tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℂ) 1 (r := z) hz)

lemma analyticSum_pole1_of_mem_ball {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    analyticSum pole1 z = (1 - z)⁻¹ := by
  exact analyticSum_pole1_of_norm_lt_one
    (by simpa [Metric.mem_ball, dist_eq_norm] using hz)

lemma analyticSum_pole2_of_mem_ball {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    analyticSum pole2 z = 1 / (1 - z) ^ 2 := by
  exact analyticSum_pole2_of_norm_lt_one
    (by simpa [Metric.mem_ball, dist_eq_norm] using hz)

end PowerSeries

lemma meromorphicOrderAt_one_sub_inv :
    meromorphicOrderAt (fun z : ℂ => (1 - z)⁻¹) 1 = (-1 : ℤ) := by
  rw [meromorphicOrderAt_eq_int_iff
    (by fun_prop : MeromorphicAt (fun z : ℂ => (1 - z)⁻¹) 1)]
  refine ⟨fun _ : ℂ => (-1 : ℂ), by fun_prop, by norm_num, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := by simpa using hz
  have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne
  have hz1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz_ne.symm
  simp [smul_eq_mul]
  field_simp [hz', hz1, sub_eq_add_neg]
  ring

lemma meromorphicOrderAt_one_div_one_sub_sq :
    meromorphicOrderAt (fun z : ℂ => 1 / (1 - z) ^ 2) 1 = (-2 : ℤ) := by
  rw [meromorphicOrderAt_eq_int_iff
    (by fun_prop : MeromorphicAt (fun z : ℂ => 1 / (1 - z) ^ 2) 1)]
  refine ⟨fun _ : ℂ => (1 : ℂ), by fun_prop, one_ne_zero, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := by simpa using hz
  have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne
  have hz1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz_ne.symm
  simp [smul_eq_mul]
  field_simp [hz', hz1, sub_eq_add_neg]
  ring

lemma meromorphicOrderAt_one_sub_inv_sq :
    meromorphicOrderAt (fun z : ℂ => (1 - z)⁻¹ ^ 2) 1 = (-2 : ℤ) := by
  rw [meromorphicOrderAt_eq_int_iff
    (by fun_prop : MeromorphicAt (fun z : ℂ => (1 - z)⁻¹ ^ 2) 1)]
  refine ⟨fun _ : ℂ => (1 : ℂ), by fun_prop, one_ne_zero, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz_ne : z ≠ 1 := by simpa using hz
  have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne
  have hz1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz_ne.symm
  simp [smul_eq_mul]
  field_simp [hz', hz1, sub_eq_add_neg]
  ring
