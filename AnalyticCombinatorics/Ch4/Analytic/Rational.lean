import AnalyticCombinatorics.Ch1.OGF.Compositions
import AnalyticCombinatorics.Ch4.Analytic.Poles
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

open Filter Asymptotics
open scoped PowerSeries Topology BigOperators

noncomputable section

namespace PowerSeries

lemma coeff_rescale_invOneSubPow (a : ℂ) (k n : ℕ) :
    coeff (R := ℂ) n (rescale a (invOneSubPow ℂ (k + 1)).val) =
      a ^ n * (Nat.choose (k + n) k : ℂ) := by
  rw [coeff_rescale, invOneSubPow_val_succ_eq_mk_add_choose]
  simp

lemma coeff_rescale_invUnitsSub_one (a : ℂ) (n : ℕ) :
    coeff (R := ℂ) n (rescale a (invUnitsSub (1 : ℂˣ))) = a ^ n := by
  simp [coeff_rescale]

lemma coeff_simplePoleSum {ι : Type*} (s : Finset ι) (c a : ι → ℂ) (n : ℕ) :
    coeff (R := ℂ) n
      (∑ i ∈ s, C (c i) * rescale (a i) (invUnitsSub (1 : ℂˣ))) =
        ∑ i ∈ s, c i * (a i) ^ n := by
  simp

lemma coeff_repeatedPoleSum {ι : Type*} (s : Finset ι)
    (c a : ι → ℂ) (k : ι → ℕ) (n : ℕ) :
    coeff (R := ℂ) n
      (∑ i ∈ s, C (c i) * rescale (a i) (invOneSubPow ℂ (k i + 1)).val) =
        ∑ i ∈ s, c i * (a i) ^ n *
          (Nat.choose (k i + n) (k i) : ℂ) := by
  simp [invOneSubPow_val_succ_eq_mk_add_choose, mul_assoc]

lemma coeff_coe_polynomial_eq_zero_of_natDegree_lt (P : Polynomial ℂ) {n : ℕ}
    (hn : P.natDegree < n) :
    coeff (R := ℂ) n (P : PowerSeries ℂ) = 0 := by
  simpa using Polynomial.coeff_eq_zero_of_natDegree_lt hn

lemma coeff_polynomialPlusSimplePoleSum_of_natDegree_lt {ι : Type*}
    (P : Polynomial ℂ) (s : Finset ι) (c a : ι → ℂ) {n : ℕ}
    (hn : P.natDegree < n) :
    coeff (R := ℂ) n
      ((P : PowerSeries ℂ) +
        ∑ i ∈ s, C (c i) * rescale (a i) (invUnitsSub (1 : ℂˣ))) =
        ∑ i ∈ s, c i * (a i) ^ n := by
  simp [coeff_coe_polynomial_eq_zero_of_natDegree_lt P hn]

end PowerSeries

lemma term_div_eq (ci ai c0 a0 : ℂ) (hc0 : c0 ≠ 0) (ha0 : a0 ≠ 0) (n : ℕ) :
    ci * ai ^ n / (c0 * a0 ^ n) = (ci / c0) * (ai / a0) ^ n := by
  field_simp [hc0, ha0, pow_ne_zero n ha0]
  rw [div_pow]
  field_simp [pow_ne_zero n ha0]

lemma dominant_tail_tendsto_zero {ι : Type*} (t : Finset ι)
    (c a : ι → ℂ) {i0 : ι}
    (hdom : ∀ i ∈ t, ‖a i / a i0‖ < 1) :
    Tendsto
      (fun n : ℕ => ∑ i ∈ t, (c i / c i0) * (a i / a i0) ^ n)
      atTop (𝓝 0) := by
  simpa using
    (tendsto_finset_sum (s := t)
      (f := fun i (n : ℕ) => (c i / c i0) * (a i / a i0) ^ n)
      (a := fun _ => 0)
      (by
        intro i hi
        simpa using tendsto_const_nhds.mul
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hdom i hi))))

lemma simplePoleSum_dominant_isEquivalent {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {i0 : ι} (hi0 : i0 ∈ s)
    (c a : ι → ℂ) (ha0 : a i0 ≠ 0) (hc0 : c i0 ≠ 0)
    (hdom : ∀ i ∈ s, i ≠ i0 → ‖a i‖ < ‖a i0‖) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
      (∑ i ∈ s, PowerSeries.C (c i) *
        PowerSeries.rescale (a i) (PowerSeries.invUnitsSub (1 : ℂˣ))))
      ~[atTop] (fun n : ℕ => c i0 * a i0 ^ n) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hratio :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
        (∑ i ∈ s, PowerSeries.C (c i) *
          PowerSeries.rescale (a i) (PowerSeries.invUnitsSub (1 : ℂˣ))) /
          (c i0 * a i0 ^ n))
        =ᶠ[atTop]
      (fun n : ℕ => 1 +
        ∑ i ∈ s.erase i0, (c i / c i0) * (a i / a i0) ^ n) := by
    exact Eventually.of_forall fun n => by
      change PowerSeries.coeff (R := ℂ) n
          (∑ i ∈ s, PowerSeries.C (c i) *
            PowerSeries.rescale (a i) (PowerSeries.invUnitsSub (1 : ℂˣ))) /
          (c i0 * a i0 ^ n) =
        1 + ∑ i ∈ s.erase i0, (c i / c i0) * (a i / a i0) ^ n
      rw [PowerSeries.coeff_simplePoleSum]
      rw [← Finset.insert_erase hi0]
      rw [Finset.sum_insert (by simp)]
      have hden : c i0 * a i0 ^ n ≠ 0 := mul_ne_zero hc0 (pow_ne_zero n ha0)
      rw [add_div, div_self hden]
      congr 1
      rw [Finset.sum_div]
      refine Finset.sum_congr ?_ ?_
      · simp
      intro i hi
      exact term_div_eq (c i) (a i) (c i0) (a i0) hc0 ha0 n
  have hdom' : ∀ i ∈ s.erase i0, ‖a i / a i0‖ < 1 := by
    intro i hi
    have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
    have his : i ∈ s := (Finset.mem_erase.mp hi).2
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr ha0)).2 (hdom i his hne)
  have htail :=
    dominant_tail_tendsto_zero (s.erase i0) c a (i0 := i0) hdom'
  have hmain :
      Tendsto
        (fun n : ℕ => 1 +
          ∑ i ∈ s.erase i0, (c i / c i0) * (a i / a i0) ^ n)
        atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add htail
  exact Tendsto.congr' hratio.symm hmain

lemma twoSimplePole_dominant_isEquivalent
    (c0 c1 a0 a1 : ℂ) (ha0 : a0 ≠ 0) (hc0 : c0 ≠ 0)
    (hdom : ‖a1‖ < ‖a0‖) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
      (PowerSeries.C c0 * PowerSeries.rescale a0
          (PowerSeries.invUnitsSub (1 : ℂˣ)) +
       PowerSeries.C c1 * PowerSeries.rescale a1
          (PowerSeries.invUnitsSub (1 : ℂˣ))))
      ~[atTop] (fun n : ℕ => c0 * a0 ^ n) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hratio :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
        (PowerSeries.C c0 * PowerSeries.rescale a0
            (PowerSeries.invUnitsSub (1 : ℂˣ)) +
         PowerSeries.C c1 * PowerSeries.rescale a1
            (PowerSeries.invUnitsSub (1 : ℂˣ))) /
        (c0 * a0 ^ n))
        =ᶠ[atTop]
      (fun n : ℕ => 1 + (c1 / c0) * (a1 / a0) ^ n) := by
    exact Eventually.of_forall fun n => by
      change PowerSeries.coeff (R := ℂ) n
          (PowerSeries.C c0 * PowerSeries.rescale a0
              (PowerSeries.invUnitsSub (1 : ℂˣ)) +
           PowerSeries.C c1 * PowerSeries.rescale a1
              (PowerSeries.invUnitsSub (1 : ℂˣ))) /
          (c0 * a0 ^ n) =
        1 + (c1 / c0) * (a1 / a0) ^ n
      have hden : c0 * a0 ^ n ≠ 0 := mul_ne_zero hc0 (pow_ne_zero n ha0)
      simp
      rw [add_div, div_self hden, term_div_eq c1 a1 c0 a0 hc0 ha0 n]
  have hratio_lt : ‖a1 / a0‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr ha0)).2 hdom
  have htail :
      Tendsto (fun n : ℕ => (c1 / c0) * (a1 / a0) ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hratio_lt)
  have hmain :
      Tendsto (fun n : ℕ => 1 + (c1 / c0) * (a1 / a0) ^ n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add htail
  exact Tendsto.congr' hratio.symm hmain

open AnalyticCombinatorics.Ch1

lemma coeff_mapℂ_ogf_compositions_isEquivalent :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
      (PowerSeries.mapℂ CombClass.compositions.ogf)) ~[atTop]
      (fun n : ℕ => (1 / 2 : ℂ) * (2 : ℂ) ^ n) := by
  apply Filter.EventuallyEq.isEquivalent
  filter_upwards [eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hn
  rw [PowerSeries.coeff_mapℂ, CombClass.coeff_ogf_compositions]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  norm_num
  ring
