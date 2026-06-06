import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateWeightedSum
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentTwo
import AnalyticCombinatorics.Ch8.Partitions.MassRateReg3
import AnalyticCombinatorics.Ch8.Partitions.MassRateBasel

/-!
# Mass-rate campaign: `M₂` weak asymptotics

`|M₂(t) − 6(π²/6)/t⁴| ≤ K/t³` on `0 < t ≤ 1`.  Split `M₂ = Σ'_{k} k²·boseKernel3(tk)` via
`boseKernel3 z = 6/z⁴ + reg3(z)`: singular part sums (Basel) to `6(π²/6)/t⁴`, remainder
`Σ'_k k²·reg3(tk)` bounded by the weighted-decay keystone (`j=2`, `Cf=3600`, `Df=6`).  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `reg3` tail bound: `|boseKernel3 z − 6/z⁴| ≤ (6/(1−e^{−1})⁴)·e^{−z/2} + 6/z⁴` for `z > 1`. -/
lemma reg3_tail {z : ℝ} (hz1 : 1 < z) :
    |boseKernel3 z - 6 / z ^ 4|
      ≤ (6 / (1 - Real.exp (-1)) ^ 4) * Real.exp (-z / 2) + 6 / z ^ 4 := by
  have hzpos : 0 < z := by linarith
  have hb3nn : 0 ≤ boseKernel3 z := boseKernel3_nonneg hzpos
  have hle := boseKernel3_le (by norm_num : (0:ℝ) < 1) hz1.le
  have hexp_le : Real.exp (-z) ≤ Real.exp (-z / 2) := by
    apply Real.exp_le_exp.mpr; linarith [Real.exp_pos (-z)]
  have htri : |boseKernel3 z - 6 / z ^ 4| ≤ |boseKernel3 z| + |6 / z ^ 4| := by
    rw [sub_eq_add_neg]
    exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
  rw [abs_of_nonneg hb3nn, abs_of_nonneg (by positivity : (0:ℝ) ≤ 6 / z ^ 4)] at htri
  have hDpos : (0:ℝ) < (1 - Real.exp (-1)) ^ 4 := by
    have he : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    have hb : (0:ℝ) < 1 - Real.exp (-1) := by linarith
    positivity
  have hstep : boseKernel3 z ≤ (6 / (1 - Real.exp (-1)) ^ 4) * Real.exp (-z / 2) := by
    refine hle.trans ?_
    rw [show 6 * Real.exp (-z) / (1 - Real.exp (-1)) ^ 4
        = (6 / (1 - Real.exp (-1)) ^ 4) * Real.exp (-z) from by ring]
    exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
  linarith [htri, hstep]

/-- Global `reg3` bound: `|reg3 z| ≤ B₃·e^{−z/2} + 3600/z⁴` for all `z > 0`. -/
lemma reg3_global_bound {z : ℝ} (hz : 0 < z) :
    |boseKernel3 z - 6 / z ^ 4|
      ≤ (6 / (1 - Real.exp (-1)) ^ 4) * Real.exp (-z / 2) + 3600 / z ^ 4 := by
  rcases le_or_gt z 1 with hz1 | hz1
  · have h1 := reg3_bdd_near_zero hz hz1
    have h2 : (3600:ℝ) ≤ 3600 / z ^ 4 := by
      rw [le_div_iff₀ (by positivity)]
      have : z ^ 4 ≤ 1 := pow_le_one₀ hz.le hz1
      nlinarith
    have h3 : (0:ℝ) ≤ (6 / (1 - Real.exp (-1)) ^ 4) * Real.exp (-z / 2) := by positivity
    linarith
  · have h1 := reg3_tail hz1
    have h2 : (6:ℝ) / z ^ 4 ≤ 3600 / z ^ 4 := by
      apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith

/-- Summability of `k²·|reg3(tk)|`. -/
lemma summable_weighted_absReg3 {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℕ => if k = 0 then (0:ℝ)
      else (k : ℝ) ^ 2 * |boseKernel3 (t * (k : ℝ)) - 6 / (t * (k : ℝ)) ^ 4|) := by
  have hr0 : (0:ℝ) ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t / 2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  set B₃ : ℝ := 6 / (1 - Real.exp (-1)) ^ 4 with hB3
  have hdom : Summable (fun k : ℕ =>
      (k : ℝ) ^ 2 * (B₃ * Real.exp (-t / 2) ^ k) + 3600 / t ^ 4 * (1 / ((k : ℝ)) ^ 2)) := by
    apply Summable.add
    · have := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left B₃
      refine this.congr fun k => ?_
      ring
    · have hb : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
      exact hb.mul_left _
  apply Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hdom
  · by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk]; positivity
  · by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk]
      have hkpos : (0:ℝ) < (k : ℝ) := by
        have : 0 < k := Nat.pos_of_ne_zero hk; exact_mod_cast this
      have htkpos : 0 < t * (k : ℝ) := by positivity
      have hg := reg3_global_bound htkpos
      have hexp_eq : Real.exp (-(t * (k : ℝ)) / 2) = Real.exp (-t / 2) ^ k := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      have htne : t ≠ 0 := ht.ne'
      have hpoly : (k : ℝ) ^ 2 * (3600 / (t * (k : ℝ)) ^ 4) = 3600 / t ^ 4 * (1 / (k : ℝ) ^ 2) := by
        rw [mul_pow, show (k : ℝ) ^ 4 = (k : ℝ) ^ 2 * (k : ℝ) ^ 2 from by ring]
        field_simp
      calc (k : ℝ) ^ 2 * |boseKernel3 (t * (k : ℝ)) - 6 / (t * (k : ℝ)) ^ 4|
          ≤ (k : ℝ) ^ 2 * (B₃ * Real.exp (-(t * (k : ℝ)) / 2) + 3600 / (t * (k : ℝ)) ^ 4) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [hB3]; exact hg
        _ = (k : ℝ) ^ 2 * (B₃ * Real.exp (-t / 2) ^ k) + 3600 / t ^ 4 * (1 / (k : ℝ) ^ 2) := by
            rw [mul_add, hexp_eq, hpoly]

/-- **`M₂` weak asymptotics**. -/
theorem sigmaMoment_two_asymp_weak {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |sigmaMoment 2 t - 6 * (Real.pi ^ 2 / 6) / t ^ 4|
      ≤ (3600 * 2 ^ 3 + (6 / (1 - Real.exp (-1)) ^ 4) * (Nat.factorial 2) * 4 ^ 3 + 2 * 6)
          / t ^ 3 := by
  classical
  have hML := sigmaMoment_two_lambert ht0
  set hrem : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (k : ℝ) ^ 2 * (boseKernel3 (t * (k : ℝ)) - 6 / (t * (k : ℝ)) ^ 4) with hremdef
  set hmain : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (6 / t ^ 4) * (1 / ((k : ℝ)) ^ 2) with hmaindef
  have hrem_summ : Summable hrem := by
    apply Summable.of_norm
    have habs := summable_weighted_absReg3 ht0
    refine habs.congr fun k => ?_
    simp only [hremdef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast]
  have hmain_summ : Summable hmain := by
    have hb : Summable (fun k : ℕ => if k = 0 then (0:ℝ) else 1 / ((k : ℝ)) ^ 2) := by
      have h0 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
      apply Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) h0
      · by_cases hk : k = 0
        · simp [hk]
        · rw [if_neg hk]; positivity
      · by_cases hk : k = 0
        · simp [hk]
        · rw [if_neg hk]
    have := hb.mul_left (6 / t ^ 4)
    refine this.congr fun k => ?_
    simp only [hmaindef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk]
  -- per-term: lambert summand = hmain + hrem
  have hterm : ∀ k : ℕ,
      (if k = 0 then (0:ℝ) else (k : ℝ) ^ 2 * boseKernel3 (t * (k : ℝ)))
        = hmain k + hrem k := by
    intro k
    simp only [hmaindef, hremdef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, if_neg hk]
      have hkpos : (0:ℝ) < (k : ℝ) := by
        have : 0 < k := Nat.pos_of_ne_zero hk; exact_mod_cast this
      have htne : t ≠ 0 := ht0.ne'
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      field_simp
      ring
  have hM2_eq : sigmaMoment 2 t = (∑' k, hmain k) + (∑' k, hrem k) := by
    rw [hML, tsum_congr hterm, hmain_summ.tsum_add hrem_summ]
  have hmain_eq : (∑' k, hmain k) = 6 * (Real.pi ^ 2 / 6) / t ^ 4 := by
    have : (∑' k, hmain k)
        = (6 / t ^ 4) * ∑' k : ℕ, (if k = 0 then (0:ℝ) else 1 / ((k : ℝ)) ^ 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr; intro k
      simp only [hmaindef]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg hk]
    rw [this, tsum_if_inv_sq]
    ring
  have hrem_abs_bound : |∑' k, hrem k|
      ≤ (3600 * 2 ^ 3 + (6 / (1 - Real.exp (-1)) ^ 4) * (Nat.factorial 2) * 4 ^ 3 + 2 * 6)
          / t ^ 3 := by
    have hnorm : |∑' k, hrem k| ≤ ∑' k, |hrem k| := by
      have hns : Summable (fun k => ‖hrem k‖) := by
        have := summable_weighted_absReg3 ht0
        refine this.congr fun k => ?_
        simp only [hremdef]
        by_cases hk : k = 0
        · simp [hk]
        · rw [if_neg hk, if_neg hk, Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast]
      have h1 := norm_tsum_le_tsum_norm hns
      rw [Real.norm_eq_abs] at h1
      refine le_trans h1 (le_of_eq (tsum_congr fun k => Real.norm_eq_abs _))
    refine le_trans hnorm ?_
    have habs_eq : (∑' k, |hrem k|)
        = ∑' k : ℕ, if k = 0 then (0:ℝ)
            else (k : ℝ) ^ 2 * |boseKernel3 (t * (k : ℝ)) - 6 / (t * (k : ℝ)) ^ 4| := by
      apply tsum_congr; intro k
      simp only [hremdef]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg hk, abs_mul, abs_pow, Nat.abs_cast]
    rw [habs_eq]
    exact weighted_decay_sum_bound 2 (fun z => boseKernel3 z - 6 / z ^ 4)
      3600 (6 / (1 - Real.exp (-1)) ^ 4) 6
      (by norm_num) (by positivity) (by norm_num)
      (fun z hz0 hz1 => reg3_bdd_near_zero hz0 hz1)
      (fun z hz1 => reg3_tail hz1)
      ht0 ht1
  rw [hM2_eq, hmain_eq]
  have harr : (6 * (Real.pi ^ 2 / 6) / t ^ 4 + ∑' k, hrem k) - 6 * (Real.pi ^ 2 / 6) / t ^ 4
      = ∑' k, hrem k := by ring
  rw [harr]
  exact hrem_abs_bound

end AnalyticCombinatorics.Ch8.Partitions.Erdos
