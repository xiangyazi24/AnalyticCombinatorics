import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateWeightedSum
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentThree
import AnalyticCombinatorics.Ch8.Partitions.MassRateReg4
import AnalyticCombinatorics.Ch8.Partitions.MassRateBasel

/-!
# Mass-rate campaign: `M₃` one-term asymptotics

`|M₃(t) − 24(π²/6)/t⁵| ≤ K/t⁴` on `0 < t ≤ 1`.  Split `M₃ = Σ'_{k} k³·boseKernel4(tk)` via
`boseKernel4 z = 24/z⁵ + reg4(z)`: singular part sums (Basel) to `24(π²/6)/t⁵`, remainder
`Σ'_k k³·reg4(tk)` bounded by the weighted-decay keystone (`j=3`, `Cf=2645`, `Df=24`).
Mirror of `MassRateMomentTwoAsymp`, powers shifted +1.  Opus-authored.
-/

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `reg4` tail bound: `|boseKernel4 z − 24/z⁵| ≤ (24/(1−e^{−1})⁵)·e^{−z/2} + 24/z⁵` for `z > 1`. -/
set_option maxHeartbeats 1000000 in
lemma reg4_tail {z : ℝ} (hz1 : 1 < z) :
    |boseKernel4 z - 24 / z ^ 5|
      ≤ (24 / (1 - Real.exp (-1)) ^ 5) * Real.exp (-z / 2) + 24 / z ^ 5 := by
  have hzpos : 0 < z := by linarith
  have hb4nn : 0 ≤ boseKernel4 z := boseKernel4_nonneg hzpos
  have hle := boseKernel4_le (by norm_num : (0:ℝ) < 1) hz1.le
  have hexp_le : Real.exp (-z) ≤ Real.exp (-z / 2) := by
    apply Real.exp_le_exp.mpr; linarith
  have htri : |boseKernel4 z - 24 / z ^ 5| ≤ |boseKernel4 z| + |24 / z ^ 5| := by
    rw [sub_eq_add_neg]
    exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
  rw [abs_of_nonneg hb4nn, abs_of_nonneg (by positivity : (0:ℝ) ≤ 24 / z ^ 5)] at htri
  have hDpos : (0:ℝ) < (1 - Real.exp (-1)) ^ 5 := by
    have he : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    have hb : (0:ℝ) < 1 - Real.exp (-1) := by linarith
    positivity
  have hstep : boseKernel4 z ≤ (24 / (1 - Real.exp (-1)) ^ 5) * Real.exp (-z / 2) := by
    refine hle.trans ?_
    rw [show 24 * Real.exp (-z) / (1 - Real.exp (-1)) ^ 5
        = (24 / (1 - Real.exp (-1)) ^ 5) * Real.exp (-z) from by ring]
    exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
  linarith [htri, hstep]

/-- Global `reg4` bound: `|reg4 z| ≤ B₄·e^{−z/2} + 2645/z⁵` for all `z > 0`. -/
set_option maxHeartbeats 1000000 in
lemma reg4_global_bound {z : ℝ} (hz : 0 < z) :
    |boseKernel4 z - 24 / z ^ 5|
      ≤ (24 / (1 - Real.exp (-1)) ^ 5) * Real.exp (-z / 2) + 2645 / z ^ 5 := by
  rcases le_or_gt z 1 with hz1 | hz1
  · have h1 := reg4_bdd_near_zero hz hz1
    have h2 : (2645:ℝ) ≤ 2645 / z ^ 5 := by
      rw [le_div_iff₀ (by positivity)]
      have : z ^ 5 ≤ 1 := pow_le_one₀ hz.le hz1
      nlinarith
    have he' : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    have h3 : (0:ℝ) ≤ (24 / (1 - Real.exp (-1)) ^ 5) * Real.exp (-z / 2) := by positivity
    linarith
  · have h1 := reg4_tail hz1
    have h2 : (24:ℝ) / z ^ 5 ≤ 2645 / z ^ 5 := by
      apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith

/-- Summability of `k³·|reg4(tk)|`. -/
set_option maxHeartbeats 1000000 in
lemma summable_weighted_absReg4 {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℕ => if k = 0 then (0:ℝ)
      else (k : ℝ) ^ 3 * |boseKernel4 (t * (k : ℝ)) - 24 / (t * (k : ℝ)) ^ 5|) := by
  have hr0 : (0:ℝ) ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t / 2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  set B₄ : ℝ := 24 / (1 - Real.exp (-1)) ^ 5 with hB4
  have hdom : Summable (fun k : ℕ =>
      (k : ℝ) ^ 3 * (B₄ * Real.exp (-t / 2) ^ k) + 2645 / t ^ 5 * (1 / ((k : ℝ)) ^ 2)) := by
    apply Summable.add
    · have := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left B₄
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
      have hg := reg4_global_bound htkpos
      have hexp_eq : Real.exp (-(t * (k : ℝ)) / 2) = Real.exp (-t / 2) ^ k := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      have htne : t ≠ 0 := ht.ne'
      have hpoly : (k : ℝ) ^ 3 * (2645 / (t * (k : ℝ)) ^ 5) = 2645 / t ^ 5 * (1 / (k : ℝ) ^ 2) := by
        rw [mul_pow, show (k : ℝ) ^ 5 = (k : ℝ) ^ 3 * (k : ℝ) ^ 2 from by ring]
        field_simp
      calc (k : ℝ) ^ 3 * |boseKernel4 (t * (k : ℝ)) - 24 / (t * (k : ℝ)) ^ 5|
          ≤ (k : ℝ) ^ 3 * (B₄ * Real.exp (-(t * (k : ℝ)) / 2) + 2645 / (t * (k : ℝ)) ^ 5) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [hB4]; exact hg
        _ = (k : ℝ) ^ 3 * (B₄ * Real.exp (-t / 2) ^ k) + 2645 / t ^ 5 * (1 / (k : ℝ) ^ 2) := by
            rw [mul_add, hexp_eq, hpoly]

/-- **`M₃` one-term asymptotic** `|M₃(t) − 24(π²/6)/t⁵| ≤ K/t⁴` on `0 < t ≤ 1`. -/
set_option maxHeartbeats 1000000 in
theorem sigmaMoment_three_one_term {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |sigmaMoment 3 t - 24 * (Real.pi ^ 2 / 6) / t ^ 5|
      ≤ (2645 * 2 ^ 4 + (24 / (1 - Real.exp (-1)) ^ 5) * (Nat.factorial 3) * 4 ^ 4 + 2 * 24)
          / t ^ 4 := by
  classical
  have hML := sigmaMoment_three_lambert ht0
  set hrem : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (k : ℝ) ^ 3 * (boseKernel4 (t * (k : ℝ)) - 24 / (t * (k : ℝ)) ^ 5) with hremdef
  set hmain : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (24 / t ^ 5) * (1 / ((k : ℝ)) ^ 2) with hmaindef
  have hrem_summ : Summable hrem := by
    apply Summable.of_norm
    have habs := summable_weighted_absReg4 ht0
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
    have := hb.mul_left (24 / t ^ 5)
    refine this.congr fun k => ?_
    simp only [hmaindef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk]
  -- per-term: lambert summand = hmain + hrem
  have hterm : ∀ k : ℕ,
      (if k = 0 then (0:ℝ) else (k : ℝ) ^ 3 * boseKernel4 (t * (k : ℝ)))
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
  have hM3_eq : sigmaMoment 3 t = (∑' k, hmain k) + (∑' k, hrem k) := by
    rw [hML, tsum_congr hterm, hmain_summ.tsum_add hrem_summ]
  have hmain_eq : (∑' k, hmain k) = 24 * (Real.pi ^ 2 / 6) / t ^ 5 := by
    have : (∑' k, hmain k)
        = (24 / t ^ 5) * ∑' k : ℕ, (if k = 0 then (0:ℝ) else 1 / ((k : ℝ)) ^ 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr; intro k
      simp only [hmaindef]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg hk]
    rw [this, tsum_if_inv_sq]
    ring
  have hrem_abs_bound : |∑' k, hrem k|
      ≤ (2645 * 2 ^ 4 + (24 / (1 - Real.exp (-1)) ^ 5) * (Nat.factorial 3) * 4 ^ 4 + 2 * 24)
          / t ^ 4 := by
    have hnorm : |∑' k, hrem k| ≤ ∑' k, |hrem k| := by
      have hns : Summable (fun k => ‖hrem k‖) := by
        have := summable_weighted_absReg4 ht0
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
            else (k : ℝ) ^ 3 * |boseKernel4 (t * (k : ℝ)) - 24 / (t * (k : ℝ)) ^ 5| := by
      apply tsum_congr; intro k
      simp only [hremdef]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg hk, abs_mul, abs_pow, Nat.abs_cast]
    rw [habs_eq]
    exact weighted_decay_sum_bound 3 (fun z => boseKernel4 z - 24 / z ^ 5)
      2645 (24 / (1 - Real.exp (-1)) ^ 5) 24
      (by norm_num) (have he' : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num; positivity) (by norm_num)
      (fun z hz0 hz1 => reg4_bdd_near_zero hz0 hz1)
      (fun z hz1 => reg4_tail hz1)
      ht0 ht1
  rw [hM3_eq, hmain_eq]
  have harr : (24 * (Real.pi ^ 2 / 6) / t ^ 5 + ∑' k, hrem k) - 24 * (Real.pi ^ 2 / 6) / t ^ 5
      = ∑' k, hrem k := by ring
  rw [harr]
  exact hrem_abs_bound

end AnalyticCombinatorics.Ch8.Partitions.Erdos
