import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateWeightedSum
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentOne
import AnalyticCombinatorics.Ch8.Partitions.MassRateBasel

/-!
# Mass-rate campaign: `M₁` weak asymptotics

`|M₁(t) − 2(π²/6)/t³| ≤ 388/t²` on `0 < t ≤ 1`.  Split the Lambert identity
`M₁ = Σ'_{k} k·boseKernel2(tk)` via `boseKernel2 z = 2/z³ − boseReg0′(z)`: the singular part
sums (Basel) to `2(π²/6)/t³`, the remainder is `−Σ'_k k·boseReg0′(tk)`, bounded by the
weighted-decay keystone (`j=1`, `Cf=32`, `Bf=16`, `Df=2`).  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The kernel-derivative split: `boseKernel2 z = 2/z³ − boseReg0′(z)` for `z > 0`. -/
lemma boseKernel2_eq_inv_cube_sub_deriv {z : ℝ} (hz : 0 < z) :
    boseKernel2 z = 2 / z ^ 3 - boseReg0Deriv z := by
  have hy : 0 < Real.exp z - 1 := by
    have := Real.add_one_lt_exp (x := z) hz.ne'
    linarith
  rw [boseKernel2, boseReg0Deriv, Real.exp_neg]
  have hz3 : z ^ 3 ≠ 0 := by positivity
  have hexp : Real.exp z ≠ 0 := (Real.exp_pos z).ne'
  field_simp
  ring

/-- Global derivative bound: `|boseReg0′(z)| ≤ 64 e^{−z/2} + 2/z³` for all `z > 0`. -/
lemma boseReg0Deriv_global_bound {z : ℝ} (hz : 0 < z) :
    |boseReg0Deriv z| ≤ 64 * Real.exp (-z / 2) + 2 / z ^ 3 := by
  rcases le_or_gt z 1 with hz1 | hz1
  · have h1 := boseReg0Deriv_bdd_near_zero hz hz1
    have h2 : (32:ℝ) ≤ 64 * Real.exp (-z / 2) := by
      have hmono : Real.exp (-(1:ℝ) / 2) ≤ Real.exp (-z / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have hhalf : (1:ℝ) / 2 ≤ Real.exp (-(1:ℝ) / 2) := by
        have := Real.add_one_le_exp (-(1:ℝ) / 2); linarith
      nlinarith [hmono, hhalf]
    have h3 : (0:ℝ) ≤ 2 / z ^ 3 := by positivity
    linarith
  · have h1 := boseReg0Deriv_tail_bound hz1.le
    have h2 : (16:ℝ) * Real.exp (-z / 2) ≤ 64 * Real.exp (-z / 2) := by
      have := Real.exp_pos (-z / 2); nlinarith
    linarith

/-- Summability of `k·|boseReg0′(tk)|`. -/
lemma summable_weighted_absDeriv {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℕ => if k = 0 then (0:ℝ) else (k : ℝ) * |boseReg0Deriv (t * (k : ℝ))|) := by
  have hr0 : (0:ℝ) ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t / 2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hdom : Summable (fun k : ℕ =>
      (k : ℝ) * (64 * Real.exp (-t / 2) ^ k) + 2 / t ^ 3 * (1 / ((k : ℝ)) ^ 2)) := by
    apply Summable.add
    · have := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left 64
      refine this.congr fun k => ?_
      rw [pow_one]; ring
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
      have hg := boseReg0Deriv_global_bound htkpos
      have hexp_eq : Real.exp (-(t * (k : ℝ)) / 2) = Real.exp (-t / 2) ^ k := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      have htne : t ≠ 0 := ht.ne'
      have hpoly : (k : ℝ) * (2 / (t * (k : ℝ)) ^ 3) = 2 / t ^ 3 * (1 / (k : ℝ) ^ 2) := by
        rw [mul_pow, show (k : ℝ) ^ 3 = (k : ℝ) ^ 2 * (k : ℝ) from by ring]
        field_simp
      calc (k : ℝ) * |boseReg0Deriv (t * (k : ℝ))|
          ≤ (k : ℝ) * (64 * Real.exp (-(t * (k : ℝ)) / 2) + 2 / (t * (k : ℝ)) ^ 3) :=
            mul_le_mul_of_nonneg_left hg hkpos.le
        _ = (k : ℝ) * (64 * Real.exp (-t / 2) ^ k) + 2 / t ^ 3 * (1 / (k : ℝ) ^ 2) := by
            rw [mul_add, hexp_eq, hpoly]

/-- **`M₁` weak asymptotics**: `|M₁(t) − 2(π²/6)/t³| ≤ 388/t²` on `0 < t ≤ 1`. -/
theorem sigmaMoment_one_asymp_weak {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |sigmaMoment 1 t - 2 * (Real.pi ^ 2 / 6) / t ^ 3| ≤ 388 / t ^ 2 := by
  classical
  have hML := sigmaMoment_one_lambert ht0
  -- the two guarded families
  set hrem : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (k : ℝ) * boseReg0Deriv (t * (k : ℝ)) with hremdef
  set hmain : ℕ → ℝ := fun k => if k = 0 then (0:ℝ)
    else (2 / t ^ 3) * (1 / ((k : ℝ)) ^ 2) with hmaindef
  -- summability
  have hrem_summ : Summable hrem := by
    apply Summable.of_norm
    have habs := summable_weighted_absDeriv ht0
    refine habs.congr fun k => ?_
    simp only [hremdef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
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
    have := hb.mul_left (2 / t ^ 3)
    refine this.congr fun k => ?_
    simp only [hmaindef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk]
  -- per-term: the lambert summand = hmain − hrem
  have hterm : ∀ k : ℕ,
      (if k = 0 then (0:ℝ) else (k : ℝ) * boseKernel2 (t * (k : ℝ)))
        = hmain k - hrem k := by
    intro k
    simp only [hmaindef, hremdef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, if_neg hk]
      have hkpos : (0:ℝ) < (k : ℝ) := by
        have : 0 < k := Nat.pos_of_ne_zero hk; exact_mod_cast this
      have htkpos : 0 < t * (k : ℝ) := by positivity
      rw [boseKernel2_eq_inv_cube_sub_deriv htkpos]
      have htne : t ≠ 0 := ht0.ne'
      have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
      field_simp
  -- M₁ = Σ hmain − Σ hrem
  have hM1_eq : sigmaMoment 1 t = (∑' k, hmain k) - (∑' k, hrem k) := by
    rw [hML, tsum_congr hterm, hmain_summ.tsum_sub hrem_summ]
  -- Σ hmain = 2Z/t³
  have hmain_eq : (∑' k, hmain k) = 2 * (Real.pi ^ 2 / 6) / t ^ 3 := by
    have : (∑' k, hmain k) = (2 / t ^ 3) * ∑' k : ℕ, (if k = 0 then (0:ℝ) else 1 / ((k : ℝ)) ^ 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr; intro k
      simp only [hmaindef]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg hk]
    rw [this, tsum_if_inv_sq]
    ring
  -- bound |Σ hrem| via keystone
  have hrem_abs_bound : |∑' k, hrem k| ≤ 388 / t ^ 2 := by
    have hnorm : |∑' k, hrem k| ≤ ∑' k, |hrem k| := by
      have hns : Summable (fun k => ‖hrem k‖) := by
        have := summable_weighted_absDeriv ht0
        refine this.congr fun k => ?_
        simp only [hremdef]
        by_cases hk : k = 0
        · simp [hk]
        · rw [if_neg hk, if_neg hk, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
      have h1 := norm_tsum_le_tsum_norm hns
      rw [Real.norm_eq_abs] at h1
      refine le_trans h1 (le_of_eq (tsum_congr fun k => Real.norm_eq_abs _))
    refine le_trans hnorm ?_
    have habs_eq : (∑' k, |hrem k|)
        = ∑' k : ℕ, if k = 0 then (0:ℝ) else (k : ℝ) ^ 1 * |boseReg0Deriv (t * (k : ℝ))| := by
      apply tsum_congr; intro k
      simp only [hremdef]
      by_cases hk : k = 0
      · simp [hk]
      · rw [if_neg hk, if_neg hk, abs_mul, Nat.abs_cast, pow_one]
    rw [habs_eq]
    have hkey := weighted_decay_sum_bound 1 boseReg0Deriv 32 16 2
      (by norm_num) (by norm_num) (by norm_num)
      (fun z hz0 hz1 => boseReg0Deriv_bdd_near_zero hz0 hz1)
      (fun z hz1 => boseReg0Deriv_tail_bound hz1.le)
      ht0 ht1
    refine le_trans hkey (le_of_eq ?_)
    norm_num
  -- conclude
  rw [hM1_eq, hmain_eq]
  have harr : (2 * (Real.pi ^ 2 / 6) / t ^ 3 - ∑' k, hrem k) - 2 * (Real.pi ^ 2 / 6) / t ^ 3
      = -(∑' k, hrem k) := by ring
  rw [harr, abs_neg]
  exact hrem_abs_bound

end AnalyticCombinatorics.Ch8.Partitions.Erdos
