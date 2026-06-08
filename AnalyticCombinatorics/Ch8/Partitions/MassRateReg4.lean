import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateBoseKernel4
import AnalyticCombinatorics.Ch8.Partitions.MassRateExpBounds

/-!
# Near-zero certificate for `reg4 = boseKernel4 − 24/z⁵`

`|boseKernel4 z − 24/z⁵| ≤ 2645` on `(0,1]`, via the degree-10 cancellation certificate
(`y = e^z − 1`, `boseKernel4 = (24+60y+50y²+15y³+y⁴)/y⁵`, Taylor `P5` of order 5).
Mirror of `MassRateReg3`, one order higher.  Opus-authored (sympy-generated polynomials).
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Taylor remainder: `|e^z − 1 − (z + z²/2 + z³/6 + z⁴/24 + z⁵/120)| ≤ z⁶` on `[0,1]`. -/
lemma exp_sub_one_order5_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.exp x - 1 - x - x ^ 2 / 2 - x ^ 3 / 6 - x ^ 4 / 24 - x ^ 5 / 120| ≤ x ^ 6 := by
  have habs : |x| ≤ 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h := Real.exp_bound habs (n := 6) (by norm_num)
  have hsum : ∑ i ∈ Finset.range 6, x ^ i / (Nat.factorial i : ℝ)
      = 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
  rw [hsum] at h
  have habs6 : |x| ^ 6 = x ^ 6 := by rw [abs_of_nonneg hx0]
  rw [habs6] at h
  calc |Real.exp x - 1 - x - x ^ 2 / 2 - x ^ 3 / 6 - x ^ 4 / 24 - x ^ 5 / 120|
      = |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120)| := by ring_nf
    _ ≤ x ^ 6 * ((6 : ℕ).succ / ((Nat.factorial 6 : ℝ) * 6)) := h
    _ ≤ x ^ 6 := by
        have hx6 : (0 : ℝ) ≤ x ^ 6 := by positivity
        have hc : ((6 : ℕ).succ : ℝ) / ((Nat.factorial 6 : ℝ) * 6) ≤ 1 := by norm_num [Nat.factorial]
        nlinarith [hx6, hc]

lemma reg4_Q0_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(1/6 : ℝ) + (5/18 : ℝ) * z ^ 1 + (13/48 : ℝ) * z ^ 2 + (421/2160 : ℝ) * z ^ 3 + (109/960 : ℝ) * z ^ 4 + (577/10368 : ℝ) * z ^ 5 + (121/5184 : ℝ) * z ^ 6 + (4409/518400 : ℝ) * z ^ 7 + (5591/2073600 : ℝ) * z ^ 8 + (1541/2073600 : ℝ) * z ^ 9 + (1463/8294400 : ℝ) * z ^ 10 + (23/648000 : ℝ) * z ^ 11 + (41/6912000 : ℝ) * z ^ 12 + (1/1296000 : ℝ) * z ^ 13 + (1/13824000 : ℝ) * z ^ 14 + (1/259200000 : ℝ) * z ^ 15| ≤ (2 : ℝ) := by
  have hp1 : z ^ 1 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp4 : z ^ 4 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp5 : z ^ 5 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp6 : z ^ 6 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp7 : z ^ 7 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp8 : z ^ 8 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp9 : z ^ 9 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp10 : z ^ 10 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp11 : z ^ 11 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp12 : z ^ 12 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp13 : z ^ 13 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp14 : z ^ 14 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp15 : z ^ 15 ≤ 1 := pow_le_one₀ hz0 hz1
  have hn1 : (0:ℝ) ≤ z ^ 1 := by positivity
  have hn2 : (0:ℝ) ≤ z ^ 2 := by positivity
  have hn3 : (0:ℝ) ≤ z ^ 3 := by positivity
  have hn4 : (0:ℝ) ≤ z ^ 4 := by positivity
  have hn5 : (0:ℝ) ≤ z ^ 5 := by positivity
  have hn6 : (0:ℝ) ≤ z ^ 6 := by positivity
  have hn7 : (0:ℝ) ≤ z ^ 7 := by positivity
  have hn8 : (0:ℝ) ≤ z ^ 8 := by positivity
  have hn9 : (0:ℝ) ≤ z ^ 9 := by positivity
  have hn10 : (0:ℝ) ≤ z ^ 10 := by positivity
  have hn11 : (0:ℝ) ≤ z ^ 11 := by positivity
  have hn12 : (0:ℝ) ≤ z ^ 12 := by positivity
  have hn13 : (0:ℝ) ≤ z ^ 13 := by positivity
  have hn14 : (0:ℝ) ≤ z ^ 14 := by positivity
  have hn15 : (0:ℝ) ≤ z ^ 15 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15]⟩

lemma reg4_Q1_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(-120 : ℝ) + (-180 : ℝ) * z ^ 1 + (-160 : ℝ) * z ^ 2 + (-105 : ℝ) * z ^ 3 + (-335/6 : ℝ) * z ^ 4 + (-295/12 : ℝ) * z ^ 5 + (-80/9 : ℝ) * z ^ 6 + (-191/72 : ℝ) * z ^ 7 + (-1307/2160 : ℝ) * z ^ 8 + (-713/8640 : ℝ) * z ^ 9 + (1/120 : ℝ) * z ^ 10 + (17/1728 : ℝ) * z ^ 11 + (1267/345600 : ℝ) * z ^ 12 + (7/7200 : ℝ) * z ^ 13 + (31/172800 : ℝ) * z ^ 14 + (1/43200 : ℝ) * z ^ 15 + (1/576000 : ℝ) * z ^ 16| ≤ (658 : ℝ) := by
  have hp1 : z ^ 1 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp4 : z ^ 4 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp5 : z ^ 5 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp6 : z ^ 6 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp7 : z ^ 7 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp8 : z ^ 8 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp9 : z ^ 9 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp10 : z ^ 10 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp11 : z ^ 11 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp12 : z ^ 12 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp13 : z ^ 13 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp14 : z ^ 14 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp15 : z ^ 15 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp16 : z ^ 16 ≤ 1 := pow_le_one₀ hz0 hz1
  have hn1 : (0:ℝ) ≤ z ^ 1 := by positivity
  have hn2 : (0:ℝ) ≤ z ^ 2 := by positivity
  have hn3 : (0:ℝ) ≤ z ^ 3 := by positivity
  have hn4 : (0:ℝ) ≤ z ^ 4 := by positivity
  have hn5 : (0:ℝ) ≤ z ^ 5 := by positivity
  have hn6 : (0:ℝ) ≤ z ^ 6 := by positivity
  have hn7 : (0:ℝ) ≤ z ^ 7 := by positivity
  have hn8 : (0:ℝ) ≤ z ^ 8 := by positivity
  have hn9 : (0:ℝ) ≤ z ^ 9 := by positivity
  have hn10 : (0:ℝ) ≤ z ^ 10 := by positivity
  have hn11 : (0:ℝ) ≤ z ^ 11 := by positivity
  have hn12 : (0:ℝ) ≤ z ^ 12 := by positivity
  have hn13 : (0:ℝ) ≤ z ^ 13 := by positivity
  have hn14 : (0:ℝ) ≤ z ^ 14 := by positivity
  have hn15 : (0:ℝ) ≤ z ^ 15 := by positivity
  have hn16 : (0:ℝ) ≤ z ^ 16 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16]⟩

lemma reg4_Q2_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(-240 : ℝ) + (-360 : ℝ) * z ^ 1 + (-250 : ℝ) * z ^ 2 + (-135 : ℝ) * z ^ 3 + (-115/2 : ℝ) * z ^ 4 + (-20 : ℝ) * z ^ 5 + (-395/72 : ℝ) * z ^ 6 + (-13/12 : ℝ) * z ^ 7 + (-19/120 : ℝ) * z ^ 8 + (11/1440 : ℝ) * z ^ 9 + (1/120 : ℝ) * z ^ 10 + (1/480 : ℝ) * z ^ 11 + (1/3600 : ℝ) * z ^ 12| ≤ (1070 : ℝ) := by
  have hp1 : z ^ 1 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp4 : z ^ 4 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp5 : z ^ 5 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp6 : z ^ 6 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp7 : z ^ 7 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp8 : z ^ 8 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp9 : z ^ 9 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp10 : z ^ 10 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp11 : z ^ 11 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp12 : z ^ 12 ≤ 1 := pow_le_one₀ hz0 hz1
  have hn1 : (0:ℝ) ≤ z ^ 1 := by positivity
  have hn2 : (0:ℝ) ≤ z ^ 2 := by positivity
  have hn3 : (0:ℝ) ≤ z ^ 3 := by positivity
  have hn4 : (0:ℝ) ≤ z ^ 4 := by positivity
  have hn5 : (0:ℝ) ≤ z ^ 5 := by positivity
  have hn6 : (0:ℝ) ≤ z ^ 6 := by positivity
  have hn7 : (0:ℝ) ≤ z ^ 7 := by positivity
  have hn8 : (0:ℝ) ≤ z ^ 8 := by positivity
  have hn9 : (0:ℝ) ≤ z ^ 9 := by positivity
  have hn10 : (0:ℝ) ≤ z ^ 10 := by positivity
  have hn11 : (0:ℝ) ≤ z ^ 11 := by positivity
  have hn12 : (0:ℝ) ≤ z ^ 12 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12]⟩

lemma reg4_Q3_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(-240 : ℝ) + (-240 : ℝ) * z ^ 1 + (-140 : ℝ) * z ^ 2 + (-45 : ℝ) * z ^ 3 + (-50/3 : ℝ) * z ^ 4 + (-10/3 : ℝ) * z ^ 5 + (-5/12 : ℝ) * z ^ 6 + (1/60 : ℝ) * z ^ 8| ≤ (686 : ℝ) := by
  have hp1 : z ^ 1 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp4 : z ^ 4 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp5 : z ^ 5 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp6 : z ^ 6 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp7 : z ^ 7 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp8 : z ^ 8 ≤ 1 := pow_le_one₀ hz0 hz1
  have hn1 : (0:ℝ) ≤ z ^ 1 := by positivity
  have hn2 : (0:ℝ) ≤ z ^ 2 := by positivity
  have hn3 : (0:ℝ) ≤ z ^ 3 := by positivity
  have hn4 : (0:ℝ) ≤ z ^ 4 := by positivity
  have hn5 : (0:ℝ) ≤ z ^ 5 := by positivity
  have hn6 : (0:ℝ) ≤ z ^ 6 := by positivity
  have hn7 : (0:ℝ) ≤ z ^ 7 := by positivity
  have hn8 : (0:ℝ) ≤ z ^ 8 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8]⟩

lemma reg4_Q4_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(-120 : ℝ) + (-60 : ℝ) * z ^ 1 + (-20 : ℝ) * z ^ 2 + (-5 : ℝ) * z ^ 3| ≤ (205 : ℝ) := by
  have hp1 : z ^ 1 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
  have hn1 : (0:ℝ) ≤ z ^ 1 := by positivity
  have hn2 : (0:ℝ) ≤ z ^ 2 := by positivity
  have hn3 : (0:ℝ) ≤ z ^ 3 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hn1, hn2, hn3], by linarith [hp1, hp2, hp3, hn1, hn2, hn3]⟩

lemma reg4_Q5_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(-24 : ℝ)| ≤ (24 : ℝ) := by


  rw [abs_le]
  refine ⟨by linarith [], by linarith []⟩

/-- The degree-10 cancellation identity (`δ = y − P5`).  Pure `ring`. -/
lemma reg4_split_identity (z y : ℝ) :
    z ^ 5 * (24 + 60 * y + 50 * y ^ 2 + 15 * y ^ 3 + y ^ 4) - 24 * y ^ 5
      = z ^ 10 * ((1/6 : ℝ) + (5/18 : ℝ) * z ^ 1 + (13/48 : ℝ) * z ^ 2 + (421/2160 : ℝ) * z ^ 3 + (109/960 : ℝ) * z ^ 4 + (577/10368 : ℝ) * z ^ 5 + (121/5184 : ℝ) * z ^ 6 + (4409/518400 : ℝ) * z ^ 7 + (5591/2073600 : ℝ) * z ^ 8 + (1541/2073600 : ℝ) * z ^ 9 + (1463/8294400 : ℝ) * z ^ 10 + (23/648000 : ℝ) * z ^ 11 + (41/6912000 : ℝ) * z ^ 12 + (1/1296000 : ℝ) * z ^ 13 + (1/13824000 : ℝ) * z ^ 14 + (1/259200000 : ℝ) * z ^ 15)
        + (y - (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120)) * z ^ 4 * ((-120 : ℝ) + (-180 : ℝ) * z ^ 1 + (-160 : ℝ) * z ^ 2 + (-105 : ℝ) * z ^ 3 + (-335/6 : ℝ) * z ^ 4 + (-295/12 : ℝ) * z ^ 5 + (-80/9 : ℝ) * z ^ 6 + (-191/72 : ℝ) * z ^ 7 + (-1307/2160 : ℝ) * z ^ 8 + (-713/8640 : ℝ) * z ^ 9 + (1/120 : ℝ) * z ^ 10 + (17/1728 : ℝ) * z ^ 11 + (1267/345600 : ℝ) * z ^ 12 + (7/7200 : ℝ) * z ^ 13 + (31/172800 : ℝ) * z ^ 14 + (1/43200 : ℝ) * z ^ 15 + (1/576000 : ℝ) * z ^ 16)
        + (y - (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120)) ^ 2 * z ^ 3 * ((-240 : ℝ) + (-360 : ℝ) * z ^ 1 + (-250 : ℝ) * z ^ 2 + (-135 : ℝ) * z ^ 3 + (-115/2 : ℝ) * z ^ 4 + (-20 : ℝ) * z ^ 5 + (-395/72 : ℝ) * z ^ 6 + (-13/12 : ℝ) * z ^ 7 + (-19/120 : ℝ) * z ^ 8 + (11/1440 : ℝ) * z ^ 9 + (1/120 : ℝ) * z ^ 10 + (1/480 : ℝ) * z ^ 11 + (1/3600 : ℝ) * z ^ 12)
        + (y - (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120)) ^ 3 * z ^ 2 * ((-240 : ℝ) + (-240 : ℝ) * z ^ 1 + (-140 : ℝ) * z ^ 2 + (-45 : ℝ) * z ^ 3 + (-50/3 : ℝ) * z ^ 4 + (-10/3 : ℝ) * z ^ 5 + (-5/12 : ℝ) * z ^ 6 + (1/60 : ℝ) * z ^ 8)
        + (y - (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120)) ^ 4 * z * ((-120 : ℝ) + (-60 : ℝ) * z ^ 1 + (-20 : ℝ) * z ^ 2 + (-5 : ℝ) * z ^ 3)
        + (y - (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120)) ^ 5 * ((-24 : ℝ)) := by
  ring

/-- Closed form of `boseKernel4` in `y = e^z − 1`. -/
lemma boseKernel4_yform {z : ℝ} (hz : 0 < z) :
    boseKernel4 z
      = (24 + 60 * (Real.exp z - 1) + 50 * (Real.exp z - 1) ^ 2
          + 15 * (Real.exp z - 1) ^ 3 + (Real.exp z - 1) ^ 4) / (Real.exp z - 1) ^ 5 := by
  have he0 : Real.exp z ≠ 0 := (Real.exp_pos z).ne'
  have he1 : (1 : ℝ) < Real.exp z := by nlinarith [Real.add_one_le_exp z, hz]
  have hy0 : Real.exp z - 1 ≠ 0 := by linarith
  have hinv1 : (Real.exp z)⁻¹ < 1 := by
    rw [inv_eq_one_div, div_lt_one (Real.exp_pos z)]; exact he1
  have hq1 : (1 : ℝ) - (Real.exp z)⁻¹ ≠ 0 := by linarith
  rw [boseKernel4, Real.exp_neg]
  field_simp
  ring

/-- Numerator bound: `|reg4Num(z, e^z−1)| ≤ 2645 z¹⁰` on `(0,1]`. -/
lemma reg4_num_le {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    |z ^ 5 * (24 + 60 * (Real.exp z - 1) + 50 * (Real.exp z - 1) ^ 2
        + 15 * (Real.exp z - 1) ^ 3 + (Real.exp z - 1) ^ 4) - 24 * (Real.exp z - 1) ^ 5|
      ≤ 2645 * z ^ 10 := by
  set y : ℝ := Real.exp z - 1 with hydef
  have hz10nn : (0:ℝ) ≤ z ^ 10 := by positivity
  set δ : ℝ := y - (z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 + z ^ 5 / 120) with hδdef
  have hδbd : |δ| ≤ z ^ 6 := by
    rw [hδdef, hydef]
    have h := exp_sub_one_order5_bound hz0.le hz1
    convert h using 2
    ring
  have hδ2 : δ ^ 2 ≤ z ^ 12 := by
    have h1 : |δ| ^ 2 ≤ (z ^ 6) ^ 2 := pow_le_pow_left₀ (abs_nonneg δ) hδbd 2
    have h3 : δ ^ 2 = |δ| ^ 2 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h3]; calc |δ| ^ 2 ≤ (z ^ 6) ^ 2 := h1
      _ = z ^ 12 := by ring
  have hδ3 : |δ| ^ 3 ≤ z ^ 18 := by
    calc |δ| ^ 3 ≤ (z ^ 6) ^ 3 := pow_le_pow_left₀ (abs_nonneg δ) hδbd 3
      _ = z ^ 18 := by ring
  have hδ4 : δ ^ 4 ≤ z ^ 24 := by
    have h1 : |δ| ^ 4 ≤ (z ^ 6) ^ 4 := pow_le_pow_left₀ (abs_nonneg δ) hδbd 4
    have h3 : δ ^ 4 = |δ| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h3]; calc |δ| ^ 4 ≤ (z ^ 6) ^ 4 := h1
      _ = z ^ 24 := by ring
  have hδ5 : |δ| ^ 5 ≤ z ^ 30 := by
    calc |δ| ^ 5 ≤ (z ^ 6) ^ 5 := pow_le_pow_left₀ (abs_nonneg δ) hδbd 5
      _ = z ^ 30 := by ring
  have r15 : z ^ 15 ≤ z ^ 10 := pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
  have r20 : z ^ 20 ≤ z ^ 10 := pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
  have r25 : z ^ 25 ≤ z ^ 10 := pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
  have r30 : z ^ 30 ≤ z ^ 10 := pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
  rw [reg4_split_identity z y, ← hδdef]
  set Q0 := (1/6 : ℝ) + (5/18 : ℝ) * z ^ 1 + (13/48 : ℝ) * z ^ 2 + (421/2160 : ℝ) * z ^ 3 + (109/960 : ℝ) * z ^ 4 + (577/10368 : ℝ) * z ^ 5 + (121/5184 : ℝ) * z ^ 6 + (4409/518400 : ℝ) * z ^ 7 + (5591/2073600 : ℝ) * z ^ 8 + (1541/2073600 : ℝ) * z ^ 9 + (1463/8294400 : ℝ) * z ^ 10 + (23/648000 : ℝ) * z ^ 11 + (41/6912000 : ℝ) * z ^ 12 + (1/1296000 : ℝ) * z ^ 13 + (1/13824000 : ℝ) * z ^ 14 + (1/259200000 : ℝ) * z ^ 15 with hQ0def
  set Q1 := (-120 : ℝ) + (-180 : ℝ) * z ^ 1 + (-160 : ℝ) * z ^ 2 + (-105 : ℝ) * z ^ 3 + (-335/6 : ℝ) * z ^ 4 + (-295/12 : ℝ) * z ^ 5 + (-80/9 : ℝ) * z ^ 6 + (-191/72 : ℝ) * z ^ 7 + (-1307/2160 : ℝ) * z ^ 8 + (-713/8640 : ℝ) * z ^ 9 + (1/120 : ℝ) * z ^ 10 + (17/1728 : ℝ) * z ^ 11 + (1267/345600 : ℝ) * z ^ 12 + (7/7200 : ℝ) * z ^ 13 + (31/172800 : ℝ) * z ^ 14 + (1/43200 : ℝ) * z ^ 15 + (1/576000 : ℝ) * z ^ 16 with hQ1def
  set Q2 := (-240 : ℝ) + (-360 : ℝ) * z ^ 1 + (-250 : ℝ) * z ^ 2 + (-135 : ℝ) * z ^ 3 + (-115/2 : ℝ) * z ^ 4 + (-20 : ℝ) * z ^ 5 + (-395/72 : ℝ) * z ^ 6 + (-13/12 : ℝ) * z ^ 7 + (-19/120 : ℝ) * z ^ 8 + (11/1440 : ℝ) * z ^ 9 + (1/120 : ℝ) * z ^ 10 + (1/480 : ℝ) * z ^ 11 + (1/3600 : ℝ) * z ^ 12 with hQ2def
  set Q3 := (-240 : ℝ) + (-240 : ℝ) * z ^ 1 + (-140 : ℝ) * z ^ 2 + (-45 : ℝ) * z ^ 3 + (-50/3 : ℝ) * z ^ 4 + (-10/3 : ℝ) * z ^ 5 + (-5/12 : ℝ) * z ^ 6 + (1/60 : ℝ) * z ^ 8 with hQ3def
  set Q4 := (-120 : ℝ) + (-60 : ℝ) * z ^ 1 + (-20 : ℝ) * z ^ 2 + (-5 : ℝ) * z ^ 3 with hQ4def
  set Q5 := (-24 : ℝ) with hQ5def
  have hQ0 := reg4_Q0_bound hz0.le hz1
  have hQ1 := reg4_Q1_bound hz0.le hz1
  have hQ2 := reg4_Q2_bound hz0.le hz1
  have hQ3 := reg4_Q3_bound hz0.le hz1
  have hQ4 := reg4_Q4_bound hz0.le hz1
  have hQ5 := reg4_Q5_bound hz0.le hz1
  have e0 : |z ^ 10 * Q0| ≤ z ^ 10 * 2 := by
    rw [abs_mul, abs_of_nonneg hz10nn]; exact mul_le_mul_of_nonneg_left hQ0 hz10nn
  have e1 : |δ * z ^ 4 * Q1| ≤ z ^ 10 * 658 := by
    rw [show δ * z ^ 4 * Q1 = δ * (z ^ 4 * Q1) by ring, abs_mul]
    have hb : |z ^ 4 * Q1| ≤ z ^ 4 * 658 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ z ^ 4)]
      exact mul_le_mul_of_nonneg_left hQ1 (by positivity)
    calc |δ| * |z ^ 4 * Q1| ≤ z ^ 6 * (z ^ 4 * 658) := mul_le_mul hδbd hb (abs_nonneg _) (by positivity)
      _ = z ^ 10 * 658 := by ring
  have e2 : |δ ^ 2 * z ^ 3 * Q2| ≤ z ^ 10 * 1070 := by
    rw [show δ ^ 2 * z ^ 3 * Q2 = δ ^ 2 * (z ^ 3 * Q2) by ring, abs_mul, abs_of_nonneg (sq_nonneg δ)]
    have hb : |z ^ 3 * Q2| ≤ z ^ 3 * 1070 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ z ^ 3)]
      exact mul_le_mul_of_nonneg_left hQ2 (by positivity)
    calc δ ^ 2 * |z ^ 3 * Q2| ≤ z ^ 12 * (z ^ 3 * 1070) := mul_le_mul hδ2 hb (abs_nonneg _) (by positivity)
      _ = z ^ 15 * 1070 := by ring
      _ ≤ z ^ 10 * 1070 := mul_le_mul_of_nonneg_right r15 (by norm_num)
  have e3 : |δ ^ 3 * z ^ 2 * Q3| ≤ z ^ 10 * 686 := by
    rw [show δ ^ 3 * z ^ 2 * Q3 = δ ^ 3 * (z ^ 2 * Q3) by ring, abs_mul,
      show |δ ^ 3| = |δ| ^ 3 from by rw [abs_pow]]
    have hb : |z ^ 2 * Q3| ≤ z ^ 2 * 686 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ z ^ 2)]
      exact mul_le_mul_of_nonneg_left hQ3 (by positivity)
    calc |δ| ^ 3 * |z ^ 2 * Q3| ≤ z ^ 18 * (z ^ 2 * 686) := mul_le_mul hδ3 hb (abs_nonneg _) (by positivity)
      _ = z ^ 20 * 686 := by ring
      _ ≤ z ^ 10 * 686 := mul_le_mul_of_nonneg_right r20 (by norm_num)
  have e4 : |δ ^ 4 * z * Q4| ≤ z ^ 10 * 205 := by
    rw [show δ ^ 4 * z * Q4 = δ ^ 4 * (z * Q4) by ring, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ δ ^ 4)]
    have hb : |z * Q4| ≤ z * 205 := by
      rw [abs_mul, abs_of_nonneg hz0.le]
      exact mul_le_mul_of_nonneg_left hQ4 hz0.le
    calc δ ^ 4 * |z * Q4| ≤ z ^ 24 * (z * 205) := mul_le_mul hδ4 hb (abs_nonneg _) (by positivity)
      _ = z ^ 25 * 205 := by ring
      _ ≤ z ^ 10 * 205 := mul_le_mul_of_nonneg_right r25 (by norm_num)
  have e5 : |δ ^ 5 * Q5| ≤ z ^ 10 * 24 := by
    rw [abs_mul, show |δ ^ 5| = |δ| ^ 5 from by rw [abs_pow]]
    have hb : |Q5| ≤ 24 := by rw [hQ5def, abs_of_nonpos (by norm_num)]; norm_num
    calc |δ| ^ 5 * |Q5| ≤ z ^ 30 * 24 := mul_le_mul hδ5 hb (abs_nonneg _) (by positivity)
      _ ≤ z ^ 10 * 24 := mul_le_mul_of_nonneg_right r30 (by norm_num)
  have hassoc : z ^ 10 * Q0 + δ * z ^ 4 * Q1 + δ ^ 2 * z ^ 3 * Q2 + δ ^ 3 * z ^ 2 * Q3
        + δ ^ 4 * z * Q4 + δ ^ 5 * Q5
      = z ^ 10 * Q0 + (δ * z ^ 4 * Q1 + (δ ^ 2 * z ^ 3 * Q2 + (δ ^ 3 * z ^ 2 * Q3
        + (δ ^ 4 * z * Q4 + δ ^ 5 * Q5)))) := by ring
  rw [hassoc]
  have t1 := abs_add_le (z ^ 10 * Q0) (δ * z ^ 4 * Q1 + (δ ^ 2 * z ^ 3 * Q2 + (δ ^ 3 * z ^ 2 * Q3 + (δ ^ 4 * z * Q4 + δ ^ 5 * Q5))))
  have t2 := abs_add_le (δ * z ^ 4 * Q1) (δ ^ 2 * z ^ 3 * Q2 + (δ ^ 3 * z ^ 2 * Q3 + (δ ^ 4 * z * Q4 + δ ^ 5 * Q5)))
  have t3 := abs_add_le (δ ^ 2 * z ^ 3 * Q2) (δ ^ 3 * z ^ 2 * Q3 + (δ ^ 4 * z * Q4 + δ ^ 5 * Q5))
  have t4 := abs_add_le (δ ^ 3 * z ^ 2 * Q3) (δ ^ 4 * z * Q4 + δ ^ 5 * Q5)
  have t5 := abs_add_le (δ ^ 4 * z * Q4) (δ ^ 5 * Q5)
  linarith [t1, t2, t3, t4, t5, e0, e1, e2, e3, e4, e5]

/-- **Near-zero bound** `|boseKernel4 z − 24/z⁵| ≤ 2645` on `(0,1]`. -/
lemma reg4_bdd_near_zero {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    |boseKernel4 z - 24 / z ^ 5| ≤ 2645 := by
  have hyz : z ≤ Real.exp z - 1 := by linarith [Real.add_one_le_exp z]
  have hypos : 0 < Real.exp z - 1 := by linarith
  have hy0 : Real.exp z - 1 ≠ 0 := hypos.ne'
  have hz0' : z ≠ 0 := hz0.ne'
  have heq : boseKernel4 z - 24 / z ^ 5
      = (z ^ 5 * (24 + 60 * (Real.exp z - 1) + 50 * (Real.exp z - 1) ^ 2
          + 15 * (Real.exp z - 1) ^ 3 + (Real.exp z - 1) ^ 4) - 24 * (Real.exp z - 1) ^ 5)
        / (z ^ 5 * (Real.exp z - 1) ^ 5) := by
    rw [boseKernel4_yform hz0]
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos (by positivity) (pow_pos hypos 5))]
  rw [div_le_iff₀ (mul_pos (by positivity) (pow_pos hypos 5))]
  have hnum := reg4_num_le hz0 hz1
  have hden : z ^ 10 ≤ z ^ 5 * (Real.exp z - 1) ^ 5 := by
    have h5 : z ^ 5 ≤ (Real.exp z - 1) ^ 5 := pow_le_pow_left₀ hz0.le hyz 5
    nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ z ^ 5)]
  have hscaled := mul_le_mul_of_nonneg_left hden (by norm_num : (0:ℝ) ≤ 2645)
  linarith [hnum, hscaled]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
