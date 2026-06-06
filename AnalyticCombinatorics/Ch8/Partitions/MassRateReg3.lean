import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentTwo
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentBound

/-!
# Mass-rate campaign: the `reg3` near-zero bound (M₂ keystone input) — split certificate

`|boseKernel3 z − 6/z⁴| ≤ 3600` on `(0,1]`, degree-8 cancellation certificate, with the
heavy polynomial-coefficient bounds and the degree-28 `ring` identity factored into separate
lemmas (each under the per-declaration heartbeat budget).  Opus-authored (sympy-generated).
-/

noncomputable section

open Finset
open scoped BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

set_option maxHeartbeats 4000000
/-- coefficient-sum bound for the certificate. -/
lemma reg3_polyQ_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : |(1/120 : ℝ) + (-1/60 : ℝ) * z ^ 1 + (9/560 : ℝ) * z ^ 2 + (-53/5040 : ℝ) * z ^ 3 + (47/9450 : ℝ) * z ^ 4 + (-271/151200 : ℝ) * z ^ 5 + (7/14400 : ℝ) * z ^ 6 + (-79/907200 : ℝ) * z ^ 7 + (653/1016064000 : ℝ) * z ^ 8 + (929/127008000 : ℝ) * z ^ 9 + (-271/72576000 : ℝ) * z ^ 10 + (1949/1524096000 : ℝ) * z ^ 11 + (-10607/30481920000 : ℝ) * z ^ 12 + (3667/45722880000 : ℝ) * z ^ 13 + (-281/17781120000 : ℝ) * z ^ 14 + (341/128024064000 : ℝ) * z ^ 15 + (-5863/15362887680000 : ℝ) * z ^ 16 + (1/21946982400 : ℝ) * z ^ 17 + (-11/2560481280000 : ℝ) * z ^ 18 + (1/3840721920000 : ℝ) * z ^ 19 + (-1/107540213760000 : ℝ) * z ^ 20| ≤ (1 : ℝ) := by
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
  have hp17 : z ^ 17 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp18 : z ^ 18 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp19 : z ^ 19 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp20 : z ^ 20 ≤ 1 := pow_le_one₀ hz0 hz1
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
  have hn17 : (0:ℝ) ≤ z ^ 17 := by positivity
  have hn18 : (0:ℝ) ≤ z ^ 18 := by positivity
  have hn19 : (0:ℝ) ≤ z ^ 19 := by positivity
  have hn20 : (0:ℝ) ≤ z ^ 20 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hn19, hn20], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hn19, hn20]⟩
/-- coefficient-sum bound for the certificate. -/
lemma reg3_polyA1_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : |(-24 : ℝ) * z ^ 3 + (24 : ℝ) * z ^ 4 + (-16 : ℝ) * z ^ 5 + (8 : ℝ) * z ^ 6 + (-49/15 : ℝ) * z ^ 7 + (67/60 : ℝ) * z ^ 8 + (-841/2520 : ℝ) * z ^ 9 + (457/5040 : ℝ) * z ^ 10 + (-83/3600 : ℝ) * z ^ 11 + (59/10080 : ℝ) * z ^ 12 + (-47/33600 : ℝ) * z ^ 13 + (67/201600 : ℝ) * z ^ 14 + (-1579/21168000 : ℝ) * z ^ 15 + (317/21168000 : ℝ) * z ^ 16 + (-37/14112000 : ℝ) * z ^ 17 + (43/108864000 : ℝ) * z ^ 18 + (-13/254016000 : ℝ) * z ^ 19 + (1/254016000 : ℝ) * z ^ 20 + (-1/5334336000 : ℝ) * z ^ 21| ≤ (80 : ℝ) := by
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
  have hp17 : z ^ 17 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp18 : z ^ 18 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp19 : z ^ 19 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp20 : z ^ 20 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp21 : z ^ 21 ≤ 1 := pow_le_one₀ hz0 hz1
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
  have hn17 : (0:ℝ) ≤ z ^ 17 := by positivity
  have hn18 : (0:ℝ) ≤ z ^ 18 := by positivity
  have hn19 : (0:ℝ) ≤ z ^ 19 := by positivity
  have hn20 : (0:ℝ) ≤ z ^ 20 := by positivity
  have hn21 : (0:ℝ) ≤ z ^ 21 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hn19, hn20, hn21], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hn19, hn20, hn21]⟩
/-- coefficient-sum bound for the certificate. -/
lemma reg3_polyA2_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : |(-36 : ℝ) * z ^ 2 + (36 : ℝ) * z ^ 3 + (-14 : ℝ) * z ^ 4 + (6 : ℝ) * z ^ 5 + (-8/5 : ℝ) * z ^ 6 + (2/5 : ℝ) * z ^ 7 + (-57/560 : ℝ) * z ^ 8 + (1/42 : ℝ) * z ^ 9 + (-41/8400 : ℝ) * z ^ 10 + (1/1200 : ℝ) * z ^ 11 + (-19/100800 : ℝ) * z ^ 12 + (1/50400 : ℝ) * z ^ 13 + (-1/705600 : ℝ) * z ^ 14| ≤ (95 : ℝ) := by
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
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14]⟩
/-- coefficient-sum bound for the certificate. -/
lemma reg3_polyA3_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : |(-24 : ℝ) * z ^ 1 + (12 : ℝ) * z ^ 2 + (-4 : ℝ) * z ^ 3 + (-1/5 : ℝ) * z ^ 5 + (1/30 : ℝ) * z ^ 6 + (-1/210 : ℝ) * z ^ 7| ≤ (41 : ℝ) := by
  have hp1 : z ^ 1 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp2 : z ^ 2 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp3 : z ^ 3 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp4 : z ^ 4 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp5 : z ^ 5 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp6 : z ^ 6 ≤ 1 := pow_le_one₀ hz0 hz1
  have hp7 : z ^ 7 ≤ 1 := pow_le_one₀ hz0 hz1
  have hn1 : (0:ℝ) ≤ z ^ 1 := by positivity
  have hn2 : (0:ℝ) ≤ z ^ 2 := by positivity
  have hn3 : (0:ℝ) ≤ z ^ 3 := by positivity
  have hn4 : (0:ℝ) ≤ z ^ 4 := by positivity
  have hn5 : (0:ℝ) ≤ z ^ 5 := by positivity
  have hn6 : (0:ℝ) ≤ z ^ 6 := by positivity
  have hn7 : (0:ℝ) ≤ z ^ 7 := by positivity
  rw [abs_le]
  refine ⟨by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hn1, hn2, hn3, hn4, hn5, hn6, hn7], by linarith [hp1, hp2, hp3, hp4, hp5, hp6, hp7, hn1, hn2, hn3, hn4, hn5, hn6, hn7]⟩

/-- Order-8 Taylor remainder for `w = 1−e^{−z}`: `|w − P₇(z)| ≤ z⁸` on `[0,1]`. -/
lemma w_sub_taylor7_bound {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |(1 - Real.exp (-z)) - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7)| ≤ z ^ 8 := by
  have habs : |(-z)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hz0]; exact hz1
  have h := Real.exp_bound habs (n := 8) (by norm_num)
  have hsum : ∑ i ∈ Finset.range 8, (-z) ^ i / (Nat.factorial i : ℝ)
      = 1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24 - z ^ 5 / 120 + z ^ 6 / 720 - z ^ 7 / 5040 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hsum] at h
  have habs8 : |(-z)| ^ 8 = z ^ 8 := by rw [abs_neg, abs_of_nonneg hz0]
  rw [habs8] at h
  have hc : (z : ℝ) ^ 8 * ((8 : ℕ).succ / ((Nat.factorial 8 : ℝ) * 8)) ≤ z ^ 8 := by
    have hz8 : (0:ℝ) ≤ z ^ 8 := by positivity
    have hcle : ((8 : ℕ).succ : ℝ) / ((Nat.factorial 8 : ℝ) * 8) ≤ 1 := by norm_num [Nat.factorial]
    nlinarith [hz8, hcle]
  have hrw : (1 - Real.exp (-z)) - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7)
      = -(Real.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24 - z ^ 5 / 120
          + z ^ 6 / 720 - z ^ 7 / 5040)) := by ring
  rw [hrw, abs_neg]
  exact le_trans h hc

set_option maxHeartbeats 0 in
/-- The degree-8 numerator identity (pure `ring` in `(z,w)`). -/
lemma reg3_N3_identity (z w : ℝ) :
    z ^ 4 * (6 - 12 * w + 7 * w ^ 2 - w ^ 3) - 6 * w ^ 4
      = z ^ 8 * ((1/120 : ℝ) + (-1/60 : ℝ) * z ^ 1 + (9/560 : ℝ) * z ^ 2 + (-53/5040 : ℝ) * z ^ 3 + (47/9450 : ℝ) * z ^ 4 + (-271/151200 : ℝ) * z ^ 5 + (7/14400 : ℝ) * z ^ 6 + (-79/907200 : ℝ) * z ^ 7 + (653/1016064000 : ℝ) * z ^ 8 + (929/127008000 : ℝ) * z ^ 9 + (-271/72576000 : ℝ) * z ^ 10 + (1949/1524096000 : ℝ) * z ^ 11 + (-10607/30481920000 : ℝ) * z ^ 12 + (3667/45722880000 : ℝ) * z ^ 13 + (-281/17781120000 : ℝ) * z ^ 14 + (341/128024064000 : ℝ) * z ^ 15 + (-5863/15362887680000 : ℝ) * z ^ 16 + (1/21946982400 : ℝ) * z ^ 17 + (-11/2560481280000 : ℝ) * z ^ 18 + (1/3840721920000 : ℝ) * z ^ 19 + (-1/107540213760000 : ℝ) * z ^ 20) + (w - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7)) * ((-24 : ℝ) * z ^ 3 + (24 : ℝ) * z ^ 4 + (-16 : ℝ) * z ^ 5 + (8 : ℝ) * z ^ 6 + (-49/15 : ℝ) * z ^ 7 + (67/60 : ℝ) * z ^ 8 + (-841/2520 : ℝ) * z ^ 9 + (457/5040 : ℝ) * z ^ 10 + (-83/3600 : ℝ) * z ^ 11 + (59/10080 : ℝ) * z ^ 12 + (-47/33600 : ℝ) * z ^ 13 + (67/201600 : ℝ) * z ^ 14 + (-1579/21168000 : ℝ) * z ^ 15 + (317/21168000 : ℝ) * z ^ 16 + (-37/14112000 : ℝ) * z ^ 17 + (43/108864000 : ℝ) * z ^ 18 + (-13/254016000 : ℝ) * z ^ 19 + (1/254016000 : ℝ) * z ^ 20 + (-1/5334336000 : ℝ) * z ^ 21)
        + (w - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7)) ^ 2 * ((-36 : ℝ) * z ^ 2 + (36 : ℝ) * z ^ 3 + (-14 : ℝ) * z ^ 4 + (6 : ℝ) * z ^ 5 + (-8/5 : ℝ) * z ^ 6 + (2/5 : ℝ) * z ^ 7 + (-57/560 : ℝ) * z ^ 8 + (1/42 : ℝ) * z ^ 9 + (-41/8400 : ℝ) * z ^ 10 + (1/1200 : ℝ) * z ^ 11 + (-19/100800 : ℝ) * z ^ 12 + (1/50400 : ℝ) * z ^ 13 + (-1/705600 : ℝ) * z ^ 14)
        + (w - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7)) ^ 3 * ((-24 : ℝ) * z ^ 1 + (12 : ℝ) * z ^ 2 + (-4 : ℝ) * z ^ 3 + (-1/5 : ℝ) * z ^ 5 + (1/30 : ℝ) * z ^ 6 + (-1/210 : ℝ) * z ^ 7)
        - 6 * (w - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7)) ^ 4 := by
  ring

set_option maxHeartbeats 0 in
/-- **`reg3` near-zero bound** (degree-8 certificate). -/
lemma reg3_bdd_near_zero {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    |boseKernel3 z - 6 / z ^ 4| ≤ 3600 := by
  have hexp1 : Real.exp (-z) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  set w : ℝ := 1 - Real.exp (-z) with hwdef
  have hwhalf : z / 2 ≤ w := by
    rw [hwdef]; have h := one_sub_exp_neg_ge_half hz0 hz1; linarith
  have hwpos : 0 < w := by linarith [hwhalf]
  have hz4 : (0:ℝ) < z ^ 4 := by positivity
  have hreg_eq : boseKernel3 z - 6 / z ^ 4
      = (z ^ 4 * (6 - 12 * w + 7 * w ^ 2 - w ^ 3) - 6 * w ^ 4) / (z ^ 4 * w ^ 4) := by
    rw [boseKernel3, hwdef]
    have hwd : (1 - Real.exp (-z)) ≠ 0 := by rw [← hwdef]; exact hwpos.ne'
    field_simp
    ring
  set δ : ℝ := w - ((1 : ℝ) * z ^ 1 + (-1/2 : ℝ) * z ^ 2 + (1/6 : ℝ) * z ^ 3 + (-1/24 : ℝ) * z ^ 4 + (1/120 : ℝ) * z ^ 5 + (-1/720 : ℝ) * z ^ 6 + (1/5040 : ℝ) * z ^ 7) with hδdef
  have hδbd : |δ| ≤ z ^ 8 := by rw [hδdef, hwdef]; exact w_sub_taylor7_bound hz0.le hz1
  have hN3 : z ^ 4 * (6 - 12 * w + 7 * w ^ 2 - w ^ 3) - 6 * w ^ 4
      = z ^ 8 * ((1/120 : ℝ) + (-1/60 : ℝ) * z ^ 1 + (9/560 : ℝ) * z ^ 2 + (-53/5040 : ℝ) * z ^ 3 + (47/9450 : ℝ) * z ^ 4 + (-271/151200 : ℝ) * z ^ 5 + (7/14400 : ℝ) * z ^ 6 + (-79/907200 : ℝ) * z ^ 7 + (653/1016064000 : ℝ) * z ^ 8 + (929/127008000 : ℝ) * z ^ 9 + (-271/72576000 : ℝ) * z ^ 10 + (1949/1524096000 : ℝ) * z ^ 11 + (-10607/30481920000 : ℝ) * z ^ 12 + (3667/45722880000 : ℝ) * z ^ 13 + (-281/17781120000 : ℝ) * z ^ 14 + (341/128024064000 : ℝ) * z ^ 15 + (-5863/15362887680000 : ℝ) * z ^ 16 + (1/21946982400 : ℝ) * z ^ 17 + (-11/2560481280000 : ℝ) * z ^ 18 + (1/3840721920000 : ℝ) * z ^ 19 + (-1/107540213760000 : ℝ) * z ^ 20) + δ * ((-24 : ℝ) * z ^ 3 + (24 : ℝ) * z ^ 4 + (-16 : ℝ) * z ^ 5 + (8 : ℝ) * z ^ 6 + (-49/15 : ℝ) * z ^ 7 + (67/60 : ℝ) * z ^ 8 + (-841/2520 : ℝ) * z ^ 9 + (457/5040 : ℝ) * z ^ 10 + (-83/3600 : ℝ) * z ^ 11 + (59/10080 : ℝ) * z ^ 12 + (-47/33600 : ℝ) * z ^ 13 + (67/201600 : ℝ) * z ^ 14 + (-1579/21168000 : ℝ) * z ^ 15 + (317/21168000 : ℝ) * z ^ 16 + (-37/14112000 : ℝ) * z ^ 17 + (43/108864000 : ℝ) * z ^ 18 + (-13/254016000 : ℝ) * z ^ 19 + (1/254016000 : ℝ) * z ^ 20 + (-1/5334336000 : ℝ) * z ^ 21) + δ ^ 2 * ((-36 : ℝ) * z ^ 2 + (36 : ℝ) * z ^ 3 + (-14 : ℝ) * z ^ 4 + (6 : ℝ) * z ^ 5 + (-8/5 : ℝ) * z ^ 6 + (2/5 : ℝ) * z ^ 7 + (-57/560 : ℝ) * z ^ 8 + (1/42 : ℝ) * z ^ 9 + (-41/8400 : ℝ) * z ^ 10 + (1/1200 : ℝ) * z ^ 11 + (-19/100800 : ℝ) * z ^ 12 + (1/50400 : ℝ) * z ^ 13 + (-1/705600 : ℝ) * z ^ 14) + δ ^ 3 * ((-24 : ℝ) * z ^ 1 + (12 : ℝ) * z ^ 2 + (-4 : ℝ) * z ^ 3 + (-1/5 : ℝ) * z ^ 5 + (1/30 : ℝ) * z ^ 6 + (-1/210 : ℝ) * z ^ 7) - 6 * δ ^ 4 := by
    rw [hδdef]; exact reg3_N3_identity z w
  have hQb := reg3_polyQ_bound hz0.le hz1
  have hA1b := reg3_polyA1_bound hz0.le hz1
  have hA2b := reg3_polyA2_bound hz0.le hz1
  have hA3b := reg3_polyA3_bound hz0.le hz1
  have hz8nn : (0:ℝ) ≤ z ^ 8 := by positivity
  have hz8le1 : z ^ 8 ≤ 1 := pow_le_one₀ hz0.le hz1
  have hδ2 : δ ^ 2 ≤ z ^ 8 := by
    have h1 : |δ| ^ 2 ≤ (z ^ 8) ^ 2 := pow_le_pow_left₀ (abs_nonneg δ) hδbd 2
    have h2 : (z ^ 8) ^ 2 ≤ z ^ 8 := by
      rw [← pow_mul]; exact pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
    have h3 : δ ^ 2 = |δ| ^ 2 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h3]; linarith
  have hδ3 : |δ| ^ 3 ≤ z ^ 8 := by
    have h1 : |δ| ^ 3 ≤ (z ^ 8) ^ 3 := pow_le_pow_left₀ (abs_nonneg δ) hδbd 3
    have h2 : (z ^ 8) ^ 3 ≤ z ^ 8 := by
      rw [← pow_mul]; exact pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
    linarith
  have hδ4 : δ ^ 4 ≤ z ^ 8 := by
    have h1 : |δ| ^ 4 ≤ (z ^ 8) ^ 4 := pow_le_pow_left₀ (abs_nonneg δ) hδbd 4
    have h2 : (z ^ 8) ^ 4 ≤ z ^ 8 := by
      rw [← pow_mul]; exact pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
    have h3 : δ ^ 4 = |δ| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h3]; linarith
  have e1 : |z ^ 8 * ((1/120 : ℝ) + (-1/60 : ℝ) * z ^ 1 + (9/560 : ℝ) * z ^ 2 + (-53/5040 : ℝ) * z ^ 3 + (47/9450 : ℝ) * z ^ 4 + (-271/151200 : ℝ) * z ^ 5 + (7/14400 : ℝ) * z ^ 6 + (-79/907200 : ℝ) * z ^ 7 + (653/1016064000 : ℝ) * z ^ 8 + (929/127008000 : ℝ) * z ^ 9 + (-271/72576000 : ℝ) * z ^ 10 + (1949/1524096000 : ℝ) * z ^ 11 + (-10607/30481920000 : ℝ) * z ^ 12 + (3667/45722880000 : ℝ) * z ^ 13 + (-281/17781120000 : ℝ) * z ^ 14 + (341/128024064000 : ℝ) * z ^ 15 + (-5863/15362887680000 : ℝ) * z ^ 16 + (1/21946982400 : ℝ) * z ^ 17 + (-11/2560481280000 : ℝ) * z ^ 18 + (1/3840721920000 : ℝ) * z ^ 19 + (-1/107540213760000 : ℝ) * z ^ 20)| ≤ z ^ 8 * 1 := by
    rw [abs_mul, abs_of_nonneg hz8nn]; exact mul_le_mul_of_nonneg_left hQb hz8nn
  have e2 : |δ * ((-24 : ℝ) * z ^ 3 + (24 : ℝ) * z ^ 4 + (-16 : ℝ) * z ^ 5 + (8 : ℝ) * z ^ 6 + (-49/15 : ℝ) * z ^ 7 + (67/60 : ℝ) * z ^ 8 + (-841/2520 : ℝ) * z ^ 9 + (457/5040 : ℝ) * z ^ 10 + (-83/3600 : ℝ) * z ^ 11 + (59/10080 : ℝ) * z ^ 12 + (-47/33600 : ℝ) * z ^ 13 + (67/201600 : ℝ) * z ^ 14 + (-1579/21168000 : ℝ) * z ^ 15 + (317/21168000 : ℝ) * z ^ 16 + (-37/14112000 : ℝ) * z ^ 17 + (43/108864000 : ℝ) * z ^ 18 + (-13/254016000 : ℝ) * z ^ 19 + (1/254016000 : ℝ) * z ^ 20 + (-1/5334336000 : ℝ) * z ^ 21)| ≤ z ^ 8 * 80 := by
    rw [abs_mul]; exact mul_le_mul hδbd hA1b (abs_nonneg _) hz8nn
  have e3 : |δ ^ 2 * ((-36 : ℝ) * z ^ 2 + (36 : ℝ) * z ^ 3 + (-14 : ℝ) * z ^ 4 + (6 : ℝ) * z ^ 5 + (-8/5 : ℝ) * z ^ 6 + (2/5 : ℝ) * z ^ 7 + (-57/560 : ℝ) * z ^ 8 + (1/42 : ℝ) * z ^ 9 + (-41/8400 : ℝ) * z ^ 10 + (1/1200 : ℝ) * z ^ 11 + (-19/100800 : ℝ) * z ^ 12 + (1/50400 : ℝ) * z ^ 13 + (-1/705600 : ℝ) * z ^ 14)| ≤ z ^ 8 * 95 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg δ)]
    exact mul_le_mul hδ2 hA2b (abs_nonneg _) hz8nn
  have e4 : |δ ^ 3 * ((-24 : ℝ) * z ^ 1 + (12 : ℝ) * z ^ 2 + (-4 : ℝ) * z ^ 3 + (-1/5 : ℝ) * z ^ 5 + (1/30 : ℝ) * z ^ 6 + (-1/210 : ℝ) * z ^ 7)| ≤ z ^ 8 * 41 := by
    rw [abs_mul, show |δ ^ 3| = |δ| ^ 3 from by rw [abs_pow]]
    exact mul_le_mul hδ3 hA3b (abs_nonneg _) hz8nn
  have e5 : |(-6 : ℝ) * δ ^ 4| ≤ z ^ 8 * 6 := by
    rw [abs_mul, show |(-6 : ℝ)| = 6 from by norm_num, abs_of_nonneg (by positivity : (0:ℝ) ≤ δ ^ 4)]
    nlinarith [hδ4, hz8nn]
  have hN3bd : |z ^ 4 * (6 - 12 * w + 7 * w ^ 2 - w ^ 3) - 6 * w ^ 4| ≤ 223 * z ^ 8 := by
    rw [hN3]
    set A := z ^ 8 * ((1/120 : ℝ) + (-1/60 : ℝ) * z ^ 1 + (9/560 : ℝ) * z ^ 2 + (-53/5040 : ℝ) * z ^ 3 + (47/9450 : ℝ) * z ^ 4 + (-271/151200 : ℝ) * z ^ 5 + (7/14400 : ℝ) * z ^ 6 + (-79/907200 : ℝ) * z ^ 7 + (653/1016064000 : ℝ) * z ^ 8 + (929/127008000 : ℝ) * z ^ 9 + (-271/72576000 : ℝ) * z ^ 10 + (1949/1524096000 : ℝ) * z ^ 11 + (-10607/30481920000 : ℝ) * z ^ 12 + (3667/45722880000 : ℝ) * z ^ 13 + (-281/17781120000 : ℝ) * z ^ 14 + (341/128024064000 : ℝ) * z ^ 15 + (-5863/15362887680000 : ℝ) * z ^ 16 + (1/21946982400 : ℝ) * z ^ 17 + (-11/2560481280000 : ℝ) * z ^ 18 + (1/3840721920000 : ℝ) * z ^ 19 + (-1/107540213760000 : ℝ) * z ^ 20) with hAdef
    set B := δ * ((-24 : ℝ) * z ^ 3 + (24 : ℝ) * z ^ 4 + (-16 : ℝ) * z ^ 5 + (8 : ℝ) * z ^ 6 + (-49/15 : ℝ) * z ^ 7 + (67/60 : ℝ) * z ^ 8 + (-841/2520 : ℝ) * z ^ 9 + (457/5040 : ℝ) * z ^ 10 + (-83/3600 : ℝ) * z ^ 11 + (59/10080 : ℝ) * z ^ 12 + (-47/33600 : ℝ) * z ^ 13 + (67/201600 : ℝ) * z ^ 14 + (-1579/21168000 : ℝ) * z ^ 15 + (317/21168000 : ℝ) * z ^ 16 + (-37/14112000 : ℝ) * z ^ 17 + (43/108864000 : ℝ) * z ^ 18 + (-13/254016000 : ℝ) * z ^ 19 + (1/254016000 : ℝ) * z ^ 20 + (-1/5334336000 : ℝ) * z ^ 21) with hBdef
    set Cc := δ ^ 2 * ((-36 : ℝ) * z ^ 2 + (36 : ℝ) * z ^ 3 + (-14 : ℝ) * z ^ 4 + (6 : ℝ) * z ^ 5 + (-8/5 : ℝ) * z ^ 6 + (2/5 : ℝ) * z ^ 7 + (-57/560 : ℝ) * z ^ 8 + (1/42 : ℝ) * z ^ 9 + (-41/8400 : ℝ) * z ^ 10 + (1/1200 : ℝ) * z ^ 11 + (-19/100800 : ℝ) * z ^ 12 + (1/50400 : ℝ) * z ^ 13 + (-1/705600 : ℝ) * z ^ 14) with hCcdef
    set Dd := δ ^ 3 * ((-24 : ℝ) * z ^ 1 + (12 : ℝ) * z ^ 2 + (-4 : ℝ) * z ^ 3 + (-1/5 : ℝ) * z ^ 5 + (1/30 : ℝ) * z ^ 6 + (-1/210 : ℝ) * z ^ 7) with hDddef
    have hassoc : A + B + Cc + Dd - 6 * δ ^ 4
        = A + (B + (Cc + (Dd + (-6 : ℝ) * δ ^ 4))) := by ring
    rw [hassoc]
    have t1 := abs_add_le A (B + (Cc + (Dd + (-6 : ℝ) * δ ^ 4)))
    have t2 := abs_add_le B (Cc + (Dd + (-6 : ℝ) * δ ^ 4))
    have t3 := abs_add_le Cc (Dd + (-6 : ℝ) * δ ^ 4)
    have t4 := abs_add_le Dd ((-6 : ℝ) * δ ^ 4)
    linarith [t1, t2, t3, t4, e1, e2, e3, e4, e5]
  have hden : z ^ 8 / 16 ≤ z ^ 4 * w ^ 4 := by
    have hw4ge : (z / 2) ^ 4 ≤ w ^ 4 := pow_le_pow_left₀ (by positivity) hwhalf 4
    have h := mul_le_mul_of_nonneg_left hw4ge hz4.le
    nlinarith [h, hz4]
  rw [hreg_eq, abs_div, abs_of_pos (by positivity : (0:ℝ) < z ^ 4 * w ^ 4)]
  rw [div_le_iff₀ (by positivity)]
  linarith [hN3bd, hden, hz8nn]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
