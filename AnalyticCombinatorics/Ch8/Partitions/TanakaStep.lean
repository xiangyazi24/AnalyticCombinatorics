import Mathlib

/-!
# R7 Fact B via Doeblin: single-step Tanaka drift of `|D|` (deterministic substrate)

For the rank-difference walk `D` under a stochastic kernel `K` that is *mean-preserving* (a martingale,
`∑_z K x z · D z = D x`) with *bounded increments* (`K x z ≠ 0 → |D z − D x| ≤ b`), the absolute value
`|D|` is a submartingale whose one-step drift is supported on the window `{|D| ≤ b}`:

  `0 ≤ ∑_z K x z |D z| − |D x| ≤ b`,  and `= 0` when `|D x| > b`.

This is the per-step heart of the Tanaka decomposition `E|D_T| = E|D_0| + (compensator)`, where the
compensator equals the window local time.  Telescoped, it gives `window-occupation ≥ (E|D_T| − E|D_0|)/b`,
which with the Paley–Zygmund bound `E|D_T| ≥ c√T` (brick 84) yields the occupation lower bound.  All in
the deterministic finite-sum substrate — no measure theory.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (D : ι → ℝ)

/-- **Jensen / submartingale:** the mean-preserving step does not decrease `|D|`. -/
theorem abs_drift_nonneg (x : ι) (hKnn : ∀ z, 0 ≤ K x z)
    (hmart : ∑ z, K x z * D z = D x) :
    |D x| ≤ ∑ z, K x z * |D z| := by
  calc |D x| = |∑ z, K x z * D z| := by rw [hmart]
    _ ≤ ∑ z, |K x z * D z| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, K x z * |D z| := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [abs_mul, abs_of_nonneg (hKnn z)]

/-- **Bounded drift:** the step increases `|D|` by at most the increment bound `hb`. -/
theorem abs_drift_le (hb : ℝ) (x : ι) (hKnn : ∀ z, 0 ≤ K x z) (hKsum : ∑ z, K x z = 1)
    (hbinc : ∀ z, K x z ≠ 0 → |D z - D x| ≤ hb) :
    (∑ z, K x z * |D z|) ≤ |D x| + hb := by
  have hstep : ∑ z, K x z * |D z| ≤ ∑ z, K x z * (|D x| + hb) := by
    refine Finset.sum_le_sum (fun z _ => ?_)
    by_cases hz : K x z = 0
    · rw [hz]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (hKnn z)
      calc |D z| = |D x + (D z - D x)| := by congr 1; ring
        _ ≤ |D x| + |D z - D x| := abs_add_le _ _
        _ ≤ |D x| + hb := by linarith [hbinc z hz]
  calc ∑ z, K x z * |D z| ≤ ∑ z, K x z * (|D x| + hb) := hstep
    _ = (∑ z, K x z) * (|D x| + hb) := by rw [Finset.sum_mul]
    _ = |D x| + hb := by rw [hKsum]; ring

/-- **Far-from-zero ⟹ no drift:** when `|D x| > b`, the bounded increment keeps every reachable `D z`
on the same side of `0`, so the step preserves `|D|` exactly. -/
theorem abs_drift_eq_of_far (hb : ℝ) (hbnn : 0 ≤ hb) (x : ι) (hKnn : ∀ z, 0 ≤ K x z)
    (hmart : ∑ z, K x z * D z = D x)
    (hbinc : ∀ z, K x z ≠ 0 → |D z - D x| ≤ hb) (hfar : hb < |D x|) :
    (∑ z, K x z * |D z|) = |D x| := by
  rcases lt_trichotomy (D x) 0 with hneg | hzero | hpos
  · -- D x < 0 : every reachable D z < 0
    have habs : |D x| = -D x := abs_of_neg hneg
    have hkey : ∀ z, K x z * |D z| = K x z * (-D z) := by
      intro z
      by_cases hz : K x z = 0
      · rw [hz, zero_mul, zero_mul]
      · have hbz := hbinc z hz
        rw [abs_le] at hbz
        have hdz : D z < 0 := by
          have hxb : D x + hb < 0 := by rw [habs] at hfar; linarith
          linarith [hbz.2]
        rw [abs_of_neg hdz]
    rw [Finset.sum_congr rfl (fun z _ => hkey z)]
    simp only [mul_neg]
    rw [Finset.sum_neg_distrib, hmart, habs]
  · exfalso; rw [hzero] at hfar; simp at hfar; linarith
  · -- D x > 0 : every reachable D z > 0
    have habs : |D x| = D x := abs_of_pos hpos
    have hkey : ∀ z, K x z * |D z| = K x z * D z := by
      intro z
      by_cases hz : K x z = 0
      · rw [hz, zero_mul, zero_mul]
      · have hbz := hbinc z hz
        rw [abs_le] at hbz
        have hdz : 0 < D z := by
          have hxb : 0 < D x - hb := by rw [habs] at hfar; linarith
          linarith [hbz.1]
        rw [abs_of_pos hdz]
    rw [Finset.sum_congr rfl (fun z _ => hkey z), hmart, habs]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
