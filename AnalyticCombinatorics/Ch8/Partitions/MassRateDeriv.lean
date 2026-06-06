import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateIntegral

/-!
# Mass-rate campaign: the boseReg0 derivative (R10 bricks 14, 15, 17)

`boseReg0′(x) = −eˣ(eˣ+1)/(eˣ−1)³ + 2/x³` on `(0,∞)`, with the tail bound
`|boseReg0′| ≤ 16e^{−x/2} + 2/x³` for `x ≥ 1`.  (The near-zero derivative bound —
brick 16 — needs the degree-6 cancellation certificate and is a separate brick.)
Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The closed form of `boseReg0′`. -/
noncomputable def boseReg0Deriv (x : ℝ) : ℝ :=
  -(Real.exp x * (Real.exp x + 1)) / (Real.exp x - 1) ^ 3 + 2 / x ^ 3

/-- `boseReg0` has derivative `boseReg0Deriv` on `(0,∞)`. -/
lemma boseReg0_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt boseReg0 (boseReg0Deriv x) x := by
  have hy : 0 < Real.exp x - 1 := by
    have := Real.add_one_lt_exp (x := x) hx.ne'
    linarith
  -- exp-form kernel derivative
  have hker : HasDerivAt (fun y : ℝ => Real.exp y / (Real.exp y - 1) ^ 2)
      (-(Real.exp x * (Real.exp x + 1)) / (Real.exp x - 1) ^ 3) x := by
    have h1 : HasDerivAt (fun y : ℝ => Real.exp y) (Real.exp x) x := Real.hasDerivAt_exp x
    have h2 : HasDerivAt (fun y : ℝ => (Real.exp y - 1) ^ 2)
        (2 * (Real.exp x - 1) ^ 1 * Real.exp x) x := by
      exact ((Real.hasDerivAt_exp x).sub_const 1).pow 2
    have hne : ((Real.exp x - 1) ^ 2) ≠ 0 := by positivity
    have hdiv := h1.div h2 hne
    convert hdiv using 1
    field_simp
    ring
  -- derivative of 1/y²
  have hinv : HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-(2 / x ^ 3)) x := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x ^ 1) x := hasDerivAt_pow 2 x
    have h2 := h1.inv (pow_ne_zero 2 hx.ne')
    have heq : -(2 * x ^ 1) / (x ^ 2) ^ 2 = -(2 / x ^ 3) := by
      field_simp
    have h3 : HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹) (-(2 / x ^ 3)) x := by
      rw [← heq]
      convert h2 using 1
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [one_div]
  have hsub := hker.sub hinv
  -- transfer along boseReg0 = exp-form − 1/x² near x
  have hev : boseReg0 =ᶠ[𝓝 x]
      fun y => Real.exp y / (Real.exp y - 1) ^ 2 - 1 / y ^ 2 := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hx] with y hy
    rw [boseReg0, boseKernel_eq_exp_form hy]
  have hfinal : HasDerivAt boseReg0
      (-(Real.exp x * (Real.exp x + 1)) / (Real.exp x - 1) ^ 3 - -(2 / x ^ 3)) x :=
    hsub.congr_of_eventuallyEq hev
  have : -(Real.exp x * (Real.exp x + 1)) / (Real.exp x - 1) ^ 3 - -(2 / x ^ 3)
      = boseReg0Deriv x := by
    rw [boseReg0Deriv]
    ring
  rwa [this] at hfinal

/-- Tail derivative bound: `|boseReg0′(x)| ≤ 16e^{−x/2} + 2/x³` for `x ≥ 1`. -/
lemma boseReg0Deriv_tail_bound {x : ℝ} (hx : 1 ≤ x) :
    |boseReg0Deriv x| ≤ 16 * Real.exp (-x / 2) + 2 / x ^ 3 := by
  have hxpos : (0 : ℝ) < x := by linarith
  have he2 : (2 : ℝ) ≤ Real.exp x := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    calc (2 : ℝ) ≤ Real.exp 1 := h1
      _ ≤ Real.exp x := Real.exp_le_exp.mpr hx
  have hy : Real.exp x / 2 ≤ Real.exp x - 1 := by linarith
  have hypos : 0 < Real.exp x - 1 := by linarith
  have hepos := Real.exp_pos x
  -- the exponential piece: e^x(e^x+1)/(e^x−1)³ ≤ 16e^{−x}
  have hmain : Real.exp x * (Real.exp x + 1) / (Real.exp x - 1) ^ 3
      ≤ 16 * Real.exp (-x) := by
    have hnum_le : Real.exp x * (Real.exp x + 1) ≤ 2 * Real.exp x ^ 2 := by
      nlinarith [hepos, he2]
    have hden_ge : (Real.exp x / 2) ^ 3 ≤ (Real.exp x - 1) ^ 3 := by
      apply pow_le_pow_left₀ (by positivity) hy
    have hden3 : (Real.exp x / 2) ^ 3 = Real.exp x ^ 3 / 8 := by ring
    have hstep : Real.exp x * (Real.exp x + 1) / (Real.exp x - 1) ^ 3
        ≤ (2 * Real.exp x ^ 2) / (Real.exp x ^ 3 / 8) := by
      apply div_le_div₀ (by positivity) hnum_le (by positivity)
      rw [← hden3]
      exact hden_ge
    have hsimp : (2 * Real.exp x ^ 2) / (Real.exp x ^ 3 / 8) = 16 / Real.exp x := by
      field_simp
      ring
    rw [hsimp] at hstep
    rw [show (16 : ℝ) * Real.exp (-x) = 16 / Real.exp x by
      rw [Real.exp_neg]
      field_simp]
    exact hstep
  have hexp_half : Real.exp (-x) ≤ Real.exp (-x / 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [boseReg0Deriv]
  calc |-(Real.exp x * (Real.exp x + 1)) / (Real.exp x - 1) ^ 3 + 2 / x ^ 3|
      ≤ |(-(Real.exp x * (Real.exp x + 1)) / (Real.exp x - 1) ^ 3)| + |2 / x ^ 3| :=
        abs_add_le _ _
    _ = Real.exp x * (Real.exp x + 1) / (Real.exp x - 1) ^ 3 + 2 / x ^ 3 := by
        rw [abs_of_pos (by positivity : (0:ℝ) < 2 / x ^ 3)]
        congr 1
        rw [abs_of_nonpos (by
          apply div_nonpos_of_nonpos_of_nonneg
          · nlinarith [hepos]
          · positivity)]
        ring
    _ ≤ 16 * Real.exp (-x) + 2 / x ^ 3 := by linarith [hmain]
    _ ≤ 16 * Real.exp (-x / 2) + 2 / x ^ 3 := by nlinarith [hexp_half]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
