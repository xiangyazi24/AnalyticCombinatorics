import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernel

/-!
# The Erdős kernel density integral

`∫₀^∞ y·e^{−ry} dy = 1/r²` (from Mathlib's scaled Gamma integral), and the normalization
`(π²/6)·∫₀^∞ y·e^{−(C/2)y} dy = 1` (using `C² = 4A`, `A = π²/6`) — the closed form the kernel
total-mass theorem consumes.

Opus-authored during the codex quota outage.
-/

noncomputable section

open Set Real

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `∫₀^∞ t·e^{−rt} dt = 1/r²` for `r > 0`. -/
lemma integral_id_mul_exp_neg_mul_Ioi {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ in Ioi (0 : ℝ), t * Real.exp (-(r * t)) = 1 / r ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr
  have hsimp :
      (fun t : ℝ => t ^ ((2 : ℝ) - 1) * Real.exp (-(r * t)))
        = fun t : ℝ => t ^ (1 : ℝ) * Real.exp (-(r * t)) := by
    norm_num
  rw [hsimp] at h
  have hint :
      ∫ t : ℝ in Ioi (0 : ℝ), t ^ (1 : ℝ) * Real.exp (-(r * t))
        = ∫ t : ℝ in Ioi (0 : ℝ), t * Real.exp (-(r * t)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [Real.rpow_one]
  rw [hint] at h
  rw [h]
  have hG : Real.Gamma 2 = 1 := by
    have h1 : Real.Gamma ((1 : ℕ) + 1) = (Nat.factorial 1 : ℝ) :=
      Real.Gamma_nat_eq_factorial 1
    set_option linter.unnecessarySimpa false in
    simpa using h1
  rw [hG, mul_one]
  rw [div_rpow (by norm_num) hr.le, Real.one_rpow]
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The kernel density integrates to 1: `(π²/6)·∫₀^∞ y·e^{−(C/2)y} dy = 1`. -/
theorem kernel_density_integral_one :
    (Real.pi ^ 2 / 6) * ∫ y : ℝ in Ioi (0 : ℝ), y * Real.exp (-(C / 2 * y)) = 1 := by
  have hC : 0 < C := C_pos
  have hr : 0 < C / 2 := by positivity
  rw [integral_id_mul_exp_neg_mul_Ioi hr]
  have hCsq : C ^ 2 = 4 * Partitions.A := C_sq_eq_four_mul_A
  have hA : Partitions.A = Real.pi ^ 2 / 6 := rfl
  have h2 : (C / 2) ^ 2 = Partitions.A := by
    rw [div_pow, hCsq]; ring
  rw [h2, hA]
  have hπ : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
  field_simp

end AnalyticCombinatorics.Ch8.Partitions.Erdos
