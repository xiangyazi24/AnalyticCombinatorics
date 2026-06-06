import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.KernelBarriers

/-!
# Mass-rate campaign: Lambert moments — definitions and the central cancellation (R8)

The critical-path brick `|kernelMass n − 1| = O(1/n)` goes through smoothed Lambert
moments `M_r(t) = Σ_m m^r σ(m) e^{−tm}` (NOT a refined pointwise summatory, which cannot
have an `o(x)` secondary at integers because of the `σ(n)` jumps).  This file banks the
definitions, the saddle parameter `λ = C/2` with `λ² = π²/6`, the Bose kernel with its
regularization, and the central algebraic cancellation of the `n^{−1/2}` coefficients:

  `−1/(2λ) + 2Z/λ³ − (C/8)·6Z/λ⁴ = 0`  (`Z = λ²`, `C = 2λ`).

Route: HANDOFF/partition-mass-rate-route-R8.md.  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The `r`-th Lambert moment of the divisor function: `Σ_m m^r σ(m) e^{−tm}`. -/
noncomputable def sigmaMoment (r : ℕ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, if m = 0 then 0
    else (m : ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))

/-- The saddle parameter `λ = C/2`. -/
noncomputable def massLam : ℝ := C / 2

lemma massLam_pos : 0 < massLam := by
  rw [massLam]
  have := C_pos
  positivity

/-- `λ² = π²/6`. -/
lemma massLam_sq : massLam ^ 2 = Real.pi ^ 2 / 6 := by
  rw [massLam, div_pow]
  have h := C_sq_eq_four_mul_A
  have hA : Partitions.A = Real.pi ^ 2 / 6 := rfl
  rw [h, hA]
  ring

/-- The Bose kernel `e^{−x}/(1−e^{−x})²`. -/
noncomputable def boseKernel (x : ℝ) : ℝ :=
  Real.exp (-x) / (1 - Real.exp (-x)) ^ 2

/-- The regularized Bose kernel `boseKernel x − 1/x²` (extends continuously to `−1/12` at 0). -/
noncomputable def boseReg0 (x : ℝ) : ℝ :=
  boseKernel x - 1 / x ^ 2

/-- The Bose kernel is the derivative of `−1/(e^x−1)`: closed antiderivative identity. -/
lemma boseKernel_eq_exp_form {x : ℝ} (hx : 0 < x) :
    boseKernel x = Real.exp x / (Real.exp x - 1) ^ 2 := by
  rw [boseKernel]
  have hexp : Real.exp (-x) = 1 / Real.exp x := by
    rw [Real.exp_neg]
    exact inv_eq_one_div _
  have hepos : 0 < Real.exp x := Real.exp_pos x
  have hne : Real.exp x ≠ 0 := hepos.ne'
  rw [hexp]
  rw [div_eq_div_iff]
  · field_simp
  · have h1 : 1 < Real.exp x := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_lt_exp.mpr hx
    have : 0 < 1 - 1 / Real.exp x := by
      rw [sub_pos, div_lt_one hepos]
      exact h1
    positivity
  · have h1 : 1 < Real.exp x := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_lt_exp.mpr hx
    have : 0 < Real.exp x - 1 := by linarith
    positivity

/--
**The central cancellation** (R8 §6): the three `n^{−1/2}` coefficients — the `−1/(2t)`
secondary of `M₀`, the reciprocal correction through `M₁`, and the exponent correction
through `M₂` — cancel exactly at the saddle `t = λ/√n`.
-/
lemma mass_rate_sqrt_coeff_cancel :
    -(1 / (2 * massLam)) + 2 * (Real.pi ^ 2 / 6) / massLam ^ 3
      - C * (6 * (Real.pi ^ 2 / 6)) / (8 * massLam ^ 4) = 0 := by
  have hlam := massLam_pos
  have hC : C = 2 * massLam := by
    rw [massLam]
    ring
  rw [hC, ← massLam_sq]
  field_simp
  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
