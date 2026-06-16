import Mathlib

/-!
# The complex logarithm power series `−log(1−z) = ∑ zⁿ⁺¹/(n+1)`

Mathlib has only the *real* `Real.hasSum_pow_div_log_of_abs_lt_one`.  This file supplies the complex
analogue, the keystone bridge for the logarithmic singularity transfer (`LogTransfer`).

Reuses Mathlib's `Complex.logTaylor` remainder bound `norm_log_one_sub_inv_add_logTaylor_neg_le`:
the partial sums `∑_{j<N} zʲ⁺¹/(j+1) = −logTaylor(N+1)(−z)` converge to `log((1−z)⁻¹) = −log(1−z)`, and
the series is geometric-summable.
-/

open Filter Complex
open scoped Topology BigOperators

namespace AnalyticCombinatorics

/-- `logTaylor (N+1) (−z) = −∑_{n<N} zⁿ⁺¹/(n+1)`. -/
lemma logTaylor_neg_eq_neg_sum (N : ℕ) (z : ℂ) :
    Complex.logTaylor (N + 1) (-z)
      = -∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
  induction N with
  | zero => simp [Complex.logTaylor]
  | succ N ih =>
    have hterm : (-1 : ℂ) ^ (N + 1 + 1) * (-z) ^ (N + 1) / ((N + 1 : ℕ) : ℂ)
        = -(z ^ (N + 1) / ((N + 1 : ℕ) : ℂ)) := by
      have hne : ((-1 : ℂ)) ^ (N + 1 + 1) * (-1) ^ (N + 1) = -1 := by
        rw [← pow_add]; exact Odd.neg_one_pow ⟨N + 1, by ring⟩
      have hz1 : ((-z) ^ (N + 1) : ℂ) = (-1) ^ (N + 1) * z ^ (N + 1) := by rw [neg_pow]
      rw [hz1, ← mul_assoc, hne]
      push_cast
      ring
    rw [Complex.logTaylor_succ, Pi.add_apply, ih, hterm, Finset.sum_range_succ, neg_add]

/-- **Complex logarithm series**: for `‖z‖ < 1`, `∑ₙ zⁿ⁺¹/(n+1) = −log(1−z)`. -/
theorem hasSum_pow_succ_div_succ_neg_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) (-Complex.log (1 - z)) := by
  have hmz : (0 : ℝ) < 1 - ‖z‖ := by linarith
  have hinv : (0 : ℝ) ≤ (1 - ‖z‖)⁻¹ := le_of_lt (inv_pos.mpr hmz)
  -- summability (dominated by the geometric series)
  have hgeo : Summable (fun n : ℕ => ‖z‖ ^ (n + 1)) := by
    simpa [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right ‖z‖
  have hsummable : Summable (fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) := by
    refine Summable.of_norm_bounded hgeo (fun n => ?_)
    rw [norm_div, norm_pow, Complex.norm_natCast]
    apply div_le_self (by positivity)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
  -- partial sums → -log(1-z)
  have harg : (1 - z).arg ≠ Real.pi := by
    have h := Complex.slitPlane_arg_ne_pi
      (Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by rwa [norm_neg]))
    rwa [sub_eq_add_neg]
  have hloginv : Complex.log (1 - z)⁻¹ = -Complex.log (1 - z) := Complex.log_inv _ harg
  have htend0 : Tendsto
      (fun N : ℕ => Complex.log (1 - z)⁻¹ + Complex.logTaylor (N + 1) (-z)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hp : Tendsto (fun N : ℕ => ‖z‖ ^ (N + 1)) atTop (𝓝 0) := by
      simpa [pow_succ] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg z) hz).mul_const ‖z‖
    have hmaj : Tendsto (fun N : ℕ => ‖z‖ ^ (N + 1) * (1 - ‖z‖)⁻¹) atTop (𝓝 0) := by
      simpa using hp.mul_const ((1 - ‖z‖)⁻¹)
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hmaj
    refine (norm_log_one_sub_inv_add_logTaylor_neg_le N hz).trans ?_
    refine div_le_self (mul_nonneg (by positivity) hinv) ?_
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
      atTop (𝓝 (-Complex.log (1 - z))) := by
    have h1 : Tendsto
        (fun N : ℕ => Complex.log (1 - z)⁻¹
          - ∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) atTop (𝓝 0) := by
      simpa [logTaylor_neg_eq_neg_sum, sub_eq_add_neg] using htend0
    have h2 := (tendsto_const_nhds (α := ℕ) (x := Complex.log (1 - z)⁻¹)).sub h1
    simpa [hloginv] using h2
  -- assemble HasSum
  have hsum := hsummable.hasSum
  have hval : ∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) = -Complex.log (1 - z) :=
    tendsto_nhds_unique hsum.tendsto_sum_nat htend
  rwa [hval] at hsum

end AnalyticCombinatorics
