import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.SigmaSummatory

/-!
# Window differences of the divisor summatory function

From the banked `sigma_summatory_asymptotic` (`Σ_{m≤x} σ₁(m) = π²x²/12 + O(x log x)` with an
explicit constant), the difference of the summatory over a window `(α√n, β√n]` is
`(π²/12)·n·(β²−α²) + O(√n·log n)` — the estimate the Erdős kernel window limit consumes.

Opus-authored during the codex quota outage (Jun 5–10).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

/-- Convenience: the summatory function `S(x) = Σ_{m ∈ Icc 1 ⌊x⌋} σR m`. -/
noncomputable def summatory (x : ℝ) : ℝ := ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, sigmaR m

/-- The summatory window difference: for `1 ≤ α√n < β√n`,
`|S(β√n) − S(α√n) − (π²/12)n(β²−α²)| ≤ K·(α+β)·√n·log(2β√n)` with the explicit `K` from
`sigma_summatory_asymptotic`. -/
theorem summatory_window_diff :
    ∃ K, 0 < K ∧ ∀ α β : ℝ, ∀ n : ℕ, 0 ≤ α → α < β →
      1 ≤ α * Real.sqrt n →
      |summatory (β * Real.sqrt n) - summatory (α * Real.sqrt n)
          - (Real.pi ^ 2 / 12) * (n : ℝ) * (β ^ 2 - α ^ 2)|
        ≤ K * (α + β) * Real.sqrt n * Real.log (2 * (β * Real.sqrt n)) := by
  obtain ⟨K, hK, hbound⟩ := sigma_summatory_asymptotic
  refine ⟨K, hK, ?_⟩
  intro α β n hα hαβ hα1
  have hsq : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hβ1 : 1 ≤ β * Real.sqrt n := le_trans hα1 (by
    have : α * Real.sqrt n ≤ β * Real.sqrt n :=
      mul_le_mul_of_nonneg_right hαβ.le hsq
    linarith)
  have hβpos : 0 < β := lt_of_le_of_lt hα hαβ
  -- the two endpoint estimates
  have hA := hbound (α * Real.sqrt n) hα1
  have hB := hbound (β * Real.sqrt n) hβ1
  -- (α√n)² = α²·n  and  (β√n)² = β²·n
  have hsqn : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hA2 : (α * Real.sqrt n) ^ 2 = α ^ 2 * (n : ℝ) := by
    rw [mul_pow, sq, sq, hsqn]
  have hB2 : (β * Real.sqrt n) ^ 2 = β ^ 2 * (n : ℝ) := by
    rw [mul_pow, sq, sq, hsqn]
  -- main term difference matches
  have hmain :
      (Real.pi ^ 2 / 12) * (β * Real.sqrt n) ^ 2
        - (Real.pi ^ 2 / 12) * (α * Real.sqrt n) ^ 2
        = (Real.pi ^ 2 / 12) * (n : ℝ) * (β ^ 2 - α ^ 2) := by
    rw [hA2, hB2]; ring
  -- log monotonicity: log(2α√n) ≤ log(2β√n)
  have hlogmono : Real.log (2 * (α * Real.sqrt n)) ≤ Real.log (2 * (β * Real.sqrt n)) := by
    apply Real.log_le_log (by linarith)
    have : α * Real.sqrt n ≤ β * Real.sqrt n :=
      mul_le_mul_of_nonneg_right hαβ.le hsq
    linarith
  -- assemble: |S(β√n)−S(α√n) − main| ≤ |S(β√n)−π²(β√n)²/12| + |S(α√n)−π²(α√n)²/12|
  have key :
      |summatory (β * Real.sqrt n) - summatory (α * Real.sqrt n)
          - (Real.pi ^ 2 / 12) * (n : ℝ) * (β ^ 2 - α ^ 2)|
        ≤ K * (β * Real.sqrt n) * Real.log (2 * (β * Real.sqrt n))
          + K * (α * Real.sqrt n) * Real.log (2 * (α * Real.sqrt n)) := by
    have expand :
        summatory (β * Real.sqrt n) - summatory (α * Real.sqrt n)
            - (Real.pi ^ 2 / 12) * (n : ℝ) * (β ^ 2 - α ^ 2)
          = (summatory (β * Real.sqrt n) - (Real.pi ^ 2 / 12) * (β * Real.sqrt n) ^ 2)
            - (summatory (α * Real.sqrt n) - (Real.pi ^ 2 / 12) * (α * Real.sqrt n) ^ 2) := by
      rw [← hmain]; ring
    rw [expand]
    calc |(summatory (β * Real.sqrt n) - (Real.pi ^ 2 / 12) * (β * Real.sqrt n) ^ 2)
          - (summatory (α * Real.sqrt n) - (Real.pi ^ 2 / 12) * (α * Real.sqrt n) ^ 2)|
        ≤ |summatory (β * Real.sqrt n) - (Real.pi ^ 2 / 12) * (β * Real.sqrt n) ^ 2|
          + |summatory (α * Real.sqrt n) - (Real.pi ^ 2 / 12) * (α * Real.sqrt n) ^ 2| :=
          abs_sub _ _
      _ ≤ K * (β * Real.sqrt n) * Real.log (2 * (β * Real.sqrt n))
          + K * (α * Real.sqrt n) * Real.log (2 * (α * Real.sqrt n)) := by
          exact add_le_add hB hA
  -- final absorption: K·β√n·log(2β√n) + K·α√n·log(2α√n) ≤ K(α+β)√n·log(2β√n)
  refine key.trans ?_
  have hlogβpos : 0 ≤ Real.log (2 * (β * Real.sqrt n)) := by
    apply Real.log_nonneg; linarith
  have h2 : K * (α * Real.sqrt n) * Real.log (2 * (α * Real.sqrt n))
      ≤ K * (α * Real.sqrt n) * Real.log (2 * (β * Real.sqrt n)) := by
    apply mul_le_mul_of_nonneg_left hlogmono
    positivity
  calc K * (β * Real.sqrt n) * Real.log (2 * (β * Real.sqrt n))
        + K * (α * Real.sqrt n) * Real.log (2 * (α * Real.sqrt n))
      ≤ K * (β * Real.sqrt n) * Real.log (2 * (β * Real.sqrt n))
        + K * (α * Real.sqrt n) * Real.log (2 * (β * Real.sqrt n)) := by linarith
    _ = K * (α + β) * Real.sqrt n * Real.log (2 * (β * Real.sqrt n)) := by ring

end AnalyticCombinatorics.Ch8.Partitions.Sigma
