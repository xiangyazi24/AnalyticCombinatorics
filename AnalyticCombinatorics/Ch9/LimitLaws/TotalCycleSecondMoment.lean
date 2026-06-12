import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.BivariateCyclePoisson
import AnalyticCombinatorics.Ch9.LimitLaws.CycleVariance
import AnalyticCombinatorics.Ch9.LimitLaws.ExpectedCycles

/-!
# Second moment matrix for the total number of cycles

This file assembles the diagonal and off-diagonal cycle-count moment bricks into
a single finite matrix formula for the second moment of the total number of
cycles in a uniform random permutation.
-/

noncomputable section

open scoped BigOperators

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

/-- Unified finite product-moment formula for two cycle lengths that separately fit in `Fin n`.

The first summand is the diagonal Bernoulli/counting contribution; the second
summand is present exactly when cycles of lengths `r` and `s` can coexist. -/
theorem cycle_product_moment_eq_diag_add_fit {n r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrn : r ≤ n) (hsn : s ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ)) =
      (if r = s then (r : ℝ)⁻¹ else 0) +
        if r + s ≤ n then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0 := by
  by_cases hrs : r = s
  · subst s
    by_cases hfit : r + r ≤ n
    · have h2 : 2 * r ≤ n := by omega
      have hsqfun :
          (fun σ : Equiv.Perm (Fin n) =>
              (rCycleCount n r σ : ℝ) * (rCycleCount n r σ : ℝ)) =
            fun σ => (rCycleCount n r σ : ℝ) ^ 2 := by
        funext σ
        ring
      rw [hsqfun, if_pos rfl, if_pos hfit, rCycle_second_moment_eq_inv_add_inv_sq hr h2]
      ring
    · have hlarge : n < 2 * r := by omega
      have hsqfun :
          (fun σ : Equiv.Perm (Fin n) =>
              (rCycleCount n r σ : ℝ) * (rCycleCount n r σ : ℝ)) =
            fun σ => (rCycleCount n r σ : ℝ) ^ 2 := by
        funext σ
        ring
      rw [hsqfun, if_pos rfl, if_neg hfit, rCycle_second_moment_eq_inv_of_large hr hrn hlarge]
      simp
  · by_cases hfit : r + s ≤ n
    · rw [if_neg hrs, if_pos hfit,
        Bivariate.joint_product_expectation_eq_inv_mul_inv_of_le hr hs hrs hfit]
      simp
    · have htail : n < r + s := Nat.lt_of_not_ge hfit
      rw [if_neg hrs, if_neg hfit,
        Bivariate.joint_product_expectation_eq_zero_of_lt hr hs hrs htail]
      simp

/-- The total cycle-count second moment as a finite matrix with diagonal and coexistence terms. -/
theorem expected_totalCycles_sq_eq_diag_add_fit_sum (n : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ) ^ 2) =
      ∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
        ((if r = s then (r : ℝ)⁻¹ else 0) +
          if r + s ≤ n then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0) := by
  rw [expected_totalCycles_sq_eq_sum_products]
  refine Finset.sum_congr rfl ?_
  intro r hrmem
  refine Finset.sum_congr rfl ?_
  intro s hsmem
  rw [Finset.mem_Icc] at hrmem hsmem
  exact cycle_product_moment_eq_diag_add_fit hrmem.1 hsmem.1 hrmem.2 hsmem.2

#print axioms cycle_product_moment_eq_diag_add_fit
#print axioms expected_totalCycles_sq_eq_diag_add_fit_sum

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
