import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoisson
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesFactorialMoment

/-!
# Variance of the number of `r`-cycles

From the banked factorial moments `E[(C_{n,r})_1] = 1/r` and `E[(C_{n,r})_2] = 1/r²`
(`rCycle_mean_eq_inv`, `factorialMoment_rCycle`), the variance of the number of length-`r`
cycles in a uniform random permutation is

  `Var(C_{n,r}) = E[(C_{n,r})_2] + E[C_{n,r}] - (E[C_{n,r}])² = 1/r² + 1/r - 1/r² = 1/r`,

for `2r ≤ n`.  This matches the variance `1/r` of the Poisson(1/r) limit, a second-moment
confirmation of `rCycles_tendstoInDistribution_poisson`.
-/

noncomputable section

open scoped BigOperators

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

/-- The pointwise identity `k² = (k)_2 + k` in `ℕ` (`(k)_2 = k(k-1)`). -/
lemma sq_eq_descFactorial_two_add (k : ℕ) : k ^ 2 = k.descFactorial 2 + k := by
  have hdf : k.descFactorial 2 = (k - 1) * k := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_one]
  rw [hdf]
  cases k with
  | zero => rfl
  | succ m => simp only [Nat.succ_sub_one]; ring

/-- `E[X²]` splits as `E[(X)_2] + E[X]` for the `r`-cycle count (linearity of the average). -/
lemma uniformPermExpectation_sq_eq (n r : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) ^ 2) =
      FixedPointsPoissonNS.uniformPermExpectation n
          (fun σ => ((rCycleCount n r σ).descFactorial 2 : ℝ)) +
        FixedPointsPoissonNS.uniformPermExpectation n
          (fun σ => (rCycleCount n r σ : ℝ)) := by
  unfold FixedPointsPoissonNS.uniformPermExpectation
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro σ _
  have hnat : (rCycleCount n r σ) ^ 2 =
      (rCycleCount n r σ).descFactorial 2 + rCycleCount n r σ :=
    sq_eq_descFactorial_two_add _
  have := congrArg (fun m : ℕ => (m : ℝ)) hnat
  push_cast at this ⊢
  linarith [this]

/-- **Variance of the number of `r`-cycles equals `1/r`** (for `2r ≤ n`), matching the
Poisson(1/r) limit variance. -/
theorem rCycle_variance_eq_inv {n r : ℕ} (hr : 0 < r) (h2 : 2 * r ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) ^ 2) -
      (FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ))) ^ 2 = (r : ℝ)⁻¹ := by
  have hrn : r ≤ n := by omega
  have hk2 : r * 2 ≤ n := by omega
  have hmean :
      FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ)) = (r : ℝ)⁻¹ := by
    rw [rCycle_mean_eq_inv hr hrn]; simp
  have key : (r : ℝ) ^ (-((2 : ℕ) : ℤ)) = ((r : ℝ)⁻¹) ^ 2 := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
  rw [uniformPermExpectation_sq_eq, hmean, factorialMoment_rCycle hr hk2, key]
  ring

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
