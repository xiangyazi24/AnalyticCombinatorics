import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoisson
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesFactorialMoment

/-!
# Expected number of cycles of a random permutation

The total number of cycles (orbits, including fixed points) of a permutation of `Fin n` is
`∑_{r=1}^{n} C_{n,r}`, where `C_{n,r} = rCycleCount n r` is the number of length-`r` cycles.
Summing the banked per-length means `E[C_{n,r}] = 1/r` (`rCycle_mean_eq_inv`) over `r = 1,…,n` by
linearity of expectation gives the classical identity

  `E[#cycles] = ∑_{r=1}^{n} 1/r = H_n`,

the `n`-th harmonic number.  (Asymptotically `H_n ∼ log n`, recovering the Goncharov result that a
uniform random permutation has about `log n` cycles.)

This is a genuine consequence of the factorial-moment machinery, not a Mathlib re-statement.
-/

noncomputable section

open Filter
open scoped BigOperators

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

/-- The total number of cycles (orbits, including fixed points) of `σ`, as the sum over all possible
lengths `r = 1,…,n` of the number of length-`r` cycles. -/
def totalCycleCount (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ r ∈ Finset.Icc 1 n, rCycleCount n r σ

/-- Linearity of the uniform permutation expectation over a finite sum of random variables. -/
lemma uniformPermExpectation_finset_sum (n : ℕ) (S : Finset ℕ)
    (g : ℕ → Equiv.Perm (Fin n) → ℝ) :
    FixedPointsPoissonNS.uniformPermExpectation n (fun σ => ∑ r ∈ S, g r σ) =
      ∑ r ∈ S, FixedPointsPoissonNS.uniformPermExpectation n (fun σ => g r σ) := by
  unfold FixedPointsPoissonNS.uniformPermExpectation
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]

/-- **Expected number of cycles of a uniform random permutation is the harmonic number.**
`E[ ∑_{r=1}^{n} C_{n,r} ] = ∑_{r=1}^{n} 1/r`. -/
theorem expected_totalCycles_eq_harmonic (n : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ => (totalCycleCount n σ : ℝ)) =
        ∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹ := by
  have hcast :
      (fun σ : Equiv.Perm (Fin n) => (totalCycleCount n σ : ℝ)) =
        fun σ => ∑ r ∈ Finset.Icc 1 n, ((rCycleCount n r σ : ℝ)) := by
    funext σ
    unfold totalCycleCount
    push_cast
    rfl
  rw [hcast, uniformPermExpectation_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Finset.mem_Icc] at hr
  have hpos : 0 < r := hr.1
  have hle : r ≤ n := hr.2
  rw [rCycle_mean_eq_inv hpos hle]
  simp

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
