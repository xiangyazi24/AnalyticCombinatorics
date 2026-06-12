import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.PermutationCycles
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

/-- Linearity of the uniform permutation expectation over a finite double sum. -/
lemma uniformPermExpectation_finset_sum₂ (n : ℕ) (S T : Finset ℕ)
    (g : ℕ → ℕ → Equiv.Perm (Fin n) → ℝ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => ∑ r ∈ S, ∑ s ∈ T, g r s σ) =
      ∑ r ∈ S, ∑ s ∈ T,
        FixedPointsPoissonNS.uniformPermExpectation n (fun σ => g r s σ) := by
  rw [uniformPermExpectation_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [uniformPermExpectation_finset_sum]

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

/-- The same exact mean identity in the `cycleH` notation used by the cycle-count
quasi-powers CLT. -/
theorem expected_totalCycles_eq_cycleH (n : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ => (totalCycleCount n σ : ℝ)) = cycleH n := by
  rw [expected_totalCycles_eq_harmonic, cycleH]
  norm_num [harmonic_eq_sum_Icc]

/-- Expanding the square of the total cycle count reduces its second moment to
the matrix of two-length product moments. -/
theorem expected_totalCycles_sq_eq_sum_products (n : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ) ^ 2) =
      ∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
        FixedPointsPoissonNS.uniformPermExpectation n
          (fun σ => (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ)) := by
  have hpoint :
      (fun σ : Equiv.Perm (Fin n) => (totalCycleCount n σ : ℝ) ^ 2) =
        fun σ =>
          ∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
            (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ) := by
    funext σ
    unfold totalCycleCount
    push_cast
    rw [pow_two, Finset.sum_mul_sum]
  rw [hpoint, uniformPermExpectation_finset_sum₂]

#print axioms expected_totalCycles_eq_cycleH
#print axioms expected_totalCycles_sq_eq_sum_products

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
