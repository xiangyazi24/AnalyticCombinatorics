import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoisson
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesFactorialMoment
import AnalyticCombinatorics.Ch9.LimitLaws.JointCycleMoments
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonComplete

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

lemma sq_eq_self_of_le_one (k : ℕ) (hk : k ≤ 1) : k ^ 2 = k := by
  interval_cases k <;> norm_num

lemma rCycleCount_le_one_of_large {n r : ℕ} (hr : 0 < r) (hlarge : n < 2 * r)
    (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ ≤ 1 := by
  by_contra hle
  have htwo : 2 ≤ rCycleCount n r σ := by omega
  have hmul : 2 * r ≤ rCycleCount n r σ * r :=
    Nat.mul_le_mul_right r htwo
  have hcard := Complete.rCycleCount_mul_le_card (n := n) (r := r) hr σ
  exact (not_le_of_gt hlarge) (hmul.trans hcard)

/-- The finite second moment of the number of `r`-cycles is `1/r + 1/r²` when
there is room for two disjoint `r`-cycles. -/
theorem rCycle_second_moment_eq_inv_add_inv_sq {n r : ℕ} (hr : 0 < r) (h2 : 2 * r ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) ^ 2) =
      (r : ℝ)⁻¹ + ((r : ℝ)⁻¹) ^ 2 := by
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

/-- If a cycle of length `r` fits but two such cycles cannot fit, then `C_{n,r}`
is pointwise a `0/1` random variable, so its second moment equals its mean. -/
theorem rCycle_second_moment_eq_inv_of_large {n r : ℕ} (hr : 0 < r) (hrn : r ≤ n)
    (hlarge : n < 2 * r) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) ^ 2) = (r : ℝ)⁻¹ := by
  have hpoint :
      (fun σ : Equiv.Perm (Fin n) => (rCycleCount n r σ : ℝ) ^ 2) =
        fun σ => (rCycleCount n r σ : ℝ) := by
    funext σ
    have hsq :
        (rCycleCount n r σ) ^ 2 = rCycleCount n r σ :=
      sq_eq_self_of_le_one _ (rCycleCount_le_one_of_large hr hlarge σ)
    exact_mod_cast hsq
  rw [hpoint, rCycle_mean_eq_inv hr hrn]
  simp

/-- **Variance of the number of `r`-cycles equals `1/r`** (for `2r ≤ n`), matching the
Poisson(1/r) limit variance. -/
theorem rCycle_variance_eq_inv {n r : ℕ} (hr : 0 < r) (h2 : 2 * r ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) ^ 2) -
      (FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ))) ^ 2 = (r : ℝ)⁻¹ := by
  have hrn : r ≤ n := by omega
  have hmean :
      FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ)) = (r : ℝ)⁻¹ := by
    rw [rCycle_mean_eq_inv hr hrn]; simp
  rw [rCycle_second_moment_eq_inv_add_inv_sq hr h2, hmean]
  ring

/-- In the large-cycle regime `r ≤ n < 2r`, the variance is the Bernoulli variance
`1/r - 1/r²`. -/
theorem rCycle_variance_eq_inv_sub_inv_sq_of_large {n r : ℕ} (hr : 0 < r) (hrn : r ≤ n)
    (hlarge : n < 2 * r) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) ^ 2) -
      (FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ))) ^ 2 =
        (r : ℝ)⁻¹ - ((r : ℝ)⁻¹) ^ 2 := by
  have hmean :
      FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ)) = (r : ℝ)⁻¹ := by
    rw [rCycle_mean_eq_inv hr hrn]; simp
  rw [rCycle_second_moment_eq_inv_of_large hr hrn hlarge, hmean]

/-- **Cycle counts of two distinct lengths are uncorrelated**:
`Cov(C_{n,r}, C_{n,s}) = E[C_{n,r} C_{n,s}] - E[C_{n,r}] E[C_{n,s}] = 1/(rs) - (1/r)(1/s) = 0`
for distinct positive `r ≠ s` with `r + s ≤ n` — the second-moment shadow of asymptotic
independence (Goncharov–Kolchin). -/
theorem rCycle_covariance_eq_zero {n r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s)
    (h : r + s ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ)) -
      FixedPointsPoissonNS.uniformPermExpectation n (fun σ => (rCycleCount n r σ : ℝ)) *
        FixedPointsPoissonNS.uniformPermExpectation n (fun σ => (rCycleCount n s σ : ℝ)) = 0 := by
  have hrn : r ≤ n := by omega
  have hsn : s ≤ n := by omega
  have hxy :
      FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ)) =
          (r : ℝ)⁻¹ * (s : ℝ)⁻¹ := by
    have hmom := JointCycleMomentsNS.factorialMoment_two_rCycle_of_pos
      (n := n) (r := r) (s := s) (a := 1) (b := 1) hr hs hrs (by omega)
    simpa [Nat.descFactorial_one, zpow_neg_one] using hmom
  rw [hxy, rCycle_mean_eq_inv hr hrn, rCycle_mean_eq_inv hs hsn]
  simp

#print axioms rCycle_second_moment_eq_inv_add_inv_sq
#print axioms rCycle_second_moment_eq_inv_of_large
#print axioms rCycle_variance_eq_inv_sub_inv_sq_of_large

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
