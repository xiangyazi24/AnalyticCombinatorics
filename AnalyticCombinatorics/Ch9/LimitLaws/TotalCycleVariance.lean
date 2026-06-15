import AnalyticCombinatorics.Ch9.LimitLaws.TotalCycleSecondMoment

/-!
# Exact variance of the total number of cycles in a uniform random permutation

The Goncharov–Kolchin companion to the cycle-count CLT: for `K_n` the total number of cycles of a
uniform random permutation of `[n]`,

  `E[K_n] = H_n`,   `Var(K_n) = H_n − H_n^{(2)}`,

where `H_n = ∑_{r=1}^n 1/r` and `H_n^{(2)} = ∑_{r=1}^n 1/r²`.

`TotalCycleSecondMoment` already reduces the variance to `H_n + cycleFitPairSum n − H_n²`.  This file
supplies the one remaining finite identity `cycleFitPairSum n = H_n² − H_n^{(2)}` (antidiagonal split
`1/(r(n+1−r)) = (1/r + 1/(n+1−r))/(n+1)` plus the reflection `r ↦ n+1−r`), giving the exact variance.
-/

noncomputable section

open scoped BigOperators

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

/-- First harmonic sum `H_n = ∑_{r=1}^n 1/r`. -/
noncomputable def cycleH1 (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹

/-- Second harmonic sum `H_n^{(2)} = ∑_{r=1}^n 1/r²`. -/
noncomputable def cycleH2 (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 n, ((r : ℝ)⁻¹) ^ 2

lemma cycleH1_succ (n : ℕ) :
    cycleH1 (n + 1) = cycleH1 n + ((n + 1 : ℕ) : ℝ)⁻¹ := by
  unfold cycleH1
  rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by
        ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sum_insert (by simp [Finset.mem_Icc])]
  ring

lemma cycleH2_succ (n : ℕ) :
    cycleH2 (n + 1) = cycleH2 n + (((n + 1 : ℕ) : ℝ)⁻¹) ^ 2 := by
  unfold cycleH2
  rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by
        ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sum_insert (by simp [Finset.mem_Icc])]
  ring

/-- The one nontrivial finite-set rearrangement: peeling level `n+1` off `cycleFitPairSum`. -/
lemma cycleFitPairSum_succ (n : ℕ) :
    cycleFitPairSum (n + 1)
      = cycleFitPairSum n
        + ∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹ * (((n + 1 - r : ℕ) : ℝ)⁻¹) := by
  classical
  have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 (n + 1) := by
    intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
  -- Step 1: the `n+1` row and column carry zero mass; reduce both sums to `Icc 1 n`.
  have hreduce :
      cycleFitPairSum (n + 1)
        = ∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
            (if r + s ≤ n + 1 then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0) := by
    unfold cycleFitPairSum
    refine (Finset.sum_subset hsub ?_).symm.trans ?_
    · intro r hr hrn
      rw [Finset.mem_Icc] at hr; rw [Finset.mem_Icc] at hrn
      apply Finset.sum_eq_zero; intro s hs
      rw [Finset.mem_Icc] at hs; rw [if_neg (by omega)]
    · apply Finset.sum_congr rfl; intro r hr
      rw [Finset.mem_Icc] at hr
      refine (Finset.sum_subset hsub ?_).symm
      intro s hs hsn
      rw [Finset.mem_Icc] at hs; rw [Finset.mem_Icc] at hsn
      rw [if_neg (by omega)]
  -- Step 2: split `[r+s ≤ n+1] = [r+s ≤ n] + [r+s = n+1]` termwise.
  have hsplit :
      (∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
          (if r + s ≤ n + 1 then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0))
        = (∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
            ((if r + s ≤ n then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0)
              + (if r + s = n + 1 then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0))) := by
    apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro s _
    by_cases h1 : r + s ≤ n
    · rw [if_pos h1, if_pos (by omega), if_neg (by omega), add_zero]
    · by_cases h2 : r + s = n + 1
      · rw [if_neg h1, if_pos (by omega), if_pos h2, zero_add]
      · rw [if_neg h1, if_neg (by omega), if_neg h2, add_zero]
  -- boundary collapses to the antidiagonal
  have hbdry :
      (∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
          (if r + s = n + 1 then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0))
        = ∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹ * (((n + 1 - r : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_congr rfl; intro r hr; rw [Finset.mem_Icc] at hr
    rw [Finset.sum_eq_single_of_mem (n + 1 - r) (Finset.mem_Icc.mpr (by omega))]
    · rw [if_pos (by omega)]
    · intro s _ hsne; rw [if_neg (by omega)]
  have hAeq :
      (∑ r ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc 1 n,
          (if r + s ≤ n then (r : ℝ)⁻¹ * (s : ℝ)⁻¹ else 0)) = cycleFitPairSum n := rfl
  rw [hreduce, hsplit]
  simp_rw [Finset.sum_add_distrib]
  rw [hAeq, hbdry]

/-- Antidiagonal splitting of a reciprocal product on the line `r + s = n+1`. -/
lemma inv_boundary_point {n r : ℕ} (hr : r ∈ Finset.Icc 1 n) :
    (r : ℝ)⁻¹ * (((n + 1 - r : ℕ) : ℝ)⁻¹)
      = (((r : ℝ)⁻¹) + (((n + 1 - r : ℕ) : ℝ)⁻¹)) / ((n + 1 : ℕ) : ℝ) := by
  rw [Finset.mem_Icc] at hr
  have hcast : ((n + 1 - r : ℕ) : ℝ) = (n : ℝ) + 1 - r := by
    rw [Nat.cast_sub (by omega : r ≤ n + 1)]; push_cast; ring
  have hNR : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast, hNR]
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 - r := by
    have : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr.2
    linarith
  have hnrR : ((n : ℝ) + 1 - r) ≠ 0 := ne_of_gt hpos
  have hN1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Reflection `r ↦ n+1−r` fixes `H_n`. -/
lemma boundary_inv_sum_symm (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, (((n + 1 - r : ℕ) : ℝ)⁻¹)) = cycleH1 n := by
  unfold cycleH1
  refine Finset.sum_nbij' (fun r => n + 1 - r) (fun r => n + 1 - r) ?_ ?_ ?_ ?_ ?_
  · intro r hr; rw [Finset.mem_Icc] at hr; show n + 1 - r ∈ Finset.Icc 1 n
    rw [Finset.mem_Icc]; omega
  · intro r hr; rw [Finset.mem_Icc] at hr; show n + 1 - r ∈ Finset.Icc 1 n
    rw [Finset.mem_Icc]; omega
  · intro r hr; rw [Finset.mem_Icc] at hr; show n + 1 - (n + 1 - r) = r; omega
  · intro r hr; rw [Finset.mem_Icc] at hr; show n + 1 - (n + 1 - r) = r; omega
  · intro r _; rfl

/-- Antidiagonal reciprocal sum `∑ 1/(r(n+1−r)) = 2 H_n/(n+1)`. -/
lemma boundary_pair_sum_eq_two_mul_harmonic_div (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹ * (((n + 1 - r : ℕ) : ℝ)⁻¹))
      = 2 * cycleH1 n / ((n + 1 : ℕ) : ℝ) := by
  have hstep :
      (∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹ * (((n + 1 - r : ℕ) : ℝ)⁻¹))
        = (∑ r ∈ Finset.Icc 1 n,
            (((r : ℝ)⁻¹) + (((n + 1 - r : ℕ) : ℝ)⁻¹))) / ((n + 1 : ℕ) : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro r hr
    rw [inv_boundary_point hr]
  rw [hstep, Finset.sum_add_distrib, boundary_inv_sum_symm]
  unfold cycleH1
  ring

/-- **The exact pair-sum identity** `cycleFitPairSum n = H_n² − H_n^{(2)}`. -/
theorem cycleFitPairSum_eq_harmonic_sq_sub_harmonic2 (n : ℕ) :
    cycleFitPairSum n = cycleH1 n ^ 2 - cycleH2 n := by
  induction n with
  | zero => simp [cycleFitPairSum, cycleH1, cycleH2]
  | succ n ih =>
      rw [cycleFitPairSum_succ, ih, boundary_pair_sum_eq_two_mul_harmonic_div,
        cycleH1_succ, cycleH2_succ]
      have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- **Exact variance of the total cycle count**: `Var(K_n) = H_n − H_n^{(2)}`. -/
theorem totalCycleCount_variance_eq_harmonic_sub_harmonic2 (n : ℕ) :
    FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ) ^ 2) -
      (FixedPointsPoissonNS.uniformPermExpectation n
        (fun σ => (totalCycleCount n σ : ℝ))) ^ 2
      = cycleH1 n - cycleH2 n := by
  rw [totalCycleCount_variance_eq_harmonic_add_fitPairSum_sub_sq,
    cycleFitPairSum_eq_harmonic_sq_sub_harmonic2]
  have hH : (∑ r ∈ Finset.Icc 1 n, (r : ℝ)⁻¹) = cycleH1 n := rfl
  rw [hH]; ring

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
