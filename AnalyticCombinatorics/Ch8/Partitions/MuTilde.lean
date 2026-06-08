import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.PartitionRenewal
import AnalyticCombinatorics.Ch8.Partitions.MassRateApprox2

/-!
# The smooth-rank conditional drift `μ̃` and its chain-drift identity

For the killed Erdős predecessor chain (`Pker n k = erdosWeight n (n−k)/kernelMass n`), the
martingale coordinate is the smooth rank `ρ(n) = 3√n`.  The one-step conditional decrement is

  `μ̃(n) = E_{k∼Pker(n,·)}[ρ(n) − ρ(k)] = 3 ∑_k Pker(n,k)(√n − √k)`.

This file defines `μ̃` via the predecessor (decrement) sum and records the identity tying it to the
chain drift through the reflection `k ↦ n−k` (`Pker_sum_mul`).  The two-term expansion
`μ̃(n) = μ̄ + μA/√n + O(1/n)` (the input to `two_term_local_lip`) is built in subsequent files from
the banked moment asymptotics (`sigmaMoment_one_two_term`, `sigmaMoment_two_asymp_weak`,
`sigmaMoment_le_power_sharp 3`) and the kernel-mass rate (`kernelMass → 1`).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The smooth-rank drop `3(√n − √(n−m))` from state `n` to predecessor value `n−m`
(decrement `m`). -/
noncomputable def rhoDrop (n m : ℕ) : ℝ :=
  3 * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))

/-- The (unnormalized) drift numerator `∑_{m=1}^{n-1} erdosWeight n m · ρ-drop`. -/
noncomputable def muNum (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * rhoDrop n m

/-- The smooth-rank conditional drift `μ̃(n) = muNum n / kernelMass n`. -/
noncomputable def muTilde (n : ℕ) : ℝ := muNum n / kernelMass n

/-- **Chain-drift identity**: `μ̃(n) = ∑_k Pker(n,k)·3(√n − √k)` — the genuine one-step
smooth-rank conditional decrement of the killed predecessor chain. -/
lemma muTilde_eq_drift {n : ℕ} (hn : 2 ≤ n) :
    muTilde n
      = ∑ k ∈ Finset.range n, Pker n k * (3 * (Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ))) := by
  rw [Pker_sum_mul n hn (fun k => 3 * (Real.sqrt (n : ℝ) - Real.sqrt (k : ℝ)))]
  unfold muTilde muNum rhoDrop
  rfl

/-- **Division step**: a two-term expansion of the numerator `muNum` transfers to `μ̃`, because
`kernelMass n = 1 + O(1/n)` (`kernelMass_sub_one_rate`).  Reduces the μ̃ expansion to a pure
numerator expansion. -/
lemma muTilde_expansion_of_muNum {c₀ c₁ : ℝ}
    (hnum : ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      |muNum n - (c₀ + c₁ / Real.sqrt (n : ℝ))| ≤ A / (n : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |muTilde n - (c₀ + c₁ / Real.sqrt (n : ℝ))| ≤ K / (n : ℝ) := by
  obtain ⟨A, hApos, hnumb⟩ := hnum
  obtain ⟨B, hBpos, hkm⟩ := kernelMass_sub_one_rate
  refine ⟨2 * (A + (|c₀| + |c₁|) * B), by positivity, ?_⟩
  filter_upwards [hnumb, hkm, Filter.eventually_ge_atTop (max 1 ⌈2 * B⌉₊)] with n hnumn hkmn hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hsqrtpos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hsqrt1 : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  -- kernelMass n ≥ 1/2
  have h2B : 2 * B ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hBn : B / (n : ℝ) ≤ 1 / 2 := by rw [div_le_iff₀ hnpos]; nlinarith [h2B]
  have hkmlo : (1 : ℝ) / 2 ≤ kernelMass n := by
    have := (abs_le.mp hkmn).1; linarith
  have hkmpos : (0 : ℝ) < kernelMass n := by linarith
  -- |c₀ + c₁/√n| ≤ |c₀| + |c₁|
  have hcbd : |c₀ + c₁ / Real.sqrt (n : ℝ)| ≤ |c₀| + |c₁| := by
    have hc1 : |c₁| / Real.sqrt (n : ℝ) ≤ |c₁| := by
      rw [div_le_iff₀ hsqrtpos]; nlinarith [abs_nonneg c₁, hsqrt1]
    calc |c₀ + c₁ / Real.sqrt (n : ℝ)| ≤ |c₀| + |c₁ / Real.sqrt (n : ℝ)| := abs_add_le _ _
      _ = |c₀| + |c₁| / Real.sqrt (n : ℝ) := by
          rw [abs_div, abs_of_pos hsqrtpos]
      _ ≤ |c₀| + |c₁| := by linarith
  -- rewrite μ̃ − target as N / kernelMass
  set L : ℝ := c₀ + c₁ / Real.sqrt (n : ℝ) with hLdef
  have key : muTilde n - L = (muNum n - L + L * (1 - kernelMass n)) / kernelMass n := by
    rw [muTilde]; field_simp; ring
  rw [key, abs_div, abs_of_pos hkmpos]
  -- numerator bound: |N| ≤ A/n + (|c₀|+|c₁|)·B/n
  have hNbd : |muNum n - L + L * (1 - kernelMass n)| ≤ A / (n : ℝ) + (|c₀| + |c₁|) * (B / (n : ℝ)) := by
    have h1 : |L * (1 - kernelMass n)| ≤ (|c₀| + |c₁|) * (B / (n : ℝ)) := by
      rw [abs_mul]
      have hkmabs : |1 - kernelMass n| ≤ B / (n : ℝ) := by
        rw [abs_sub_comm]; exact hkmn
      exact mul_le_mul hcbd hkmabs (abs_nonneg _) (by positivity)
    calc |muNum n - L + L * (1 - kernelMass n)|
        ≤ |muNum n - L| + |L * (1 - kernelMass n)| := abs_add_le _ _
      _ ≤ A / (n : ℝ) + (|c₀| + |c₁|) * (B / (n : ℝ)) := by
          have := hnumn; rw [hLdef] at this ⊢; linarith [h1]
  -- divide by kernelMass ≥ 1/2
  rw [div_le_div_iff₀ hkmpos hnpos]
  set N : ℝ := muNum n - L + L * (1 - kernelMass n) with hNdef
  set S : ℝ := A + (|c₀| + |c₁|) * B with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; positivity
  -- |N| · n ≤ S  (clear the 1/n in hNbd)
  have hNn : |N| * (n : ℝ) ≤ S := by
    have h := mul_le_mul_of_nonneg_right hNbd hnpos.le
    calc |N| * (n : ℝ)
        ≤ (A / (n : ℝ) + (|c₀| + |c₁|) * (B / (n : ℝ))) * (n : ℝ) := h
      _ = S := by rw [hSdef]; field_simp
  -- goal: |N| · n ≤ 2·S·kernelMass n, and 2·S·kernelMass ≥ 2·S·(1/2) = S ≥ |N|·n
  have hkmstep : S ≤ 2 * S * kernelMass n := by
    nlinarith [mul_nonneg hSnn (by linarith [hkmlo] : (0 : ℝ) ≤ 2 * kernelMass n - 1)]
  calc |N| * (n : ℝ) ≤ S := hNn
    _ ≤ 2 * S * kernelMass n := hkmstep

end AnalyticCombinatorics.Ch8.Partitions.Erdos
