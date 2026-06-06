import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateAssembly
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentBound
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentSharp
import AnalyticCombinatorics.Ch8.Partitions.MassRateCoef
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernelClose

/-!
# Mass-rate campaign: §5 the second-order divisor calc

`kernelMass n = ∑_{m=1}^{n-1} σ(m)/(n−m)·exp(−C(√n−√(n−m)))` versus
`kernelMassApprox2 n = (1/n)M₀(t)+(1/n²)M₁(t)−(C/(8n²√n))M₂(t)` at `t=λ/√n`.

Brick 1 here: `kernelMassApprox2 n = ∑' m, modelSummand n m`, where
`modelSummand n m = σ(m)·e^{−tm}·(1/n + m/n² − Cm²/(8n²√n))` — i.e. the moment package collapses
to a single divisor-weighted Lambert sum.  This is the object the per-term estimate
`erdosWeight_coef_second_order` (#97), multiplied by `σ(m)≥0`, is compared against.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The model (leading-order) summand of the kernel mass at `m`: the divisor-weighted Lambert term
whose tsum over `m` is `kernelMassApprox2 n`. -/
noncomputable def modelSummand (n m : ℕ) : ℝ :=
  if m = 0 then 0
  else Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))
    * (1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 - C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ)))

private lemma sigmaR_zero : Sigma.sigmaR 0 = 0 := by
  simp [Sigma.sigmaR]

/-- Summability of the (sign-adjusted) Lambert summand `m^r σ(m) e^{−tm}` for `t > 0`. -/
private lemma summable_sigma_exp (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ =>
      if m = 0 then (0:ℝ) else (m:ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))) := by
  have hnorm : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hg := summable_pow_sigma_geometric r (r := Real.exp (-t)) hnorm
  refine hg.congr ?_
  intro m
  rcases eq_or_ne m 0 with h | h
  · subst h; simp [sigmaR_zero]
  · rw [if_neg h, abs_of_pos (Real.exp_pos _)]
    have hpow : Real.exp (-t) ^ m = Real.exp (-t * (m:ℝ)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hpow]

/-- **Model identity** (§5 brick 1): `kernelMassApprox2 n = ∑' m, modelSummand n m`. -/
theorem kernelMassApprox2_eq_tsum_model {n : ℕ} (hn : 1 ≤ n) :
    kernelMassApprox2 n = ∑' m : ℕ, modelSummand n m := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have ht0 : 0 < massLam / Real.sqrt (n:ℝ) := div_pos massLam_pos hs0
  -- scaled summability of the three Lambert summands
  have h0c : Summable (fun m : ℕ => (1 / (n:ℝ)) *
      (if m = 0 then (0:ℝ) else (m:ℝ) ^ 0 * Sigma.sigmaR m *
        Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))) :=
    (summable_sigma_exp 0 ht0).mul_left _
  have h1c : Summable (fun m : ℕ => (1 / (n:ℝ) ^ 2) *
      (if m = 0 then (0:ℝ) else (m:ℝ) ^ 1 * Sigma.sigmaR m *
        Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))) :=
    (summable_sigma_exp 1 ht0).mul_left _
  have h2c : Summable (fun m : ℕ => (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) *
      (if m = 0 then (0:ℝ) else (m:ℝ) ^ 2 * Sigma.sigmaR m *
        Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))) :=
    (summable_sigma_exp 2 ht0).mul_left _
  simp only [kernelMassApprox2, sigmaMoment]
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  rw [← h0c.tsum_add h1c, ← (h0c.add h1c).tsum_sub h2c]
  apply tsum_congr
  intro m
  rcases eq_or_ne m 0 with h | h
  · subst h; simp [modelSummand]
  · simp only [if_neg h, modelSummand]
    ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
