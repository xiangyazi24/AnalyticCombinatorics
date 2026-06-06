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

/-- **Error-moment bound** (§5 brick 2): the divisor-weighted majorant of the second-order error,
`(3C²+5C+2)·[(1/n³)M₂ + (1/(n³√n))M₃ + (1/n⁴)M₄]` at `t=λ/√n`, is `O(1/n)`.  Pure application of the
sharp moment bound `sigmaMoment_le_power_sharp` (#119) at `r=2,3,4` with `t=λ/√n` (so
`1/t^{r+2}=O(n^{(r+2)/2})`).  This is the `O(1/n)` core that the main-range `#97×σ(m)` error sums to. -/
theorem model_error_moment_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (3 * C ^ 2 + 5 * C + 2) *
        ((1 / (n:ℝ) ^ 3) * sigmaMoment 2 (massLam / Real.sqrt (n:ℝ))
         + (1 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
         + (1 / (n:ℝ) ^ 4) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ)))
        ≤ K / (n:ℝ) := by
  obtain ⟨K2, hK2nn, hK2⟩ := sigmaMoment_le_power_sharp 2
  obtain ⟨K3, hK3nn, hK3⟩ := sigmaMoment_le_power_sharp 3
  obtain ⟨K4, hK4nn, hK4⟩ := sigmaMoment_le_power_sharp 4
  set lam : ℝ := massLam with hlamdef
  have hlam0 : 0 < lam := massLam_pos
  have hlamne : lam ≠ 0 := hlam0.ne'
  have hCpos : 0 < C := C_pos
  have hcoef : 0 ≤ 3 * C ^ 2 + 5 * C + 2 := by positivity
  have hinner : 0 ≤ K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6 :=
    add_nonneg (add_nonneg (div_nonneg hK2nn (by positivity)) (div_nonneg hK3nn (by positivity)))
      (div_nonneg hK4nn (by positivity))
  refine ⟨(3 * C ^ 2 + 5 * C + 2) * (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) + 1, ?_, ?_⟩
  · have := mul_nonneg hcoef hinner; linarith
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (1:ℝ) ≤ (n : ℝ) ∧ lam ^ 2 ≤ (n : ℝ) := by
    rw [eventually_atTop]
    refine ⟨max 1 ⌈lam ^ 2⌉₊, fun n hn => ?_⟩
    refine ⟨by exact_mod_cast (le_trans (le_max_left _ _) hn), ?_⟩
    have h2 : (⌈lam ^ 2⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_trans (le_max_right _ _) hn)
    exact le_trans (Nat.le_ceil _) h2
  filter_upwards [hev] with n hn
  obtain ⟨hn1, hnlam⟩ := hn
  have hnpos : (0:ℝ) < (n : ℝ) := by linarith
  set s : ℝ := Real.sqrt (n:ℝ) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hnpos
  have hsne : s ≠ 0 := hs0.ne'
  have hs2 : s ^ 2 = (n : ℝ) := by rw [hsdef, Real.sq_sqrt hnpos.le]
  set t : ℝ := lam / s with htdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one hs0, ← Real.sqrt_sq hlam0.le, hsdef]
    exact Real.sqrt_le_sqrt hnlam
  have hM2 := hK2 t ht0 ht1
  have hM3 := hK3 t ht0 ht1
  have hM4 := hK4 t ht0 ht1
  -- per-term bounds, each ≤ (Kr/lam^?)/n
  have e2 : (1 / (n:ℝ) ^ 3) * (K2 / t ^ 4) = (K2 / lam ^ 4) / (n:ℝ) := by
    rw [htdef, ← hs2]; field_simp
  have e3 : (1 / ((n:ℝ) ^ 3 * s)) * (K3 / t ^ 5) = (K3 / lam ^ 5) / (n:ℝ) := by
    rw [htdef, ← hs2]; field_simp
  have e4 : (1 / (n:ℝ) ^ 4) * (K4 / t ^ 6) = (K4 / lam ^ 6) / (n:ℝ) := by
    rw [htdef, ← hs2]; field_simp
  have b2 : (1 / (n:ℝ) ^ 3) * sigmaMoment 2 t ≤ (K2 / lam ^ 4) / (n:ℝ) := by
    rw [← e2]; exact mul_le_mul_of_nonneg_left hM2 (by positivity)
  have b3 : (1 / ((n:ℝ) ^ 3 * s)) * sigmaMoment 3 t ≤ (K3 / lam ^ 5) / (n:ℝ) := by
    rw [← e3]; exact mul_le_mul_of_nonneg_left hM3 (by positivity)
  have b4 : (1 / (n:ℝ) ^ 4) * sigmaMoment 4 t ≤ (K4 / lam ^ 6) / (n:ℝ) := by
    rw [← e4]; exact mul_le_mul_of_nonneg_left hM4 (by positivity)
  -- assemble; note the goal's sqrt/massLam fold to s/lam/t
  have hsum : (1 / (n:ℝ) ^ 3) * sigmaMoment 2 t
      + (1 / ((n:ℝ) ^ 3 * s)) * sigmaMoment 3 t
      + (1 / (n:ℝ) ^ 4) * sigmaMoment 4 t
      ≤ (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) / (n:ℝ) := by
    have : (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) / (n:ℝ)
        = (K2 / lam ^ 4) / (n:ℝ) + (K3 / lam ^ 5) / (n:ℝ) + (K4 / lam ^ 6) / (n:ℝ) := by ring
    rw [this]; linarith [b2, b3, b4]
  calc (3 * C ^ 2 + 5 * C + 2) *
        ((1 / (n:ℝ) ^ 3) * sigmaMoment 2 t
         + (1 / ((n:ℝ) ^ 3 * s)) * sigmaMoment 3 t
         + (1 / (n:ℝ) ^ 4) * sigmaMoment 4 t)
      ≤ (3 * C ^ 2 + 5 * C + 2) *
          ((K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) / (n:ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hcoef
    _ ≤ ((3 * C ^ 2 + 5 * C + 2) * (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) + 1) / (n:ℝ) := by
        have h1n : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
        have hL : (3 * C ^ 2 + 5 * C + 2) * ((K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) / (n:ℝ))
            = (3 * C ^ 2 + 5 * C + 2) * (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) / (n:ℝ) := by
          ring
        have hR : ((3 * C ^ 2 + 5 * C + 2) * (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) + 1) / (n:ℝ)
            = (3 * C ^ 2 + 5 * C + 2) * (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) / (n:ℝ)
              + 1 / (n:ℝ) := by ring
        rw [hL, hR]; linarith

/-- **Per-term error** (§5 brick 3): on the main range (`2m≤n`, `4Cm²≤√n³`), the per-`m` error
`|erdosWeight n m − modelSummand n m|` is `σ(m)·#97RHS` — i.e. the divisor-weighted form of
`erdosWeight_coef_second_order` (#97).  Both `erdosWeight` and `modelSummand` factor as `σ(m)·(·)`. -/
theorem erdosWeight_sub_model_le {n m : ℕ} (hn : 1 ≤ n) (hm1 : 1 ≤ m)
    (h2m : 2 * m ≤ n) (hsmall : 4 * C * (m:ℝ) ^ 2 ≤ Real.sqrt (n:ℝ) ^ 3) :
    |erdosWeight n m - modelSummand n m|
      ≤ Sigma.sigmaR m * ((3 * C ^ 2 + 5 * C + 2) *
          Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
          ((m:ℝ) ^ 2 / (n:ℝ) ^ 3 + (m:ℝ) ^ 3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))
            + (m:ℝ) ^ 4 / (n:ℝ) ^ 4)) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hsqrt0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have hsq : Real.sqrt (n:ℝ) ^ 2 = (n:ℝ) := Real.sq_sqrt hnpos.le
  have hσnn : 0 ≤ Sigma.sigmaR m := sigmaR_nonneg m
  have hmne : ¬ m = 0 := by omega
  -- exp argument identity (massLam = C/2, √n)
  have hexparg : -(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)
      = -(C / 2) * (m:ℝ) / Real.sqrt (n:ℝ) := by rw [massLam]; ring
  -- √n powers in terms of n
  have hcube : Real.sqrt (n:ℝ) ^ 3 = (n:ℝ) * Real.sqrt (n:ℝ) := by
    linear_combination Real.sqrt (n:ℝ) * hsq
  have h6 : Real.sqrt (n:ℝ) ^ 6 = (n:ℝ) ^ 3 := by
    rw [show (6:ℕ) = 2 * 3 from rfl, pow_mul, hsq]
  have h7 : Real.sqrt (n:ℝ) ^ 7 = (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) := by
    rw [show (7:ℕ) = 6 + 1 from rfl, pow_succ, h6]
  have h8 : Real.sqrt (n:ℝ) ^ 8 = (n:ℝ) ^ 4 := by
    rw [show (8:ℕ) = 2 * 4 from rfl, pow_mul, hsq]
  -- factor σ out of erdosWeight and modelSummand
  have hweight : erdosWeight n m
      = Sigma.sigmaR m * (1 / ((n - m : ℕ):ℝ) *
          Real.exp (-C * (Real.sqrt (n:ℝ) - Real.sqrt ((n - m : ℕ):ℝ)))) := by
    rw [erdosWeight]; ring
  have hmodel : modelSummand n m
      = Sigma.sigmaR m * ((1 / (n:ℝ)) * Real.exp (-(C / 2) * (m:ℝ) / Real.sqrt (n:ℝ)) *
          (1 + (m:ℝ) / (n:ℝ) - C * (m:ℝ) ^ 2 / (8 * Real.sqrt (n:ℝ) ^ 3))) := by
    rw [modelSummand, if_neg hmne, hexparg, hcube]
    field_simp
  -- the difference is σ · (#97 inner expression)
  have hfac : erdosWeight n m - modelSummand n m
      = Sigma.sigmaR m * (1 / ((n - m : ℕ):ℝ) *
            Real.exp (-C * (Real.sqrt (n:ℝ) - Real.sqrt ((n - m : ℕ):ℝ)))
          - (1 / (n:ℝ)) * Real.exp (-(C / 2) * (m:ℝ) / Real.sqrt (n:ℝ)) *
            (1 + (m:ℝ) / (n:ℝ) - C * (m:ℝ) ^ 2 / (8 * Real.sqrt (n:ℝ) ^ 3))) := by
    rw [hweight, hmodel]; ring
  -- convert the stated RHS to #97's RHS
  have hRHS : (3 * C ^ 2 + 5 * C + 2) *
        Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
        ((m:ℝ) ^ 2 / (n:ℝ) ^ 3 + (m:ℝ) ^ 3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))
          + (m:ℝ) ^ 4 / (n:ℝ) ^ 4)
      = (3 * C ^ 2 + 5 * C + 2) *
        Real.exp (-(C / 2) * (m:ℝ) / Real.sqrt (n:ℝ)) *
        ((m:ℝ) ^ 2 / Real.sqrt (n:ℝ) ^ 6 + (m:ℝ) ^ 3 / Real.sqrt (n:ℝ) ^ 7
          + (m:ℝ) ^ 4 / Real.sqrt (n:ℝ) ^ 8) := by
    rw [hexparg, h6, h7, h8]
  rw [hfac, abs_mul, abs_of_nonneg hσnn, hRHS]
  exact mul_le_mul_of_nonneg_left
    (erdosWeight_coef_second_order hn hm1 h2m hsmall) hσnn

end AnalyticCombinatorics.Ch8.Partitions.Erdos
