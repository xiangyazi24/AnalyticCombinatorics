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

/-- The main cutoff `⌊n^{2/3}⌋`: for `n` large, every `1 ≤ m ≤ ⌊n^{2/3}⌋` satisfies the two
side-conditions of `erdosWeight_coef_second_order` (#97): `2m ≤ n` and `4Cm² ≤ √n³`. -/
private lemma mainCut_cond :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℕ, 1 ≤ m → m ≤ ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ →
      2 * m ≤ n ∧ 4 * C * (m:ℝ) ^ 2 ≤ Real.sqrt (n:ℝ) ^ 3 := by
  have hCpos : 0 < C := C_pos
  rw [Filter.eventually_atTop]
  refine ⟨max 8 (⌈(4 * C) ^ 6⌉₊ + 1), fun n hn m hm1 hmle => ?_⟩
  have hn8 : 8 ≤ n := le_trans (le_max_left _ _) hn
  have hnC : ⌈(4 * C) ^ 6⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hp23 : (0:ℝ) ≤ (n:ℝ) ^ (2/3 : ℝ) := Real.rpow_nonneg hnpos.le _
  -- (m:ℝ) ≤ n^{2/3}
  have hmr : (m:ℝ) ≤ (n:ℝ) ^ (2/3 : ℝ) :=
    le_trans (by exact_mod_cast hmle) (Nat.floor_le hp23)
  have hmr0 : (0:ℝ) ≤ (m:ℝ) := by positivity
  -- cube root: 2 ≤ n^{1/3}
  have hcubrt : (2:ℝ) ≤ (n:ℝ) ^ (1/3 : ℝ) := by
    have h8 : (8:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn8
    have hmono : (8:ℝ) ^ (1/3 : ℝ) ≤ (n:ℝ) ^ (1/3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h8 (by norm_num)
    have h83 : (8:ℝ) ^ (1/3 : ℝ) = 2 := by
      rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, ← Real.rpow_natCast 2 3,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [h83] at hmono
  -- sixth root: 4C ≤ n^{1/6}
  have hsixrt : 4 * C ≤ (n:ℝ) ^ (1/6 : ℝ) := by
    have hbase : ((4 * C) ^ 6 : ℝ) ≤ (n:ℝ) := by
      have h1 : ((4 * C) ^ 6 : ℝ) ≤ (⌈(4 * C) ^ 6⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈(4 * C) ^ 6⌉₊ : ℕ):ℝ) ≤ (n:ℝ) := by
        have : ⌈(4 * C) ^ 6⌉₊ ≤ n := by omega
        exact_mod_cast this
      linarith
    have hmono : ((4 * C) ^ 6 : ℝ) ^ (1/6 : ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbase (by norm_num)
    have hid : ((4 * C) ^ 6 : ℝ) ^ (1/6 : ℝ) = 4 * C := by
      rw [← Real.rpow_natCast (4 * C) 6, ← Real.rpow_mul (by positivity)]
      norm_num
    rwa [hid] at hmono
  -- power identities
  have hn1 : (n:ℝ) = (n:ℝ) ^ (1/3 : ℝ) * (n:ℝ) ^ (2/3 : ℝ) := by
    rw [← Real.rpow_add hnpos]; norm_num
  have hsqrtcube : Real.sqrt (n:ℝ) ^ 3 = ((n:ℝ) ^ (2/3 : ℝ)) ^ 2 * (n:ℝ) ^ (1/6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((n:ℝ) ^ (1/2 : ℝ)) 3,
      ← Real.rpow_mul hnpos.le, ← Real.rpow_natCast ((n:ℝ) ^ (2/3 : ℝ)) 2,
      ← Real.rpow_mul hnpos.le, ← Real.rpow_add hnpos]
    norm_num
  refine ⟨?_, ?_⟩
  · -- 2 m ≤ n
    have hreal : 2 * (m:ℝ) ≤ (n:ℝ) := by
      calc 2 * (m:ℝ) ≤ 2 * (n:ℝ) ^ (2/3 : ℝ) := by linarith
        _ ≤ (n:ℝ) ^ (1/3 : ℝ) * (n:ℝ) ^ (2/3 : ℝ) := by
            apply mul_le_mul_of_nonneg_right hcubrt hp23
        _ = (n:ℝ) := hn1.symm
    exact_mod_cast hreal
  · -- 4 C m² ≤ √n³
    have hm2 : (m:ℝ) ^ 2 ≤ ((n:ℝ) ^ (2/3 : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ hmr0 hmr 2
    calc 4 * C * (m:ℝ) ^ 2 ≤ 4 * C * ((n:ℝ) ^ (2/3 : ℝ)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hm2 (by positivity)
      _ ≤ (n:ℝ) ^ (1/6 : ℝ) * ((n:ℝ) ^ (2/3 : ℝ)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hsixrt (by positivity)
      _ = Real.sqrt (n:ℝ) ^ 3 := by rw [hsqrtcube]; ring

/-- **Main-range error sum** (§5 brick 4): `∑_{m=1}^{⌊n^{2/3}⌋} |erdosWeight − modelSummand| ≤ K/n`.
Per-term `#97×σ(m)` (brick 3) on the cutoff range, then the finite divisor sums are `≤` the full
Lambert moments (`sum_le_tsum`), reducing to the `O(1/n)` moment bound (brick 2). -/
theorem main_range_error_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (∑ m ∈ Finset.Icc 1 ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊, |erdosWeight n m - modelSummand n m|)
        ≤ K / (n:ℝ) := by
  obtain ⟨K, hKpos, hKbound⟩ := model_error_moment_bound
  have hCpos : 0 < C := C_pos
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [mainCut_cond, hKbound, Filter.eventually_ge_atTop 1] with n hcond hKb hn1
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have ht0 : 0 < massLam / Real.sqrt (n:ℝ) := div_pos massLam_pos hs0
  set M : ℕ := ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ with hM
  -- step 1: per-term #97×σ
  have hstep1 : (∑ m ∈ Finset.Icc 1 M, |erdosWeight n m - modelSummand n m|)
      ≤ ∑ m ∈ Finset.Icc 1 M, Sigma.sigmaR m * ((3 * C ^ 2 + 5 * C + 2) *
          Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
          ((m:ℝ) ^ 2 / (n:ℝ) ^ 3 + (m:ℝ) ^ 3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))
            + (m:ℝ) ^ 4 / (n:ℝ) ^ 4)) := by
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmle⟩ := hm
    obtain ⟨h2m, hsmall⟩ := hcond m hm1 hmle
    exact erdosWeight_sub_model_le hn1 hm1 h2m hsmall
  -- step 2: rearrange each summand into the three moment summands
  have hrw : ∀ m : ℕ, Sigma.sigmaR m * ((3 * C ^ 2 + 5 * C + 2) *
        Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
        ((m:ℝ) ^ 2 / (n:ℝ) ^ 3 + (m:ℝ) ^ 3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))
          + (m:ℝ) ^ 4 / (n:ℝ) ^ 4))
      = (3 * C ^ 2 + 5 * C + 2) *
          ((1 / (n:ℝ) ^ 3) * ((m:ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
           + (1 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * ((m:ℝ) ^ 3 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
           + (1 / (n:ℝ) ^ 4) * ((m:ℝ) ^ 4 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))) := by
    intro m; ring
  rw [Finset.sum_congr rfl (fun m _ => hrw m), ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hstep1
  -- step 3: each finite divisor sum ≤ the full Lambert moment
  have hfin : ∀ r : ℕ, (∑ m ∈ Finset.Icc 1 M,
        (m:ℝ) ^ r * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
      ≤ sigmaMoment r (massLam / Real.sqrt (n:ℝ)) := by
    intro r
    have hge0 : ∀ k : ℕ, 0 ≤ (if k = 0 then (0:ℝ)
        else (k:ℝ) ^ r * Sigma.sigmaR k * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (k:ℝ))) := by
      intro k; rcases eq_or_ne k 0 with h | h
      · simp [h]
      · rw [if_neg h]
        exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg k)) (Real.exp_pos _).le
    have hsumm := summable_sigma_exp r ht0
    have hle := sum_le_hasSum (Finset.Icc 1 M) (fun k _ => hge0 k) hsumm.hasSum
    rw [sigmaMoment]
    refine le_trans (le_of_eq ?_) hle
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [if_neg (by omega : ¬ m = 0)]
  -- combine
  have hmono : (3 * C ^ 2 + 5 * C + 2) *
        ((1 / (n:ℝ) ^ 3) * (∑ m ∈ Finset.Icc 1 M, (m:ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
         + (1 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * (∑ m ∈ Finset.Icc 1 M, (m:ℝ) ^ 3 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
         + (1 / (n:ℝ) ^ 4) * (∑ m ∈ Finset.Icc 1 M, (m:ℝ) ^ 4 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
      ≤ (3 * C ^ 2 + 5 * C + 2) *
        ((1 / (n:ℝ) ^ 3) * sigmaMoment 2 (massLam / Real.sqrt (n:ℝ))
         + (1 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
         + (1 / (n:ℝ) ^ 4) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))) := by
    have hcoef : 0 ≤ 3 * C ^ 2 + 5 * C + 2 := by positivity
    apply mul_le_mul_of_nonneg_left _ hcoef
    gcongr <;> [exact hfin 2; exact hfin 3; exact hfin 4]
  exact le_trans hstep1 (le_trans hmono hKb)

/-- Exp beats poly with a sixth-root exponent: `(n:ℝ)^d · exp(−a·n^{1/6}) ≤ 1/n` eventually. The
analytic engine for both the far-`erdosWeight` tail and the `modelSummand` tail (cutoff `⌊n^{2/3}⌋`,
`t·⌊n^{2/3}⌋ ≍ n^{1/6}`). -/
private lemma poly_mul_exp_neg_sixthRoot_le_inv (a : ℝ) (ha : 0 < a) (d : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n:ℝ) ^ d * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)) ≤ 1 / (n:ℝ) := by
  have htend : Filter.Tendsto
      (fun n : ℕ => (n:ℝ) ^ (d + 1) * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)))
      Filter.atTop (nhds 0) := by
    have hreal : Filter.Tendsto
        (fun x : ℝ => x ^ ((6 * (d + 1) : ℕ) : ℝ) * Real.exp (-a * x))
        Filter.atTop (nhds 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ a ha
    have hroot : Filter.Tendsto (fun n : ℕ => (n:ℝ) ^ (1/6 : ℝ)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    refine (hreal.comp hroot).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hpow : ((n:ℝ) ^ (1/6 : ℝ)) ^ ((6 * (d + 1) : ℕ) : ℝ) = (n:ℝ) ^ (d + 1) := by
      rw [← Real.rpow_mul hn0,
        show (1/6 : ℝ) * ((6 * (d + 1) : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    simp only [Function.comp]
    rw [hpow]
  have h1 : ∀ᶠ n : ℕ in Filter.atTop,
      (n:ℝ) ^ (d + 1) * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)) ≤ 1 :=
    htend.eventually_le_const (by norm_num)
  filter_upwards [h1, Filter.eventually_ge_atTop 1] with n hn1 hn
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hnpos]
  have hrw : (n:ℝ) ^ d * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)) * (n:ℝ)
      = (n:ℝ) ^ (d + 1) * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)) := by ring
  rw [hrw]; exact hn1

/-- Geometric tail-extraction: for `t > 0`, the `m > M` tail of the Lambert summand `m^k σ(m) e^{−tm}`
is bounded by `e^{−(t/2)M}` times the full `(t/2)`-moment. (For `m ≥ M`, `e^{−tm} ≤ e^{−(t/2)M}e^{−(t/2)m}`.) -/
private lemma sigma_geom_tail_le (k : ℕ) {t : ℝ} (ht : 0 < t) (M : ℕ) :
    (∑' m : ℕ, (if m ≤ M then (0:ℝ)
        else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))))
      ≤ Real.exp (-(t/2) * (M:ℝ)) * sigmaMoment k (t/2) := by
  have ht2 : 0 < t/2 := by linarith
  have hg0 := summable_sigma_exp k ht
  have hg2 := summable_sigma_exp k ht2
  set f : ℕ → ℝ := fun m => if m ≤ M then (0:ℝ)
      else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m:ℝ)) with hfdef
  set g'' : ℕ → ℝ := fun m => Real.exp (-(t/2) * (M:ℝ)) *
      (if m = 0 then (0:ℝ) else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(t/2) * (m:ℝ))) with hg''def
  have hfnn : ∀ m, 0 ≤ f m := by
    intro m; rw [hfdef]; dsimp only; split
    · rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
  have hfle0 : ∀ m, f m ≤ (if m = 0 then (0:ℝ)
      else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))) := by
    intro m; rw [hfdef]; dsimp only
    rcases le_or_gt m M with h | h
    · rw [if_pos h]; split
      · rfl
      · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
    · rw [if_neg (not_le.mpr h), if_neg (by omega : ¬ m = 0)]
  have hfsumm : Summable f := Summable.of_nonneg_of_le hfnn hfle0 hg0
  have hg''summ : Summable g'' := hg2.mul_left _
  have hbound : ∀ m, f m ≤ g'' m := by
    intro m; rw [hfdef, hg''def]; dsimp only
    rcases le_or_gt m M with h | h
    · rw [if_pos h]
      apply mul_nonneg (Real.exp_pos _).le
      split
      · rfl
      · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
    · rw [if_neg (not_le.mpr h), if_neg (by omega : ¬ m = 0)]
      have hexp : Real.exp (-t * (m:ℝ))
          ≤ Real.exp (-(t/2) * (M:ℝ)) * Real.exp (-(t/2) * (m:ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hmM : (M:ℝ) ≤ (m:ℝ) := by exact_mod_cast h.le
        nlinarith [hmM, ht]
      calc (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))
          ≤ (m:ℝ) ^ k * Sigma.sigmaR m * (Real.exp (-(t/2) * (M:ℝ)) * Real.exp (-(t/2) * (m:ℝ))) :=
            mul_le_mul_of_nonneg_left hexp
              (mul_nonneg (by positivity) (sigmaR_nonneg m))
        _ = Real.exp (-(t/2) * (M:ℝ)) *
              ((m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(t/2) * (m:ℝ))) := by ring
  calc (∑' m, f m) ≤ ∑' m : ℕ, g'' m := Summable.tsum_le_tsum hbound hfsumm hg''summ
    _ = Real.exp (-(t/2) * (M:ℝ)) *
          ∑' m : ℕ, (if m = 0 then (0:ℝ) else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(t/2) * (m:ℝ))) :=
        tsum_mul_left
    _ = Real.exp (-(t/2) * (M:ℝ)) * sigmaMoment k (t/2) := by rw [sigmaMoment]

/-- Per-`m` majorant of `|modelSummand|`: triangle inequality on the coefficient gives the three
nonnegative Lambert pieces (`k=0,1,2`). -/
private lemma abs_modelSummand_le (n m : ℕ) :
    |modelSummand n m|
      ≤ (1 / (n:ℝ)) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 0 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (1 / (n:ℝ) ^ 2) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 1 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))) := by
  have hCpos : 0 < C := C_pos
  rcases eq_or_ne m 0 with h | h
  · subst h; simp [modelSummand]
  · rw [modelSummand, if_neg h, if_neg h, if_neg h, if_neg h]
    rw [abs_mul, abs_mul, abs_of_nonneg (sigmaR_nonneg m), abs_of_pos (Real.exp_pos _)]
    have hcoef : |1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 - C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))|
        ≤ 1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 + C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ)) := by
      have h1 : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
      have h2 : (0:ℝ) ≤ (m:ℝ) / (n:ℝ) ^ 2 := by positivity
      have h3 : (0:ℝ) ≤ C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ)) := by positivity
      rw [abs_le]; constructor <;> linarith
    calc Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
            |1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 - C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))|
        ≤ Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
            (1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 + C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) :=
          mul_le_mul_of_nonneg_left hcoef
            (mul_nonneg (sigmaR_nonneg m) (Real.exp_pos _).le)
      _ = _ := by ring

/-- Abbreviation: the `m > M` tail of the `k`-th Lambert summand at `t = massLam/√n`. -/
private def gTail (n M k m : ℕ) : ℝ :=
  if m ≤ M then (0:ℝ)
  else (if m = 0 then (0:ℝ) else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))

private lemma gTail_nonneg (n M k m : ℕ) : 0 ≤ gTail n M k m := by
  rw [gTail]; split
  · rfl
  · split
    · rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le

private lemma summable_gTail (n M k : ℕ) {t : ℝ} (ht : massLam / Real.sqrt (n:ℝ) = t) (htp : 0 < t) :
    Summable (fun m => gTail n M k m) := by
  apply Summable.of_nonneg_of_le (gTail_nonneg n M k) (fun m => ?_) (summable_sigma_exp k htp)
  rw [gTail, ← ht]; split
  · split
    · rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
  · exact le_refl _

/-- `gTail` equals the bare-`else` tail used by `sigma_geom_tail_le` (the inner `if m=0` never fires
for `m > M`). -/
private lemma gTail_eq_bare (n M k : ℕ) :
    (∑' m : ℕ, gTail n M k m)
      = ∑' m : ℕ, (if m ≤ M then (0:ℝ)
          else (m:ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))) := by
  apply tsum_congr; intro m
  rw [gTail]
  rcases le_or_gt m M with h | h
  · rw [if_pos h, if_pos h]
  · rw [if_neg (not_le.mpr h), if_neg (not_le.mpr h), if_neg (by omega : ¬ m = 0)]

/-- **Model tail** (§5 brick 5): the `m > ⌊n^{2/3}⌋` tail of `|modelSummand|` is `O(1/n)`. The three
moment tails are exp-small (`sigma_geom_tail_le` + sharp `#119`); the surviving `exp(−(λ/4)n^{1/6})`
beats `1/n` (`poly_mul_exp_neg_sixthRoot_le_inv`). -/
theorem model_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (∑' m : ℕ, (if m ≤ ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ then (0:ℝ) else |modelSummand n m|))
        ≤ K / (n:ℝ) := by
  obtain ⟨K0, hK0nn, hK0⟩ := sigmaMoment_le_power_sharp 0
  obtain ⟨K1, hK1nn, hK1⟩ := sigmaMoment_le_power_sharp 1
  obtain ⟨K2, hK2nn, hK2⟩ := sigmaMoment_le_power_sharp 2
  have hlam0 : 0 < massLam := massLam_pos
  have hCpos : 0 < C := C_pos
  set B : ℝ := 4 * K0 / massLam ^ 2 + 8 * K1 / massLam ^ 3 + 2 * C * K2 / massLam ^ 4 with hBdef
  have hBnn : 0 ≤ B := by
    have t0 : (0:ℝ) ≤ 4 * K0 / massLam ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) hK0nn) (by positivity)
    have t1 : (0:ℝ) ≤ 8 * K1 / massLam ^ 3 :=
      div_nonneg (mul_nonneg (by norm_num) hK1nn) (by positivity)
    have t2 : (0:ℝ) ≤ 2 * C * K2 / massLam ^ 4 :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCpos.le) hK2nn) (by positivity)
    rw [hBdef]; linarith
  refine ⟨B + 1, by linarith, ?_⟩
  filter_upwards [poly_mul_exp_neg_sixthRoot_le_inv (massLam / 4) (by positivity) 0,
    Filter.eventually_ge_atTop (max 8 ⌈massLam ^ 2⌉₊)] with n hpoly hnge
  have hn8 : 8 ≤ n := le_trans (le_max_left _ _) hnge
  have hnlamc : ⌈massLam ^ 2⌉₊ ≤ n := le_trans (le_max_right _ _) hnge
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hnge1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have hs2 : Real.sqrt (n:ℝ) ^ 2 = (n:ℝ) := Real.sq_sqrt hnpos.le
  have hs1 : 1 ≤ Real.sqrt (n:ℝ) := by
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (n:ℝ) := Real.sqrt_le_sqrt hnge1
  have htp : 0 < massLam / Real.sqrt (n:ℝ) := div_pos hlam0 hs0
  have hlamle : massLam ≤ Real.sqrt (n:ℝ) := by
    calc massLam = Real.sqrt (massLam ^ 2) := (Real.sqrt_sq hlam0.le).symm
      _ ≤ Real.sqrt (n:ℝ) := Real.sqrt_le_sqrt (by
          have : (⌈massLam ^ 2⌉₊ : ℝ) ≤ (n:ℝ) := by exact_mod_cast hnlamc
          linarith [Nat.le_ceil (massLam ^ 2)])
  have ht2pos : 0 < massLam / Real.sqrt (n:ℝ) / 2 := by positivity
  have ht2le1 : massLam / Real.sqrt (n:ℝ) / 2 ≤ 1 := by
    rw [div_div, div_le_one (by positivity)]; nlinarith [hlamle, hs1, hlam0]
  set M : ℕ := ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ with hMdef
  -- step 1: model tail ≤ three weighted sigma-tails
  have hsummgT : ∀ k, Summable (fun m => gTail n M k m) := fun k => summable_gTail n M k rfl htp
  have hpt : ∀ m, (if m ≤ M then (0:ℝ) else |modelSummand n m|)
      ≤ (1 / (n:ℝ)) * gTail n M 0 m + (1 / (n:ℝ) ^ 2) * gTail n M 1 m
        + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * gTail n M 2 m := by
    intro m
    rcases le_or_gt m M with h | h
    · rw [if_pos h, gTail, gTail, gTail, if_pos h, if_pos h, if_pos h]; simp
    · rw [if_neg (not_le.mpr h), gTail, gTail, gTail,
        if_neg (not_le.mpr h), if_neg (not_le.mpr h), if_neg (not_le.mpr h)]
      exact abs_modelSummand_le n m
  have h3summ : Summable (fun m => (1 / (n:ℝ)) * gTail n M 0 m + (1 / (n:ℝ) ^ 2) * gTail n M 1 m
      + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * gTail n M 2 m) :=
    (((hsummgT 0).mul_left _).add ((hsummgT 1).mul_left _)).add ((hsummgT 2).mul_left _)
  have hsummF : Summable (fun m => if m ≤ M then (0:ℝ) else |modelSummand n m|) :=
    Summable.of_nonneg_of_le (fun m => by split <;> positivity) hpt h3summ
  have hsplit : (∑' m : ℕ, (if m ≤ M then (0:ℝ) else |modelSummand n m|))
      ≤ (1 / (n:ℝ)) * (∑' m, gTail n M 0 m) + (1 / (n:ℝ) ^ 2) * (∑' m, gTail n M 1 m)
        + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (∑' m, gTail n M 2 m) := by
    calc (∑' m : ℕ, (if m ≤ M then (0:ℝ) else |modelSummand n m|))
        ≤ ∑' m, ((1 / (n:ℝ)) * gTail n M 0 m + (1 / (n:ℝ) ^ 2) * gTail n M 1 m
            + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * gTail n M 2 m) :=
          Summable.tsum_le_tsum hpt hsummF h3summ
      _ = (1 / (n:ℝ)) * (∑' m, gTail n M 0 m) + (1 / (n:ℝ) ^ 2) * (∑' m, gTail n M 1 m)
            + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (∑' m, gTail n M 2 m) := by
          rw [(((hsummgT 0).mul_left _).add ((hsummgT 1).mul_left _)).tsum_add ((hsummgT 2).mul_left _),
            ((hsummgT 0).mul_left _).tsum_add ((hsummgT 1).mul_left _),
            tsum_mul_left, tsum_mul_left, tsum_mul_left]
  -- step 2: each sigma-tail ≤ E · M_k(t/2)
  have hTk : ∀ k, (∑' m, gTail n M k m)
      ≤ Real.exp (-(massLam / Real.sqrt (n:ℝ) / 2) * (M:ℝ)) *
          sigmaMoment k (massLam / Real.sqrt (n:ℝ) / 2) := by
    intro k; rw [gTail_eq_bare]; exact sigma_geom_tail_le k htp M
  -- step 3: bound everything by B · E, then E ≤ exp(−(λ/4) n^{1/6}), then poly.
  have hE : Real.exp (-(massLam / Real.sqrt (n:ℝ) / 2) * (M:ℝ))
      ≤ Real.exp (-(massLam / 4) * (n:ℝ) ^ (1/6 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    -- (λ/4) n^{1/6} ≤ (t/2) M
    have hM_ge : ((M:ℝ)) ≥ (n:ℝ) ^ (2/3 : ℝ) - 1 := by
      have := Nat.lt_floor_add_one ((n:ℝ) ^ (2/3 : ℝ))
      rw [hMdef]; linarith
    have hn23ge2 : (2:ℝ) ≤ (n:ℝ) ^ (2/3 : ℝ) := by
      have hx0 : 0 ≤ (n:ℝ) ^ (2/3 : ℝ) := Real.rpow_nonneg hnpos.le _
      have hcube : ((n:ℝ) ^ (2/3 : ℝ)) ^ 3 = (n:ℝ) ^ 2 := by
        rw [← Real.rpow_natCast ((n:ℝ) ^ (2/3 : ℝ)) 3, ← Real.rpow_mul hnpos.le,
          show (2/3 : ℝ) * ((3:ℕ):ℝ) = ((2:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
      have hge : (64:ℝ) ≤ (n:ℝ) ^ 2 := by
        have h8 : (8:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn8
        nlinarith [h8]
      nlinarith [hcube, hge, hx0, mul_nonneg hx0 hx0, sq_nonneg ((n:ℝ) ^ (2/3 : ℝ) - 2),
        sq_nonneg ((n:ℝ) ^ (2/3 : ℝ) + 1)]
    -- M ≥ (1/2) n^{2/3}
    have hMhalf : (1/2 : ℝ) * (n:ℝ) ^ (2/3 : ℝ) ≤ (M:ℝ) := by nlinarith [hM_ge, hn23ge2]
    -- (t/2)·M = (λ/(2√n))·M ≥ (λ/(2√n))·(1/2)n^{2/3} = (λ/4) n^{1/6}
    have hsqrt_rpow : Real.sqrt (n:ℝ) = (n:ℝ) ^ (1/2 : ℝ) := Real.sqrt_eq_rpow _
    have hsplitpow : (n:ℝ) ^ (2/3 : ℝ) = (n:ℝ) ^ (1/2 : ℝ) * (n:ℝ) ^ (1/6 : ℝ) := by
      rw [← Real.rpow_add hnpos]; norm_num
    have hkey : (massLam / 4) * (n:ℝ) ^ (1/6 : ℝ)
        ≤ massLam / Real.sqrt (n:ℝ) / 2 * (M:ℝ) := by
      rw [hsqrt_rpow]
      have hpos16 : (0:ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) := Real.rpow_nonneg hnpos.le _
      have hpos12 : (0:ℝ) < (n:ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hnpos _
      calc (massLam / 4) * (n:ℝ) ^ (1/6 : ℝ)
          = massLam / (n:ℝ) ^ (1/2 : ℝ) / 2 * ((1/2 : ℝ) * (n:ℝ) ^ (2/3 : ℝ)) := by
            rw [hsplitpow]; field_simp; ring
        _ ≤ massLam / (n:ℝ) ^ (1/2 : ℝ) / 2 * (M:ℝ) := by
            apply mul_le_mul_of_nonneg_left hMhalf (by positivity)
    nlinarith [hkey]
  -- assemble: model tail ≤ B·E ≤ B·exp(−(λ/4)n^{1/6}) ≤ B/n ≤ (B+1)/n
  have hsharp0 := hK0 _ ht2pos ht2le1
  have hsharp1 := hK1 _ ht2pos ht2le1
  have hsharp2 := hK2 _ ht2pos ht2le1
  -- (t/2)-power identities
  have hp2 : (massLam / Real.sqrt (n:ℝ) / 2) ^ 2 = massLam ^ 2 / (4 * (n:ℝ)) := by
    rw [div_div]; field_simp; nlinarith [hs2]
  have hp3 : (massLam / Real.sqrt (n:ℝ) / 2) ^ 3
      = massLam ^ 3 / (8 * (n:ℝ) * Real.sqrt (n:ℝ)) := by
    rw [div_div]; field_simp; nlinarith [hs2]
  have hp4 : (massLam / Real.sqrt (n:ℝ) / 2) ^ 4 = massLam ^ 4 / (16 * (n:ℝ) ^ 2) := by
    rw [div_div]; field_simp; nlinarith [hs2]
  -- final assembly
  have hlamne : massLam ≠ 0 := hlam0.ne'
  have hnne : (n:ℝ) ≠ 0 := hnpos.ne'
  have hsne : Real.sqrt (n:ℝ) ≠ 0 := hs0.ne'
  set E : ℝ := Real.exp (-(massLam / Real.sqrt (n:ℝ) / 2) * (M:ℝ)) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hsqle : Real.sqrt (n:ℝ) ≤ (n:ℝ) := by
    nlinarith [hs2, hs1, mul_nonneg hs0.le (sub_nonneg.mpr hs1)]
  have e0 : (1 / (n:ℝ)) * (∑' m, gTail n M 0 m) ≤ E * (4 * K0 / massLam ^ 2) := by
    calc (1 / (n:ℝ)) * (∑' m, gTail n M 0 m)
        ≤ (1 / (n:ℝ)) * (E * sigmaMoment 0 (massLam / Real.sqrt (n:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (hTk 0) (by positivity)
      _ ≤ (1 / (n:ℝ)) * (E * (K0 / (massLam / Real.sqrt (n:ℝ) / 2) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp0 hEpos.le) (by positivity)
      _ = E * (4 * K0 / massLam ^ 2) := by rw [hp2]; field_simp
  have e1 : (1 / (n:ℝ) ^ 2) * (∑' m, gTail n M 1 m) ≤ E * (8 * K1 / massLam ^ 3) := by
    calc (1 / (n:ℝ) ^ 2) * (∑' m, gTail n M 1 m)
        ≤ (1 / (n:ℝ) ^ 2) * (E * sigmaMoment 1 (massLam / Real.sqrt (n:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (hTk 1) (by positivity)
      _ ≤ (1 / (n:ℝ) ^ 2) * (E * (K1 / (massLam / Real.sqrt (n:ℝ) / 2) ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp1 hEpos.le) (by positivity)
      _ = E * (8 * K1 * Real.sqrt (n:ℝ) / (massLam ^ 3 * (n:ℝ))) := by rw [hp3]; field_simp
      _ ≤ E * (8 * K1 / massLam ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ hEpos.le
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hsqle, hK1nn, hlam0, pow_pos hlam0 3,
            mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hK1nn) (pow_nonneg hlam0.le 3)]
  have e2 : (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (∑' m, gTail n M 2 m)
      ≤ E * (2 * C * K2 / massLam ^ 4) := by
    calc (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (∑' m, gTail n M 2 m)
        ≤ (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) *
            (E * sigmaMoment 2 (massLam / Real.sqrt (n:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (hTk 2) (by positivity)
      _ ≤ (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) *
            (E * (K2 / (massLam / Real.sqrt (n:ℝ) / 2) ^ 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp2 hEpos.le) (by positivity)
      _ = E * (2 * C * K2 / (massLam ^ 4 * Real.sqrt (n:ℝ))) := by rw [hp4]; field_simp; ring
      _ ≤ E * (2 * C * K2 / massLam ^ 4) := by
          apply mul_le_mul_of_nonneg_left _ hEpos.le
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hs1, hK2nn, hlam0, hCpos, pow_pos hlam0 4,
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCpos.le) hK2nn)
              (pow_nonneg hlam0.le 4)]
  calc (∑' m : ℕ, (if m ≤ M then (0:ℝ) else |modelSummand n m|))
      ≤ (1 / (n:ℝ)) * (∑' m, gTail n M 0 m) + (1 / (n:ℝ) ^ 2) * (∑' m, gTail n M 1 m)
        + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (∑' m, gTail n M 2 m) := hsplit
    _ ≤ E * (4 * K0 / massLam ^ 2) + E * (8 * K1 / massLam ^ 3) + E * (2 * C * K2 / massLam ^ 4) := by
        linarith [e0, e1, e2]
    _ = E * B := by rw [hBdef]; ring
    _ ≤ Real.exp (-(massLam / 4) * (n:ℝ) ^ (1/6 : ℝ)) * B :=
        mul_le_mul_of_nonneg_right hE hBnn
    _ ≤ (1 / (n:ℝ)) * B := by
        apply mul_le_mul_of_nonneg_right _ hBnn
        have hp := hpoly; rw [pow_zero, one_mul] at hp; exact hp
    _ = B / (n:ℝ) := by ring
    _ ≤ (B + 1) / (n:ℝ) := by
        have hsplit2 : (B + 1) / (n:ℝ) = B / (n:ℝ) + 1 / (n:ℝ) := by ring
        have h1n : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
        rw [hsplit2]; linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
