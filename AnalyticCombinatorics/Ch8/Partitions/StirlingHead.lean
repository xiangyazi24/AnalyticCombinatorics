import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.TrapezoidEM

/-!
# Singular head via Stirling (HR constant, brick 2)

The `2π` of the partition prefactor comes from Mathlib's Stirling theorem here.
`singularHead t = ∑_{k=1}^{N t} -log(t·k) = -N log t - log N!`, and
`log N! = N log N - N + ½log(2πN) + o(1)` (from `Stirling.log_stirlingSeq_formula`
+ `tendsto_stirlingSeq_sqrt_pi`). With `R t = N t · t → 1`, this gives

  `singularHead t - [(R - R log R)/t + ½log(t/2π)] → 0`.   (ChatGPT R7)
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators Real
open scoped Topology BigOperators

noncomputable section

/-- `R(t) = ⌊1/t⌋·t → 1` as `t → 0⁺`. -/
lemma trapR_tendsto_one : Tendsto trapR (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h : ∀ᶠ t in 𝓝[>] (0 : ℝ), |trapR t - 1| ≤ t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have hle : ((trapN t : ℝ)) ≤ 1 / t := Nat.floor_le (by positivity)
    have hgt : 1 / t < (trapN t : ℝ) + 1 := Nat.lt_floor_add_one (1 / t)
    have hRle : trapR t ≤ 1 := by
      rw [trapR]
      calc ((trapN t : ℝ)) * t ≤ (1 / t) * t := mul_le_mul_of_nonneg_right hle htpos.le
        _ = 1 := by field_simp
    have hRgt : 1 - t ≤ trapR t := by
      rw [trapR]
      have hlt : (1 / t - 1) * t < ((trapN t : ℝ)) * t :=
        mul_lt_mul_of_pos_right (by linarith) htpos
      have heq : (1 / t - 1) * t = 1 - t := by field_simp
      linarith [heq ▸ hlt]
    rw [abs_le]; constructor <;> linarith
  have hsq : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hzero : Tendsto (fun t => trapR t - 1) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero_norm' (by filter_upwards [h] with t ht; rwa [Real.norm_eq_abs]) hsq
  simpa using hzero.add_const 1

/-- `N(t) = ⌊1/t⌋ → ∞` as `t → 0⁺`. -/
lemma trapN_tendsto_atTop : Tendsto trapN (𝓝[>] (0 : ℝ)) atTop := by
  have hinv : Tendsto (fun t : ℝ => 1 / t) (𝓝[>] (0 : ℝ)) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero
  exact tendsto_nat_floor_atTop.comp hinv

/-- `∑_{k=1}^N log k = log N!`. -/
lemma sum_log_nat_Icc_eq_log_factorial :
    ∀ N : ℕ, (∑ k ∈ Finset.Icc 1 N, Real.log (k : ℝ)) = Real.log (Nat.factorial N : ℝ) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ]
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      push_cast; ring

/-- `singularHead t = ∑_{k=1}^{N t} -log(t·k)`. -/
noncomputable def singularHead (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (trapN t), -Real.log (t * (k : ℝ))

/-- `singularHead t = -(N log t) - log N!` for `t > 0`. -/
lemma singularHead_eq_factorial {t : ℝ} (ht : 0 < t) :
    singularHead t = -((trapN t : ℝ) * Real.log t) - Real.log ((trapN t).factorial : ℝ) := by
  unfold singularHead
  have hterm : ∀ k ∈ Finset.Icc 1 (trapN t),
      -Real.log (t * (k : ℝ)) = -Real.log t - Real.log (k : ℝ) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [Real.log_mul (by positivity) (by positivity)]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
    sum_log_nat_Icc_eq_log_factorial, Nat.card_Icc]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul]
  ring

/-- `singularHeadMain t = (R - R log R)/t + ½log(t/2π)`. -/
noncomputable def singularHeadMain (t : ℝ) : ℝ :=
  (trapR t - trapR t * Real.log (trapR t)) / t + (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))

/-- log-factorial Stirling asymptotic along `N(t)`:
`log N! - (N log N - N + ½log(2πN)) → 0`. -/
lemma log_factorial_stirling_along_trapN :
    Tendsto
      (fun t : ℝ =>
        Real.log ((trapN t).factorial : ℝ)
          - ((trapN t : ℝ) * Real.log (trapN t : ℝ) - (trapN t : ℝ)
              + (1 / 2 : ℝ) * Real.log (2 * Real.pi * (trapN t : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- Reduce to log (stirlingSeq (trapN t)) - ½ log π → 0.
  have hstir : Tendsto (fun t : ℝ => Real.log (Stirling.stirlingSeq (trapN t)))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    have hc : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
        (𝓝 (Real.log (Real.sqrt Real.pi))) :=
      (Real.continuousAt_log (by positivity)).tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi
    exact hc.comp trapN_tendsto_atTop
  have hlogpi : Real.log (Real.sqrt Real.pi) = (1 / 2 : ℝ) * Real.log Real.pi := by
    rw [Real.log_sqrt Real.pi_pos.le]; ring
  -- Eventually (trapN t ≥ 1) the algebra holds.
  have heventic : ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 ≤ trapN t :=
    trapN_tendsto_atTop.eventually_ge_atTop 1
  have hcongr : (fun t : ℝ =>
        Real.log ((trapN t).factorial : ℝ)
          - ((trapN t : ℝ) * Real.log (trapN t : ℝ) - (trapN t : ℝ)
              + (1 / 2 : ℝ) * Real.log (2 * Real.pi * (trapN t : ℝ))))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => Real.log (Stirling.stirlingSeq (trapN t)) - (1 / 2 : ℝ) * Real.log Real.pi) := by
    filter_upwards [heventic] with t ht
    have hN : (1 : ℝ) ≤ (trapN t : ℝ) := by exact_mod_cast ht
    have hNpos : (0 : ℝ) < (trapN t : ℝ) := by linarith
    have hform := Stirling.log_stirlingSeq_formula (trapN t)
    -- log N! = log(stirlingSeq N) + ½ log(2N) + N log(N/e)
    rw [Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp] at hform
    have h2N : Real.log (2 * (trapN t : ℝ)) = Real.log 2 + Real.log (trapN t : ℝ) :=
      Real.log_mul (by norm_num) hNpos.ne'
    have h2piN : Real.log (2 * Real.pi * (trapN t : ℝ))
        = Real.log 2 + Real.log Real.pi + Real.log (trapN t : ℝ) := by
      rw [Real.log_mul (by positivity) hNpos.ne', Real.log_mul (by norm_num) Real.pi_pos.ne']
    rw [h2N] at hform
    rw [h2piN]
    -- hform: log(stirlingSeq N) = log N! - ½(log2+logN) - N(logN - 1)
    nlinarith [hform]
  rw [Filter.tendsto_congr' hcongr]
  have := hstir
  rw [hlogpi] at this
  simpa using this.sub_const ((1 / 2 : ℝ) * Real.log Real.pi)

/-- **Singular head Stirling asymptotic** (the `2π` source):
`singularHead − singularHeadMain = −D − ½ log R → 0` (D from `log_factorial_stirling`,
`R → 1`). -/
theorem singularHead_stirling :
    Tendsto (fun t : ℝ => singularHead t - singularHeadMain t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hD := log_factorial_stirling_along_trapN
  have hR : Tendsto (fun t => Real.log (trapR t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp trapR_tendsto_one
    simpa using this
  have hcomb : Tendsto
      (fun t =>
        -(Real.log ((trapN t).factorial : ℝ)
            - ((trapN t : ℝ) * Real.log (trapN t : ℝ) - (trapN t : ℝ)
                + (1 / 2 : ℝ) * Real.log (2 * Real.pi * (trapN t : ℝ))))
          - (1 / 2 : ℝ) * Real.log (trapR t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (hD.neg).sub (hR.const_mul (1 / 2 : ℝ))
    simpa using h
  refine hcomb.congr' ?_
  have heventic : ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 ≤ trapN t :=
    trapN_tendsto_atTop.eventually_ge_atTop 1
  filter_upwards [self_mem_nhdsWithin, heventic] with t ht htN
  have htpos : 0 < t := ht
  have hNpos : (0 : ℝ) < (trapN t : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_pos htN
  rw [singularHead_eq_factorial htpos, singularHeadMain, trapR,
    Real.log_mul hNpos.ne' htpos.ne',
    Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hNpos.ne',
    Real.log_div htpos.ne' (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
  field_simp
  ring

end

end AnalyticCombinatorics.Ch8.Partitions
