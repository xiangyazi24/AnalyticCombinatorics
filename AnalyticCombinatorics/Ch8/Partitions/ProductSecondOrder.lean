import AnalyticCombinatorics.Ch8.Partitions.Log1mexpTailTrapezoid
import AnalyticCombinatorics.Ch8.Partitions.Log1mexpIoiIntegral
import AnalyticCombinatorics.Ch8.Partitions.LaplaceLimit

/-!
# Second-order Laplace asymptotic for the partition generating function (HR brick 2)

Assembles the head asymptotic (`log1mexp_head_asymp`) and the tail asymptotic
(`log1mexp_tail_trapezoid`) into the Meinardus second-order law

`log P(e^{-t}) = (1/t)·I + ½·log(2π/t) + o(1)`,  `I = ∫₀^∞ -log(1-e^{-x}) dx`,

i.e. `log P(e^{-t}) − (1/t)·I − ½·log(t/2π) → 0` as `t → 0⁺`, where
`P(e^{-t}) = PartLaplace t = ∑ p(n) e^{-tn}` and `log1mexp x = -log(1-e^{-x})`.

The key splice: `log P = headLog1mexp + tail` (finite head + infinite tail of the
Euler-log series), `∫₀ᴿ + ∫_R^∞ = ∫₀^∞`, and the head/tail boundary regularizers
cancel up to `−½ log R` with `R = trapR t → 1`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open scoped Topology BigOperators Interval

noncomputable section

/-- `log P(e^{-t})` splits as the finite head sum plus the infinite tail samples. -/
lemma log_partLaplace_eq_head_add_tail {t : ℝ} (ht : 0 < t) :
    headLog1mexp t + (∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
      = Real.log (PartLaplace t) := by
  set N := trapN t with hN
  -- (1) `log P = ∑' n:ℕ, log1mexp (t·(n+1))`
  have hL2 : Real.log (PartLaplace t) = ∑' n : ℕ, log1mexp (t * ((n + 1 : ℕ) : ℝ)) := by
    have h1 : Real.log (PartLaplace t) = ∑' k : ℕ+, log1mexp (t * (k : ℝ)) := by
      rw [log_partLaplace_eq ht]
      apply tsum_congr; intro k
      rw [log1mexp]
    rw [h1, tsum_pnat_eq_tsum_succ (f := fun m : ℕ => log1mexp (t * (m : ℝ)))]
  -- (2) summability of the full series
  have hsumm : Summable (fun n : ℕ => log1mexp (t * ((n + 1 : ℕ) : ℝ))) := by
    obtain ⟨M, hM⟩ : ∃ M : ℕ, Real.log 2 ≤ (M : ℝ) * t := by
      obtain ⟨M, hMge⟩ := exists_nat_ge (Real.log 2 / t)
      exact ⟨M, (div_le_iff₀ ht).mp hMge⟩
    have htailM : Summable (fun n : ℕ => log1mexp ((M : ℝ) * t + t * ((n + 1 : ℕ) : ℝ))) :=
      summable_log1mexp_tail_samples hM ht
    have hcongr :
        (fun n : ℕ => log1mexp (t * (((n + M) + 1 : ℕ) : ℝ)))
          = (fun n : ℕ => log1mexp ((M : ℝ) * t + t * ((n + 1 : ℕ) : ℝ))) := by
      funext n; congr 1; push_cast; ring
    have hshift : Summable (fun n : ℕ => log1mexp (t * (((n + M) + 1 : ℕ) : ℝ))) := by
      rw [hcongr]; exact htailM
    exact (summable_nat_add_iff (f := fun m : ℕ => log1mexp (t * ((m + 1 : ℕ) : ℝ))) M).mp hshift
  -- (3) finite/infinite split of the tsum
  have hsplit := hsumm.sum_add_tsum_nat_add N
  -- (4) head reindex: `∑_{i<N} log1mexp(t·(i+1)) = headLog1mexp t`
  have hhead :
      (∑ i ∈ Finset.range N, log1mexp (t * ((i + 1 : ℕ) : ℝ))) = headLog1mexp t := by
    unfold headLog1mexp
    have hIccIco : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
      ext x; simp [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
    rw [← hN, hIccIco, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
    congr 2
    push_cast; ring
  -- (5) tail reindex: `∑' i, log1mexp(t·(i+N+1)) = tail samples`
  have htail :
      (∑' i : ℕ, log1mexp (t * (((i + N) + 1 : ℕ) : ℝ)))
        = ∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t) := by
    apply tsum_congr; intro i
    rw [mul_comm, ← hN]
    congr 2
    push_cast; ring
  rw [hhead, htail] at hsplit
  rw [hsplit, ← hL2]

/-- **Second-order Laplace asymptotic, with-`I` form.**
`log P(e^{-t}) − (1/t)·∫₀^∞ log1mexp − ½·log(t/2π) → 0` as `t → 0⁺`. -/
theorem log_partLaplace_second_order_with_I :
    Tendsto
      (fun t : ℝ =>
        Real.log (PartLaplace t)
          - (1 / t) * (∫ x in Set.Ioi (0 : ℝ), log1mexp x)
          - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- head + tail asymptotics, summed
  have hsum :
      Tendsto
        (fun t : ℝ =>
          (headLog1mexp t
            - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), log1mexp x)
            - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))
            - (1 / 2 : ℝ) * log1mexpReg (trapR t))
          + ((∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
            - (1 / t) * (∫ x in Set.Ioi (trapR t), log1mexp x)
            + (1 / 2 : ℝ) * log1mexp (trapR t)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [add_zero] using log1mexp_head_asymp.add log1mexp_tail_trapezoid
  -- this sum equals `G(t) − ½ log(trapR t)` for `t > 0`
  have heq :
      (fun t : ℝ =>
        (headLog1mexp t
          - (1 / t) * (∫ x in (0 : ℝ)..(trapR t), log1mexp x)
          - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))
          - (1 / 2 : ℝ) * log1mexpReg (trapR t))
        + ((∑' j : ℕ, log1mexp (((trapN t + 1 + j : ℕ) : ℝ) * t))
          - (1 / t) * (∫ x in Set.Ioi (trapR t), log1mexp x)
          + (1 / 2 : ℝ) * log1mexp (trapR t)))
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ =>
        (Real.log (PartLaplace t)
          - (1 / t) * (∫ x in Set.Ioi (0 : ℝ), log1mexp x)
          - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
        - (1 / 2 : ℝ) * Real.log (trapR t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have hR0 : (0 : ℝ) ≤ trapR t := by rw [trapR]; positivity
    have hstart := log_partLaplace_eq_head_add_tail htpos
    have hint :
        (1 / t) * (∫ x in (0 : ℝ)..(trapR t), log1mexp x)
          + (1 / t) * (∫ x in Set.Ioi (trapR t), log1mexp x)
          = (1 / t) * (∫ x in Set.Ioi (0 : ℝ), log1mexp x) := by
      rw [← mul_add, log1mexp_integral_split hR0]
    simp only [log1mexpReg]
    linarith [hstart, hint]
  have hGwith :
      Tendsto
        (fun t : ℝ =>
          (Real.log (PartLaplace t)
            - (1 / t) * (∫ x in Set.Ioi (0 : ℝ), log1mexp x)
            - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
          - (1 / 2 : ℝ) * Real.log (trapR t))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := hsum.congr' heq
  -- `½ log(trapR t) → 0` since `trapR → 1`
  have hlogR : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * Real.log (trapR t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => Real.log (trapR t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp trapR_tendsto_one
      simpa using this
    simpa using hc.const_mul (1 / 2 : ℝ)
  -- add back the boundary term
  have hadd := hGwith.add hlogR
  simp only [add_zero] at hadd
  refine hadd.congr' (Eventually.of_forall fun t => ?_)
  ring

/-- The Laplace integral constant equals the first-order constant: `∫₀^∞ log1mexp = A`.
Proof: `t·log P → I` (from the second-order law) and `t·log P → A`
(`partition_laplace_log_asymptotic`); limits are unique. -/
theorem log1mexp_integral_eq_A :
    (∫ x in Set.Ioi (0 : ℝ), log1mexp x) = A := by
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  -- `t·φ(t) → 0` where `φ` is the second-order remainder
  have htphi := ht0.mul log_partLaplace_second_order_with_I
  rw [mul_zero] at htphi
  -- `t·½log(t/2π) → 0`
  have htlog :
      Tendsto (fun t : ℝ => t * ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hxlogx : Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) (by norm_num : (0 : ℝ) < 1)
      simp only [Real.rpow_one] at h
      exact h.congr (fun x => mul_comm _ _)
    have hconst : Tendsto (fun t : ℝ => t * Real.log (2 * Real.pi)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using ht0.mul_const (Real.log (2 * Real.pi))
    have hcombo :
        Tendsto (fun t : ℝ => (1 / 2 : ℝ) * (t * Real.log t - t * Real.log (2 * Real.pi)))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (hxlogx.sub hconst).const_mul (1 / 2 : ℝ)
    refine hcombo.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    rw [Real.log_div (ne_of_gt htpos) (by positivity)]
    ring
  -- assemble `t·log P → I`
  have hL :
      Tendsto (fun t : ℝ => t * Real.log (PartLaplace t)) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ x in Set.Ioi (0 : ℝ), log1mexp x)) := by
    have hcomb :=
      (htphi.add (tendsto_const_nhds
        (x := (∫ x in Set.Ioi (0 : ℝ), log1mexp x)))).add htlog
    simp only [zero_add, add_zero] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := ne_of_gt ht
    field_simp
    ring
  exact tendsto_nhds_unique hL partition_laplace_log_asymptotic

/-- **Second-order Laplace asymptotic (Meinardus main term), final form.**
`log P(e^{-t}) − A/t − ½·log(t/2π) → 0` as `t → 0⁺`, with `A = π²/6`. -/
theorem log_partLaplace_second_order :
    Tendsto
      (fun t : ℝ =>
        Real.log (PartLaplace t)
          - (1 / t) * A
          - (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := log_partLaplace_second_order_with_I
  rw [log1mexp_integral_eq_A] at h
  exact h

end

end AnalyticCombinatorics.Ch8.Partitions
