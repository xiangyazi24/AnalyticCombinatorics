import AnalyticCombinatorics.Ch4.Analytic.LogKTransferNatural
import AnalyticCombinatorics.Ch7.SingularityApp.CycleMarkedPermPairBoth

/-!
# A genuine logᵏ combinatorial application (`~ n^{k-1}/(k-1)!·(log n)ᵏ`)

`cycleMarkedPermLpowClass k := cycleMarkedPermClass.lpow k` — an ordered `k`-tuple of
permutations, each with one distinguished cycle — has EGF

  `(log(1/(1-z))·(1-z)^{-1})^k = log^k(1/(1-z))·(1-z)^{-k} = logKSingularityFun k k`.

Applying the general logᵏ transfer at `α = k`, `C = 1` (zero residual) gives

  `aₙ / n! ~ n^{k-1}/(k-1)!·(log n)ᵏ`   (for `k ≥ 2`),

the first end-to-end use of the general logᵏ singularity hierarchy.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

namespace AnalyticCombinatorics

open AnalyticCombinatorics.Ch1

/-- `logKGF α k = oneSubCpowGF α · logGF^k`. -/
theorem logKGF_eq_oneSubCpow_mul_logPow (α : ℂ) (k : ℕ) :
    logKGF α k = oneSubCpowGF α * logGF ^ k := by
  induction k with
  | zero => simp [logKGF]
  | succ k ih => rw [logKGF, ih, pow_succ, mul_assoc]

/-- `oneSubCpowGF 1 ^ k = oneSubCpowGF k` (`k ≥ 1`). -/
theorem oneSubCpowGF_one_pow {k : ℕ} (hk : 1 ≤ k) :
    oneSubCpowGF (1 : ℂ) ^ k = oneSubCpowGF (k : ℂ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 1 + (m + 1) = (1 + m) + 1 by omega, pow_succ, ih, oneSubCpowGF_add]
    congr 1
    push_cast; ring

/-- Ordered `k`-tuple of marked-cycle permutations. -/
noncomputable def cycleMarkedPermLpowClass (k : ℕ) : CombClass :=
  cycleMarkedPermClass.lpow k

/-- **Master EGF identity**: `mapℂ A.egf = logKGF k k`. -/
theorem mapℂ_cycleMarkedPermLpowClass_egf {k : ℕ} (hk : 1 ≤ k) :
    PowerSeries.mapℂ (cycleMarkedPermLpowClass k).egf = logKGF (k : ℂ) k := by
  rw [cycleMarkedPermLpowClass, CombClass.egf_lpow, map_pow, mapℂ_cycleMarkedPermClass_egf,
    logKGF_eq_oneSubCpow_mul_logPow, mul_pow, oneSubCpowGF_one_pow hk, mul_comm]

/-- **~ n^{k-1}/(k-1)!·(log n)ᵏ** for the marked-cycle permutation `k`-tuple (`k ≥ 2`). -/
theorem cycleMarkedPermLpowClass_counts_div_factorial_isEquivalent {k : ℕ} (hk : 2 ≤ k) :
    (fun n : ℕ => ((cycleMarkedPermLpowClass k).counts n : ℝ) / (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ (k - 1) / ((k - 1).factorial : ℝ) * (Real.log n) ^ k) := by
  set R : ℝ := 2 with hR_def
  set φ : ℝ := Real.pi / 4 with hφ_def
  have hk1 : 1 ≤ k := by omega
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hφ0 : 0 < φ := by rw [hφ_def]; positivity
  have hφ2 : φ < Real.pi / 2 := by rw [hφ_def]; linarith [Real.pi_pos]
  have hφπ : φ < Real.pi := by linarith [Real.pi_pos]
  -- carrier is exactly the model: residual is 0
  have hkcast : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; ring
  have hsing : Tendsto
      (fun z : ℂ => ‖logKSingularityFun ((k : ℝ) : ℂ) k z
          - (1 : ℂ) * logKSingularityFun ((k : ℝ) : ℂ) k z‖ * ‖(1 : ℂ) - z‖ ^ (k : ℝ)
        * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0) := by
    have : (fun z : ℂ => ‖logKSingularityFun ((k : ℝ) : ℂ) k z
        - (1 : ℂ) * logKSingularityFun ((k : ℝ) : ℂ) k z‖ * ‖(1 : ℂ) - z‖ ^ (k : ℝ)
        * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k)⁻¹) = fun _ : ℂ => (0 : ℝ) := by
      funext z; simp
    rw [this]; exact tendsto_const_nhds
  have hfaith : HasFPowerSeriesAt (logKSingularityFun ((k : ℝ) : ℂ) k)
      (PowerSeries.toFMLS (PowerSeries.mapℂ (cycleMarkedPermLpowClass k).egf)) 0 := by
    rw [mapℂ_cycleMarkedPermLpowClass_egf hk1, ← hkcast]
    exact logKSingularityFun_hasFPowerSeriesAt ((k : ℝ) : ℂ) k
  have htransfer := logK_transfer_theorem_natural_remainder
    (α := (k : ℝ)) (C := (1 : ℂ)) (R := R) (φ := φ)
    (f := logKSingularityFun ((k : ℝ) : ℂ) k)
    (p := PowerSeries.toFMLS (PowerSeries.mapℂ (cycleMarkedPermLpowClass k).egf))
    hkR (by norm_num) (by rw [hR_def]; norm_num) hφ0 hφ2 k hk1
    hfaith
    (analyticOnNhd_logKSingularityFun_deltaDomain (α := ((k : ℝ) : ℂ)) k hφ0 hφπ)
    hsing
  have hLHS : (fun n : ℕ =>
        (PowerSeries.toFMLS (PowerSeries.mapℂ (cycleMarkedPermLpowClass k).egf)).coeff n)
      = (fun n : ℕ =>
          (((((cycleMarkedPermLpowClass k).counts n : ℝ) / (n.factorial : ℝ)) : ℝ) : ℂ)) := by
    funext n
    rw [PowerSeries.coeff_toFMLS, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
    push_cast; ring
  have hRHS : (fun n : ℕ => (1 : ℂ) *
        (((n : ℝ) ^ ((k : ℝ) - 1) / Real.Gamma (k : ℝ) * (Real.log n) ^ k : ℝ) : ℂ))
      = (fun n : ℕ =>
          (((n : ℝ) ^ (k - 1) / ((k - 1).factorial : ℝ) * (Real.log n) ^ k : ℝ) : ℂ)) := by
    funext n
    have hΓ : Real.Gamma (k : ℝ) = ((k - 1).factorial : ℝ) := by
      have hkk : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
        have : k - 1 + 1 = k := by omega
        rw [← this]; push_cast; ring
      rw [hkk, Real.Gamma_nat_eq_factorial]
    have hpow : ((n : ℝ) ^ ((k : ℝ) - 1)) = (n : ℝ) ^ (k - 1) := by
      have hkk : ((k : ℝ) - 1) = (((k - 1 : ℕ)) : ℝ) := by
        have : k - 1 + 1 = k := by omega
        rw [show ((k : ℝ) - 1) = ((k : ℝ)) - 1 from rfl]
        rw [show (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 by
          rw [← this]; push_cast; ring]
      rw [hkk, Real.rpow_natCast]
    rw [hΓ, hpow, one_mul]
  rw [hLHS, hRHS] at htransfer
  exact ofReal_isEquivalent_iff.mp htransfer

end AnalyticCombinatorics
