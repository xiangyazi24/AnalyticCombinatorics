import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics
import AnalyticCombinatorics.Ch4.Analytic.Derangements
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Growth-rate corollaries of exact asymptotics

This file records API-level growth-rate consequences derived from the existing
asymptotic-equivalent headlines.
-/

open Filter Asymptotics
open scoped Topology BigOperators

theorem centralBinom_isTheta :
    (fun n : ℕ => (n.centralBinom : ℝ)) =Θ[atTop]
      (fun n : ℕ => (4 : ℝ)^n / Real.sqrt (Real.pi * (n : ℝ))) := by
  exact centralBinom_isEquivalent_real_sqrt.isTheta

theorem catalan_isTheta :
    (fun n : ℕ => (catalan n : ℝ)) =Θ[atTop]
      (fun n : ℕ =>
        (4 : ℝ)^n / (Real.sqrt Real.pi * (n : ℝ)^(3 / 2 : ℝ))) := by
  exact catalan_isEquivalent_real_rpow.isTheta

theorem fib_isTheta :
    (fun n : ℕ => (Nat.fib (n + 1) : ℝ)) =Θ[atTop]
      (fun n : ℕ =>
        (Real.goldenRatio / (Real.goldenRatio - Real.goldenConj)) * Real.goldenRatio ^ n) := by
  exact fib_isEquivalent_real.isTheta

theorem numDerangements_isTheta :
    (fun n : ℕ => (numDerangements n : ℝ)) =Θ[atTop]
      (fun n : ℕ => (n.factorial : ℝ) * Real.exp (-1)) := by
  exact numDerangements_isEquivalent.isTheta

theorem centralBinom_isBigO :
    (fun n : ℕ => (n.centralBinom : ℝ)) =O[atTop]
      (fun n : ℕ => (4 : ℝ)^n / Real.sqrt (Real.pi * (n : ℝ))) := by
  exact centralBinom_isEquivalent_real_sqrt.isBigO

theorem catalan_isBigO :
    (fun n : ℕ => (catalan n : ℝ)) =O[atTop]
      (fun n : ℕ =>
        (4 : ℝ)^n / (Real.sqrt Real.pi * (n : ℝ)^(3 / 2 : ℝ))) := by
  exact catalan_isEquivalent_real_rpow.isBigO

theorem fib_isBigO :
    (fun n : ℕ => (Nat.fib (n + 1) : ℝ)) =O[atTop]
      (fun n : ℕ =>
        (Real.goldenRatio / (Real.goldenRatio - Real.goldenConj)) * Real.goldenRatio ^ n) := by
  exact fib_isEquivalent_real.isBigO

theorem numDerangements_isBigO :
    (fun n : ℕ => (numDerangements n : ℝ)) =O[atTop]
      (fun n : ℕ => (n.factorial : ℝ) * Real.exp (-1)) := by
  exact numDerangements_isEquivalent.isBigO

theorem centralBinom_ratio_tendsto :
    Tendsto (fun n : ℕ => (n.centralBinom : ℝ) * Real.sqrt (n : ℝ) / (4 : ℝ)^n)
      atTop (𝓝 (1 / Real.sqrt Real.pi)) := by
  have htarget :
      ∀ᶠ n : ℕ in atTop,
        (4 : ℝ)^n / Real.sqrt (Real.pi * (n : ℝ)) ≠ 0 := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hpow : (4 : ℝ)^n ≠ 0 := pow_ne_zero n (by norm_num)
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mp hn)
    have hsqrt : Real.sqrt (Real.pi * (n : ℝ)) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos_of_pos (mul_pos Real.pi_pos hnpos))
    exact div_ne_zero hpow hsqrt
  have hratio :
      Tendsto
        (((fun n : ℕ => (n.centralBinom : ℝ)) /
          (fun n : ℕ => (4 : ℝ)^n / Real.sqrt (Real.pi * (n : ℝ)))) /
            fun _ : ℕ => Real.sqrt Real.pi)
        atTop (𝓝 (1 / Real.sqrt Real.pi)) := by
    simpa using
      ((isEquivalent_iff_tendsto_one htarget).mp
        centralBinom_isEquivalent_real_sqrt).div_const (Real.sqrt Real.pi)
  refine Tendsto.congr' ?_ hratio
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hpow : (4 : ℝ)^n ≠ 0 := pow_ne_zero n (by norm_num)
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mp hn)
  have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos_of_pos hnpos)
  have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos_of_pos Real.pi_pos)
  have hsqrtpin : Real.sqrt (Real.pi * (n : ℝ)) =
      Real.sqrt Real.pi * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (le_of_lt Real.pi_pos)]
  dsimp
  rw [hsqrtpin]
  field_simp [hpow, hsqrtn, hsqrtpi]

-- The derangement ratio limit is already named `derangement_prob_tendsto`
-- in `Derangements.lean` and is re-exported by this import-only API file.
