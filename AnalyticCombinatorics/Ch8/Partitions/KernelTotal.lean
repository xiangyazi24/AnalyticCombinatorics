import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MeshEstimate
import AnalyticCombinatorics.Ch8.Partitions.KernelWindow
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernelClose
import AnalyticCombinatorics.Ch8.Partitions.ErdosIntegral

/-!
# The Erdős kernel total-mass limit

`Σ_{m=1}^{n-1} erdosWeight n m → 1`.

Assembly: the window piece `(0, R√n]` tends to `∫_0^R (π²/6) y e^{−(C/2)y} dy`
(`erdos_kernel_window`), the tail `m ≥ R√n` is eventually `≤ ε` (`erdos_kernel_tail`,
monotone in `R`), and `∫_0^R → ∫_0^∞ = 1` as `R → ∞` (`kernel_density_integral_one` +
`intervalIntegral_tendsto_integral_Ioi`).  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

/-- The kernel density is integrable on `(0,∞)`. -/
private lemma density_integrableOn :
    IntegrableOn (fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y))
      (Set.Ioi (0 : ℝ)) := by
  have hr : (0 : ℝ) < C / 2 := by
    have := C_pos
    positivity
  -- t ↦ t^1 · e^{−(C/2)t} is integrable on (0,∞) (Gamma-type integrand)
  have h1 : IntegrableOn (fun y : ℝ => y ^ (1 : ℝ) * Real.exp (-(C / 2) * y))
      (Set.Ioi (0 : ℝ)) := by
    have h2 : IntegrableOn (fun y : ℝ => y ^ (1 : ℝ) * Real.exp (-(C / 2 * y)))
        (Set.Ioi (0 : ℝ)) := by
      have := Real.integrable_rpow_mul_exp_neg_mul_Ioi (a := 1) hr (by norm_num)
      simpa using this
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro y _hy
    ring_nf
  refine (h1.const_mul (Real.pi ^ 2 / 6)).congr_fun ?_ measurableSet_Ioi
  intro y hy
  rw [Real.rpow_one]
  ring

/-- `∫_0^R (π²/6) y e^{−(C/2)y} dy → 1` as `R → ∞`. -/
private lemma modelIntegral_tendsto_one :
    Tendsto (fun R : ℝ => modelIntegral C 0 R) atTop (𝓝 1) := by
  have hval :
      (∫ y : ℝ in Set.Ioi (0 : ℝ),
        (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y)) = 1 := by
    have h := kernel_density_integral_one
    rw [← h, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro y _hy
    ring_nf
  have htend :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
      density_integrableOn tendsto_id
  rw [hval] at htend
  exact htend

/-- Tail monotonicity in the cut: larger cut ⇒ smaller tail. -/
private lemma kernel_tail_mono {R R' : ℝ} (hRR' : R ≤ R') (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if R' * Real.sqrt (n : ℝ) ≤ (m : ℝ) then erdosWeight n m else 0)
      ≤
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if R * Real.sqrt (n : ℝ) ≤ (m : ℝ) then erdosWeight n m else 0) := by
  classical
  refine Finset.sum_le_sum ?_
  intro m hm
  have hw : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
  by_cases h' : R' * Real.sqrt (n : ℝ) ≤ (m : ℝ)
  · have h : R * Real.sqrt (n : ℝ) ≤ (m : ℝ) := by
      have hs : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      have := mul_le_mul_of_nonneg_right hRR' hs
      linarith
    rw [if_pos h', if_pos h]
  · rw [if_neg h']
    by_cases h : R * Real.sqrt (n : ℝ) ≤ (m : ℝ)
    · rw [if_pos h]; exact hw
    · rw [if_neg h]

/-- The total is sandwiched: `window(0,R) ≤ total ≤ window(0,R) + tail(R)`. -/
private lemma total_window_tail_sandwich (R : ℝ) (hR : 0 < R) (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
      (if (0 : ℝ) * Real.sqrt (n : ℝ) < (m : ℝ) ∧
          (m : ℝ) ≤ R * Real.sqrt (n : ℝ)
       then erdosWeight n m else 0))
      ≤ (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m)
    ∧ (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m)
      ≤ (∑ m ∈ Finset.Icc 1 (n - 1),
          (if (0 : ℝ) * Real.sqrt (n : ℝ) < (m : ℝ) ∧
              (m : ℝ) ≤ R * Real.sqrt (n : ℝ)
           then erdosWeight n m else 0)) +
        (∑ m ∈ Finset.Icc 1 (n - 1),
          if R * Real.sqrt (n : ℝ) ≤ (m : ℝ) then erdosWeight n m else 0) := by
  classical
  constructor
  · refine Finset.sum_le_sum ?_
    intro m hm
    have hw : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
    by_cases h : (0 : ℝ) * Real.sqrt (n : ℝ) < (m : ℝ) ∧
        (m : ℝ) ≤ R * Real.sqrt (n : ℝ)
    · rw [if_pos h]
    · rw [if_neg h]; exact hw
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro m hm
    have hw : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmpos : (0 : ℝ) * Real.sqrt (n : ℝ) < (m : ℝ) := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      simpa using this
    by_cases h : (m : ℝ) ≤ R * Real.sqrt (n : ℝ)
    · -- window term picks it up
      have hwin : (0 : ℝ) * Real.sqrt (n : ℝ) < (m : ℝ) ∧
          (m : ℝ) ≤ R * Real.sqrt (n : ℝ) := ⟨hmpos, h⟩
      rw [if_pos hwin]
      have : (0 : ℝ) ≤ (if R * Real.sqrt (n : ℝ) ≤ (m : ℝ)
          then erdosWeight n m else 0) := by
        by_cases ht : R * Real.sqrt (n : ℝ) ≤ (m : ℝ)
        · rw [if_pos ht]; exact hw
        · rw [if_neg ht]
      linarith
    · -- tail term picks it up
      have ht : R * Real.sqrt (n : ℝ) ≤ (m : ℝ) := (not_le.mp h).le
      rw [if_pos ht]
      have : (0 : ℝ) ≤ (if (0 : ℝ) * Real.sqrt (n : ℝ) < (m : ℝ) ∧
          (m : ℝ) ≤ R * Real.sqrt (n : ℝ) then erdosWeight n m else 0) := by
        by_cases hwin : (0 : ℝ) * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ R * Real.sqrt (n : ℝ)
        · rw [if_pos hwin]; exact hw
        · rw [if_neg hwin]
      linarith

/--
**The Erdős kernel total-mass limit** (HR Stage I.3 capstone):

  `Σ_{m=1}^{n-1} erdosWeight n m → 1`.
-/
theorem erdos_kernel_total :
    Tendsto (fun n : ℕ => ∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m)
      atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε6 : 0 < ε / 6 := by linarith
  -- tail cut R₁ with eventual tail ≤ ε/6
  obtain ⟨R₁, hR₁pos, htail₁⟩ := Close.erdos_kernel_tail (ε / 6) hε6
  -- integral cut: eventually in R, |∫_0^R − 1| < ε/6
  have hint := modelIntegral_tendsto_one
  rw [Metric.tendsto_atTop] at hint
  obtain ⟨R₀, hR₀⟩ := hint (ε / 6) hε6
  -- combined cut
  set R : ℝ := max R₁ (max R₀ 1) with hRdef
  have hRpos : 0 < R := by
    have : (1 : ℝ) ≤ max R₀ 1 := le_max_right _ _
    have h2 : max R₀ 1 ≤ R := le_max_right _ _
    linarith
  have hR_ge_R₁ : R₁ ≤ R := le_max_left _ _
  have hR_ge_R₀ : R₀ ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hint_R : |modelIntegral C 0 R - 1| < ε / 6 := by
    have := hR₀ R hR_ge_R₀
    rwa [Real.dist_eq] at this
  -- window convergence at cut R
  have hwin := erdos_kernel_window (a := 0) (b := R) le_rfl hRpos
  rw [Metric.tendsto_atTop] at hwin
  obtain ⟨N₁, hN₁⟩ := hwin (ε / 6) hε6
  -- eventual tail bound at the combined cut
  have htail : ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 (n - 1),
        if R * Real.sqrt (n : ℝ) ≤ (m : ℝ) then erdosWeight n m else 0)
        ≤ ε / 6 := by
    filter_upwards [htail₁] with n hn
    exact le_trans (kernel_tail_mono hR_ge_R₁ n) hn
  rw [eventually_atTop] at htail
  obtain ⟨N₂, hN₂⟩ := htail
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hnN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hwin_n := hN₁ n hnN₁
  rw [Real.dist_eq] at hwin_n
  have htail_n := hN₂ n hnN₂
  obtain ⟨hlow, hhigh⟩ := total_window_tail_sandwich R hRpos n
  rw [Real.dist_eq]
  have habs₁ := abs_lt.mp hwin_n
  have habs₂ := abs_lt.mp hint_R
  rw [abs_lt]
  constructor
  · -- 1 − ε < total: total ≥ window > ∫_0^R − ε/6 > 1 − ε/6 − ε/6
    have h1 := habs₁.1
    have h2 := habs₂.1
    linarith
  · -- total < 1 + ε: total ≤ window + tail < ∫_0^R + ε/6 + ε/6 < 1 + 3ε/6
    have h1 := habs₁.2
    have h2 := habs₂.2
    linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos.Model
