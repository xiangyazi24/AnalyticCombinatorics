import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.SummatoryBridge

/-!
# The weighted block squeeze (rehabilitated)

With the index bridge in hand, the model-kernel windowed sum is squeezed between the endpoint
exponentials times the *same* half-open mass — both sides living on `Icc 1 (n−1)`:

  `e^{−(C/2)β}·M_n(α,β) ≤ (1/n)·Σ_{window} σ(m)·e^{−(C/2)m/√n} ≤ e^{−(C/2)α}·M_n(α,β)`,

eventually in `n`, where `M_n(α,β) = (S(β√n) − S(α√n))/n`.  Opus-authored.
-/

noncomputable section

open Filter Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

open AnalyticCombinatorics.Ch8.Partitions.Sigma

/-- Eventually `⌊β√n⌋ ≤ n − 1`. -/
lemma floor_beta_sqrt_le_eventually {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop, ⌊β * Real.sqrt n⌋₊ ≤ n - 1 := by
  have hquad : ∀ᶠ n : ℕ in atTop, (4 * β ^ 2 ≤ (n : ℝ)) ∧ 2 ≤ n := by
    have h1 : ∀ᶠ n : ℕ in atTop, ((⌈4 * β ^ 2⌉₊ : ℕ) ≤ n) := eventually_ge_atTop _
    have h2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
    filter_upwards [h1, h2] with n hn h2n
    refine ⟨?_, h2n⟩
    calc (4 * β ^ 2 : ℝ) ≤ (⌈4 * β ^ 2⌉₊ : ℕ) := Nat.le_ceil _
      _ ≤ (n : ℝ) := by exact_mod_cast hn
  filter_upwards [hquad] with n ⟨hn4, hn2⟩
  -- β√n ≤ n/2 ≤ n−1 for n ≥ 2
  have hnpos : (0 : ℝ) < n := by positivity
  have hs : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hsqrtle : 2 * β ≤ Real.sqrt n := by
    have h2β : (0 : ℝ) ≤ 2 * β := by positivity
    have : (2 * β) ^ 2 ≤ (n : ℝ) := by nlinarith
    calc 2 * β = Real.sqrt ((2 * β) ^ 2) := (Real.sqrt_sq h2β).symm
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt this
  have hhalf : β * Real.sqrt n ≤ (n : ℝ) / 2 := by
    have hs0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    nlinarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
  have hfin : β * Real.sqrt n ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    have h2n' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  calc ⌊β * Real.sqrt n⌋₊ ≤ ⌊((n - 1 : ℕ) : ℝ)⌋₊ := Nat.floor_le_floor hfin
    _ = n - 1 := Nat.floor_natCast _

/-- **The weighted block squeeze**: eventually in `n`, the model-kernel windowed sum lies between
the endpoint exponentials times the half-open mass. -/
theorem weighted_window_block_squeeze {C α β : ℝ} (hC : 0 < C) (hα : 0 ≤ α) (hαβ : α < β) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(C / 2) * β) *
          ((1 / (n : ℝ)) * (summatory (β * Real.sqrt n) - summatory (α * Real.sqrt n)))
        ≤ (1 / (n : ℝ)) *
            ∑ m ∈ Finset.Icc 1 (n - 1),
              (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
               then sigmaR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt n) else 0)
      ∧ (1 / (n : ℝ)) *
            ∑ m ∈ Finset.Icc 1 (n - 1),
              (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
               then sigmaR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt n) else 0)
        ≤ Real.exp (-(C / 2) * α) *
            ((1 / (n : ℝ)) * (summatory (β * Real.sqrt n) - summatory (α * Real.sqrt n))) := by
  have hβ : 0 < β := lt_of_le_of_lt hα hαβ
  filter_upwards
    [floor_beta_sqrt_le_eventually hβ,
     model_exp_endpoint_squeeze (C := C) (α := α) (β := β) hC hαβ.le]
    with n hcap hsq
  have hbridge := summatory_diff_eq_window_sum hα hαβ.le (n := n) hcap
  have hcoef : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  constructor
  · -- lower: e^{−(C/2)β}·mass ≤ windowed sum
    rw [hbridge]
    rw [show Real.exp (-(C / 2) * β) *
          ((1 / (n : ℝ)) * ∑ m ∈ Finset.Icc 1 (n - 1),
            (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
             then sigmaR m else 0))
        = (1 / (n : ℝ)) * ∑ m ∈ Finset.Icc 1 (n - 1),
            Real.exp (-(C / 2) * β) *
              (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
               then sigmaR m else 0) by
          rw [← Finset.mul_sum]; ring]
    refine mul_le_mul_of_nonneg_left ?_ hcoef
    refine Finset.sum_le_sum ?_
    intro m _hm
    by_cases hwin : α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
    · simp only [hwin]
      have hσ : 0 ≤ sigmaR m := sigmaR_nonneg m
      have hexp := (hsq m hwin.1 hwin.2).1
      calc Real.exp (-(C / 2) * β) * sigmaR m
          ≤ Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt n) * sigmaR m :=
            mul_le_mul_of_nonneg_right hexp hσ
        _ = sigmaR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt n) := by ring
    · simp [hwin]
  · -- upper: windowed sum ≤ e^{−(C/2)α}·mass
    rw [hbridge]
    rw [show Real.exp (-(C / 2) * α) *
          ((1 / (n : ℝ)) * ∑ m ∈ Finset.Icc 1 (n - 1),
            (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
             then sigmaR m else 0))
        = (1 / (n : ℝ)) * ∑ m ∈ Finset.Icc 1 (n - 1),
            Real.exp (-(C / 2) * α) *
              (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
               then sigmaR m else 0) by
          rw [← Finset.mul_sum]; ring]
    refine mul_le_mul_of_nonneg_left ?_ hcoef
    refine Finset.sum_le_sum ?_
    intro m _hm
    by_cases hwin : α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
    · simp only [hwin]
      have hσ : 0 ≤ sigmaR m := sigmaR_nonneg m
      have hexp := (hsq m hwin.1 hwin.2).2
      calc sigmaR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt n)
          = Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt n) * sigmaR m := by ring
        _ ≤ Real.exp (-(C / 2) * α) * sigmaR m :=
            mul_le_mul_of_nonneg_right hexp hσ
    · simp [hwin]

end AnalyticCombinatorics.Ch8.Partitions.Erdos.Model
