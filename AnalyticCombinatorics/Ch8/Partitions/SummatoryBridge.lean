import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.SummatoryWindow
import AnalyticCombinatorics.Ch8.Partitions.ErdosModel

/-!
# The summatory ↔ windowed-sum index bridge

`S(β√n) − S(α√n) = Σ_{m ∈ Icc 1 (n−1)} [α√n < m ≤ β√n]·σ(m)` whenever `β√n ≤ n−1` — the
identity that converts half-open summatory masses into the if-windowed sums used by the
Erdős model kernel.  Opus-authored during the codex outage.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

/-- `Ioc` of floors = the real-window filter on `Icc 1 (n-1)`. -/
lemma window_filter_eq_Ioc {α β : ℝ} (hα : 0 ≤ α) {n : ℕ}
    (hcap : ⌊β * Real.sqrt n⌋₊ ≤ n - 1) :
    (Finset.Icc 1 (n - 1)).filter
        (fun m : ℕ => α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n)
      = Finset.Ioc ⌊α * Real.sqrt n⌋₊ ⌊β * Real.sqrt n⌋₊ := by
  have hαs : 0 ≤ α * Real.sqrt n := mul_nonneg hα (Real.sqrt_nonneg _)
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_, _⟩, hlt, hle⟩
    exact ⟨(Nat.floor_lt hαs).mpr hlt, Nat.le_floor hle⟩
  · rintro ⟨hlt, hle⟩
    have h1 : α * Real.sqrt n < (m : ℝ) := (Nat.floor_lt hαs).mp hlt
    have hm1 : 1 ≤ m := by omega
    have hb1 : 1 ≤ ⌊β * Real.sqrt n⌋₊ := le_trans hm1 hle
    have hβs : 0 ≤ β * Real.sqrt n := by
      by_contra hneg
      have h0 : ⌊β * Real.sqrt n⌋₊ = 0 :=
        Nat.floor_of_nonpos (le_of_lt (not_le.mp hneg))
      omega
    have h2 : (m : ℝ) ≤ β * Real.sqrt n := by
      calc (m : ℝ) ≤ (⌊β * Real.sqrt n⌋₊ : ℝ) := by exact_mod_cast hle
        _ ≤ β * Real.sqrt n := Nat.floor_le hβs
    exact ⟨⟨hm1, le_trans hle hcap⟩, h1, h2⟩

/-- **The index bridge**: for `0 ≤ α ≤ β` and `⌊β√n⌋ ≤ n−1`,
`S(β√n) − S(α√n) = Σ_{m ∈ Icc 1 (n−1)} [α√n < m ≤ β√n]·σ(m)`. -/
theorem summatory_diff_eq_window_sum {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) {n : ℕ}
    (hcap : ⌊β * Real.sqrt n⌋₊ ≤ n - 1) :
    summatory (β * Real.sqrt n) - summatory (α * Real.sqrt n)
      = ∑ m ∈ Finset.Icc 1 (n - 1),
          (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
           then sigmaR m else 0) := by
  set a := ⌊α * Real.sqrt n⌋₊ with ha_def
  set b := ⌊β * Real.sqrt n⌋₊ with hb_def
  have hab : a ≤ b := by
    apply Nat.floor_le_floor
    exact mul_le_mul_of_nonneg_right hαβ (Real.sqrt_nonneg _)
  -- RHS = sum over the Ioc of floors
  have hrhs :
      (∑ m ∈ Finset.Icc 1 (n - 1),
          (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
           then sigmaR m else 0))
        = ∑ m ∈ Finset.Ioc a b, sigmaR m := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [window_filter_eq_Ioc hα hcap]
  rw [hrhs]
  -- LHS: summatory difference = sum over Ioc a b
  unfold summatory
  rw [← hb_def, ← ha_def]
  have hIcc_Ioc : ∀ k : ℕ, Finset.Icc 1 k = Finset.Ioc 0 k := by
    intro k
    ext m
    simp [Finset.mem_Icc, Finset.mem_Ioc, Nat.lt_iff_add_one_le]
  have hsplit :
      (∑ m ∈ Finset.Ioc 0 a, sigmaR m) + ∑ m ∈ Finset.Ioc a b, sigmaR m
        = ∑ m ∈ Finset.Ioc 0 b, sigmaR m :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab
  rw [hIcc_Ioc b, hIcc_Ioc a, ← hsplit]
  ring

end AnalyticCombinatorics.Ch8.Partitions.Sigma
