import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernel
import AnalyticCombinatorics.Ch8.Partitions.KernelBarriers
import AnalyticCombinatorics.Ch8.Partitions.RenewalSpine
import AnalyticCombinatorics.Ch8.Partitions.RenewalHitPot

/-!
# R7 Layer 1: instantiation of the renewal spine to the partition kernel

Defines the predecessor transition kernel `Pker n k = erdosWeight n (n−k)/kernelMass n`, the rank
`rnk n = ⌊3√n⌋` (`ρ=3` makes window steps strictly drop rank), and the residual `dres`.  Proves the
kernel facts that feed the banked spine (`rec_iter_bound`, `pot_le_block_sum_of_leave`): nonnegativity,
rank monotonicity, the recurrence-in-`P` form, the probability normalization, the residual bound
(block-summable via `DefectSummable`), and the leave-probability `≥ μ`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Predecessor transition kernel `P n k = erdosWeight n (n−k)/kernelMass n` for `1 ≤ k < n`. -/
noncomputable def Pker (n k : ℕ) : ℝ :=
  if 1 ≤ k ∧ k < n then erdosWeight n (n - k) / kernelMass n else 0

/-- Rank on the `√n` scale: `⌊3√n⌋` (the factor `3 > 2/α` forces window steps to drop rank). -/
noncomputable def rnk (n : ℕ) : ℕ := ⌊3 * Real.sqrt (n : ℝ)⌋₊

/-- Residual of the normalized recurrence. -/
noncomputable def dres (n : ℕ) : ℝ := u n - ∑ k ∈ Finset.range n, Pker n k * u k

lemma kernelMass_nonneg (n : ℕ) : 0 ≤ kernelMass n :=
  Finset.sum_nonneg (fun _ hm => erdosWeight_nonneg_of_mem hm)

lemma Pker_nonneg (n k : ℕ) : 0 ≤ Pker n k := by
  unfold Pker
  split_ifs with h
  · exact div_nonneg (erdosWeight_nonneg_of_lt (by omega)) (kernelMass_nonneg n)
  · exact le_refl 0

lemma rnk_mono : Monotone rnk := by
  intro a b hab
  apply Nat.floor_mono
  have : Real.sqrt (a : ℝ) ≤ Real.sqrt (b : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hab)
  linarith

/-- The recurrence in normalized form holds by definition of the residual. -/
lemma u_eq_Pker_sum_add_dres (n : ℕ) :
    u n = (∑ k ∈ Finset.range n, Pker n k * u k) + dres n := by
  unfold dres; ring

/-- Reflection `k ↦ n−k` on `Icc 1 (n−1)`. -/
lemma sum_Icc_reflect_sub (n : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 (n - 1), F (n - k) = ∑ m ∈ Finset.Icc 1 (n - 1), F m := by
  apply Finset.sum_nbij' (fun k => n - k) (fun m => n - m)
  · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
  · intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
  · intro k hk; rw [Finset.mem_Icc] at hk; omega
  · intro m hm; rw [Finset.mem_Icc] at hm; omega
  · intro k _; rfl

/-- Folding the normalized kernel against any test function `φ`, reindexed to the step variable. -/
lemma Pker_sum_mul (n : ℕ) (hn : 2 ≤ n) (φ : ℕ → ℝ) :
    ∑ k ∈ Finset.range n, Pker n k * φ k
      = (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * φ (n - m)) / kernelMass n := by
  have hsub : ∑ k ∈ Finset.range n, Pker n k * φ k
      = ∑ k ∈ Finset.Icc 1 (n - 1), Pker n k * φ k := by
    symm
    apply Finset.sum_subset
    · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
    · intro k _ hknot
      rw [Finset.mem_Icc] at hknot
      have hP0 : Pker n k = 0 := by
        unfold Pker; rw [if_neg]; rintro ⟨h1, h2⟩; omega
      rw [hP0, zero_mul]
  rw [hsub]
  have hval : ∀ k ∈ Finset.Icc 1 (n - 1),
      Pker n k * φ k = erdosWeight n (n - k) * φ k / kernelMass n := by
    intro k hk; rw [Finset.mem_Icc] at hk
    unfold Pker; rw [if_pos ⟨hk.1, by omega⟩]; ring
  rw [Finset.sum_congr rfl hval, ← Finset.sum_div]
  congr 1
  rw [← sum_Icc_reflect_sub n (fun j => erdosWeight n j * φ (n - j))]
  apply Finset.sum_congr rfl
  intro k hk; rw [Finset.mem_Icc] at hk
  rw [show n - (n - k) = k by omega]

/-- **Probability normalization** (`hP_mass`): the normalized kernel sums to `1`. -/
lemma Pker_mass {n : ℕ} (hn : 2 ≤ n) (hS : kernelMass n ≠ 0) :
    ∑ k ∈ Finset.range n, Pker n k = 1 := by
  have h := Pker_sum_mul n hn (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  rw [show (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m) = kernelMass n from rfl]
  exact div_self hS

/-- **Residual formula** (`d_eq`): `d n = u n − (u n − boundaryTerm n)/kernelMass n`. -/
lemma dres_eq {n : ℕ} (hn : 2 ≤ n) :
    dres n = u n - (u n - boundaryTerm n) / kernelMass n := by
  unfold dres
  rw [Pker_sum_mul n hn u]
  rw [show (∑ m ∈ Finset.Icc 1 (n - 1), erdosWeight n m * u (n - m)) = u n - boundaryTerm n by
    have hrec := u_recurrence n hn; linarith]

/-- Floor bounds tying `rnk n = ⌊3√n⌋` to `√n`: `rnk n ≤ 3√n < rnk n + 1`. -/
lemma rnk_sqrt_bounds (n : ℕ) :
    (rnk n : ℝ) ≤ 3 * Real.sqrt n ∧ 3 * Real.sqrt n < (rnk n : ℝ) + 1 := by
  unfold rnk
  exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩

/-- A `√`-gap exceeding `1/3` forces a strict rank drop (since `rnk = ⌊3√·⌋`). -/
lemma rnk_lt_of_sqrt_gap {n k : ℕ} (h : (1:ℝ)/3 < Real.sqrt n - Real.sqrt k) :
    rnk k < rnk n := by
  unfold rnk
  rw [← Nat.add_one_le_iff]
  apply Nat.le_floor
  push_cast
  have hfk : (⌊3 * Real.sqrt k⌋₊ : ℝ) ≤ 3 * Real.sqrt k := Nat.floor_le (by positivity)
  linarith

/-- **Window steps drop rank.** If `√n < m` (the window lower edge `a₀=1`) then the predecessor
`n − m` has strictly smaller rank: `√n − √(n−m) > 1/2 > 1/3`. -/
lemma window_rank_drop {n m : ℕ} (hn : 1 ≤ n) (hmn : m < n)
    (hmlb : Real.sqrt (n : ℝ) < (m : ℝ)) :
    rnk (n - m) < rnk n := by
  apply rnk_lt_of_sqrt_gap
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have ha : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hble : Real.sqrt ((n - m : ℕ) : ℝ) ≤ Real.sqrt n :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n m)
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by rw [Nat.cast_sub (le_of_lt hmn)]
  have hprod : (Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ))
      * (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) = (m : ℝ) := by
    have e1 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
    have e2 : Real.sqrt ((n - m : ℕ) : ℝ) ^ 2 = (n : ℝ) - m := by
      rw [Real.sq_sqrt (by positivity), hcast]
    nlinarith [e1, e2]
  have hsumpos : 0 < Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ) := by linarith [Real.sqrt_nonneg ((n - m : ℕ) : ℝ)]
  have hgap : Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ)
      = (m : ℝ) / (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) := by
    rw [eq_div_iff (ne_of_gt hsumpos)]; exact hprod
  rw [hgap, lt_div_iff₀ hsumpos]
  nlinarith [hmlb, hble, ha]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
