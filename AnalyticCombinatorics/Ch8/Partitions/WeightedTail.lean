import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateApprox2
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernelClose

/-!
# Weighted far-erdos tail: `Σ_{m>⌊n^{2/3}⌋} erdosWeight·m ≤ const/n`

Three sub-lemmas adapted from `ErdosKernelClose.lean` (left_half_tail_sum_le_block_majorants)
with the extra `(m:ℝ)` weight, plus the capstone `weighted_far_erdos_tail_le`.
Opus-authored (weighted adaptations by ChatGPT ac1).
-/

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos
open Close

/-- `m ∈ block k` ⟹ `m ≤ (k+1)·√n`. -/
set_option maxHeartbeats 400000 in
lemma m_le_block_bound {n m k : ℕ} (hn : 0 < n) (hmk : blockIndex n m = k) :
    (m : ℝ) ≤ (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hfloor_lt : (m : ℝ) / Real.sqrt (n : ℝ) < (k : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((m : ℝ) / Real.sqrt (n : ℝ))
    have hfloor_eq : ⌊(m : ℝ) / Real.sqrt (n : ℝ)⌋₊ = k := by
      simpa [blockIndex] using hmk
    simpa [hfloor_eq, Nat.cast_add, Nat.cast_one] using h
  have hmul := mul_le_mul_of_nonneg_right hfloor_lt.le hsqrt_pos.le
  field_simp [hsqrt_pos.ne'] at hmul ⊢

/-- Per-block weighted bound: `Σ_{m∈block k, m≤n/2} erdosWeight·m ≤ leftBlockMajorant(k)·(k+1)·√n`. -/
set_option maxHeartbeats 400000 in
lemma weighted_kernel_block_left_half_le (n k : ℕ) (hn : 0 < n) :
    (∑ m ∈ (Finset.Icc 1 (n - 1)).filter
      (fun m => blockIndex n m = k ∧ 2 * m ≤ n),
      erdosWeight n m * (m : ℝ))
    ≤ leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by
  classical
  let s := (Finset.Icc 1 (n - 1)).filter
    (fun m => blockIndex n m = k ∧ 2 * m ≤ n)
  have hterm_le : ∀ m ∈ s,
      erdosWeight n m * (m : ℝ) ≤ erdosWeight n m * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by
    intro m hm
    have hmf : m ∈ (Finset.Icc 1 (n - 1)).filter
        (fun m => blockIndex n m = k ∧ 2 * m ≤ n) := by simpa [s] using hm
    have hmk : blockIndex n m = k := (Finset.mem_filter.mp hmf).2.1
    exact mul_le_mul_of_nonneg_left (m_le_block_bound hn hmk)
      (Erdos.erdosWeight_nonneg_of_mem (Finset.mem_filter.mp hmf).1)
  have hsum_le : (∑ m ∈ s, erdosWeight n m * (m : ℝ))
      ≤ ∑ m ∈ s, erdosWeight n m * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) :=
    Finset.sum_le_sum hterm_le
  have hfactor : (∑ m ∈ s, erdosWeight n m * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)))
      = (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) * (∑ m ∈ s, erdosWeight n m) := by
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have hblock : (∑ m ∈ s, erdosWeight n m) ≤ leftBlockMajorant k := by
    simpa [s, leftBlockMajorant] using kernel_block_left_half_le n k hn
  have hcoef_nonneg : 0 ≤ (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by positivity
  calc
    (∑ m ∈ s, erdosWeight n m * (m : ℝ))
        ≤ ∑ m ∈ s, erdosWeight n m * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := hsum_le
    _ = (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) * (∑ m ∈ s, erdosWeight n m) := hfactor
    _ ≤ (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) * leftBlockMajorant k :=
      mul_le_mul_of_nonneg_left hblock hcoef_nonneg
    _ = leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by ring

/-- Weighted adaptation of `left_half_tail_sum_le_block_majorants`.
  `Σ_{m} erdosWeight·m·indicator ≤ Σ_{k} leftBlockMajorant(k)·(k+1)·√n·indicator`. -/
set_option maxHeartbeats 1000000 in
lemma weighted_left_half_tail_sum_le_block_majorants (n K : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
      then erdosWeight n m * (m : ℝ)
      else 0)
    ≤ ∑ k ∈ Finset.range (numBlocks n),
        if K ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ))
        else 0 := by
  classical
  let f : ℕ → ℝ := fun m =>
    if (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
    then erdosWeight n m * (m : ℝ) else 0
  have hdecomp := block_decomposition n f
  rw [hdecomp]
  refine Finset.sum_le_sum (fun k _ => ?_)
  by_cases hKk : K ≤ k
  · have hterm_le : ∀ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
        f m ≤ if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0 := by
      intro m hm
      have hmI : m ∈ Finset.Icc 1 (n - 1) := (Finset.mem_filter.mp hm).1
      by_cases hhalf : 2 * m ≤ n
      · by_cases htail : (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ)
        · simp [f, htail, hhalf]
        · simp [f, htail, hhalf, mul_nonneg (Erdos.erdosWeight_nonneg_of_mem hmI) (by positivity)]
      · simp [f, hhalf]
    have hsum_le_half : (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m)
        ≤ ∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
          if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0 :=
      Finset.sum_le_sum hterm_le
    have hhalf_eq : (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
          if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0)
        = ∑ m ∈ (Finset.Icc 1 (n - 1)).filter
            (fun m => blockIndex n m = k ∧ 2 * m ≤ n),
          erdosWeight n m * (m : ℝ) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      by_cases hb : blockIndex n m = k
      · by_cases hh : 2 * m ≤ n <;> simp [hb, hh]
      · simp [hb]
    calc
      (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m)
          ≤ ∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
            if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0 := hsum_le_half
      _ = ∑ m ∈ (Finset.Icc 1 (n - 1)).filter
            (fun m => blockIndex n m = k ∧ 2 * m ≤ n),
          erdosWeight n m * (m : ℝ) := hhalf_eq
      _ ≤ leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) :=
        weighted_kernel_block_left_half_le n k hn
      _ = (if K ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) else 0) := by
        simp [hKk]
  · have hzero : ∀ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
        f m = 0 := by
      intro m hm
      by_cases htail : (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ)
      · have hge := tail_block_index_ge (n := n) (K := K) (k := k) (m := m) hn hm htail
        exact False.elim (hKk hge)
      · simp [f, htail]
    calc
      (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m) = 0 :=
        Finset.sum_eq_zero hzero
      _ ≤ (if K ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) else 0) := by
        simp [hKk]

/-- The constant for the weighted shift identity: `Σ_{j} leftBlockMajorant(j+Kn)·((j+Kn+1)·√n)`. -/
noncomputable def tailH3 : ℝ :=
  ∑' j : ℕ, (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j

lemma tailH3_pos : 0 < tailH3 := by
  dsimp [tailH3]
  refine lt_of_lt_of_le (by
    have h0 : (0 : ℝ) < ((0 : ℕ).succ : ℝ)^3 * Real.exp (-(C / 2)) ^ 0 := by norm_num
    exact h0) (tsum_nonneg (fun j => by positivity))

lemma tailH3_nonneg : 0 ≤ tailH3 := tailH3_pos.le

/-- Weighted block-majorant shift identity. -/
set_option maxHeartbeats 2000000 in
lemma leftBlockMajorant_weighted_shifted_tsum_le (Kn : ℕ) (s : ℝ) (hs : 0 < s) :
    (∑' j : ℕ, leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * s))
    ≤ 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3
      * Real.exp (-(C / 2) * (Kn : ℝ)) * Real.exp (C / 2) := by
  have hqpos : 0 < Real.exp (-(C / 2)) := Real.exp_pos _
  have hqlt1 : Real.exp (-(C / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [C_pos]
  set q := Real.exp (-(C / 2)) with hqdef
  have hsum : Summable (fun j : ℕ => (((j : ℕ).succ : ℝ)^3) * q ^ j) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3
      (by rw [Real.norm_eq_abs, abs_of_pos hqpos]; exact hqlt1)
    exact h
  calc (∑' j : ℕ, leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * s))
      = (∑' j : ℕ,
          2 * sigmaQuadConst * (((j + Kn : ℕ) + 1 : ℝ) ^ 2) * q ^ (j + Kn)
          * (((j + Kn : ℕ) + 1 : ℝ) * s)) := by
    apply tsum_congr; intro j
    rw [leftBlockMajorant, show Real.exp (-(C / 2) * ((j + Kn : ℕ) : ℝ))
        = q ^ (j + Kn) by rw [hqdef, ← Real.exp_nat_mul]; ring]
    ring
  _ = 2 * sigmaQuadConst * s * q ^ Kn * (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by
    rw [tsum_mul_left, tsum_mul_left, tsum_mul_right]
    refine tsum_congr (fun j => ?_); ring
  _ ≤ 2 * sigmaQuadConst * s * q ^ Kn
      * (((Kn : ℝ) + 1) ^ 3 * (∑' j : ℕ, (((j : ℕ).succ : ℝ) ^ 3) * q ^ j)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j)
        ≤ ∑' j : ℕ, (((Kn : ℝ) + 1) ^ 3 * (((j : ℕ).succ : ℝ) ^ 3)) * q ^ j := by
      refine tsum_le_tsum (fun j => mul_le_mul_of_nonneg_right ?_ (by positivity)) ?_ ?_
      · have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
        have hk : 0 ≤ (Kn : ℝ) := Nat.cast_nonneg _
        nlinarith
      · exact hsum
      · have hbound := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3
          (by rw [Real.norm_eq_abs, abs_of_pos hqpos]; exact hqlt1)
        refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hbound
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith
    _ = ((Kn : ℝ) + 1) ^ 3 * tailH3 := by rw [tsum_mul_left, tailH3]
  _ = 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 * q ^ Kn := by ring
  _ = 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3
      * Real.exp (-(C / 2) * (Kn : ℝ)) := by
    rw [hqdef, ← Real.exp_nat_mul]; ring
  _ ≤ 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3
      * Real.exp (-(C / 2) * (Kn : ℝ)) * Real.exp (C / 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_of_eq (by ring)

/-- **Weighted far-erdos tail**: `Σ_{m>⌊n^{2/3}⌋} erdosWeight·m ≤ const/n`. -/
set_option maxHeartbeats 4000000 in
theorem weighted_far_erdos_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Icc (⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ + 1) (n - 1), erdosWeight n m * (m : ℝ)) ≤ K / (n : ℝ) := by
  have hCpos2 : (0:ℝ) < C / 2 := by nlinarith [C_pos]
  have hCpos10 : (0:ℝ) < C / 10 := by nlinarith [C_pos]
  have hsQ : 0 ≤ sigmaQuadConst := sigmaQuadConst_pos.le
  have hH3pos : 0 < tailH3 := tailH3_pos
  have hKconst : 0 ≤ 16 * sigmaQuadConst * tailH3 * Real.exp (C) := by positivity
  refine ⟨1 + 16 * sigmaQuadConst * tailH3 * Real.exp (C) + 1, by linarith, ?_⟩
  filter_upwards [poly_mul_exp_neg_sqrt_le_inv (C / 10) hCpos10 4,
    poly_mul_exp_neg_sixthRoot_le_inv (C / 2) hCpos2 2,
    Filter.eventually_ge_atTop 2] with n hsqrt hsixth hn2
  have hnpos : 0 < n := by omega
  have hnpos' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos'
  have hew_nn : ∀ m, 0 ≤ erdosWeight n m := fun m => by
    rw [erdosWeight]
    exact mul_nonneg (div_nonneg (sigmaR_nonneg m) (by positivity)) (Real.exp_pos _).le
  set M : ℕ := ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ with hMdef
  set Kn : ℕ := ⌊(n:ℝ) ^ (1/6 : ℝ)⌋₊ with hKndef
  -- split into right-half and left-half
  have hsplit : ∀ m : ℕ, erdosWeight n m
      = (if n < 2 * m then erdosWeight n m else 0)
      + (if 2 * m ≤ n then erdosWeight n m else 0) := by
    intro m; rcases lt_or_ge n (2 * m) with h | h
    · rw [if_pos h, if_neg (by omega)]; ring
    · rw [if_neg (by omega), if_pos h]; ring
  have hsum_split : (∑ m ∈ Icc (M + 1) (n - 1), erdosWeight n m * (m : ℝ))
      = (∑ m ∈ Icc (M + 1) (n - 1), (if n < 2 * m then erdosWeight n m else 0) * (m : ℝ))
      + (∑ m ∈ Icc (M + 1) (n - 1), (if 2 * m ≤ n then erdosWeight n m else 0) * (m : ℝ)) := by
    rw [Finset.sum_congr rfl (fun m _ => by rw [hsplit m, add_mul]), Finset.sum_add_distrib]
  rw [hsum_split]
  -- right-half
  have hright : (∑ m ∈ Icc (M + 1) (n - 1), (if n < 2 * m then erdosWeight n m else 0) * (m : ℝ))
      ≤ 1 / (n : ℝ) := by
    have hright_bound : (∑ m ∈ Icc (M + 1) (n - 1), (if n < 2 * m then erdosWeight n m else 0) * (m : ℝ))
        ≤ (n : ℝ) * ((n : ℝ)^3 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ))) := by
      calc (∑ m ∈ Icc (M + 1) (n - 1), (if n < 2 * m then erdosWeight n m else 0) * (m : ℝ))
          ≤ (n : ℝ) * (∑ m ∈ Icc (M + 1) (n - 1), if n < 2 * m then erdosWeight n m else 0) := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        by_cases h : n < 2 * m
        · rw [if_pos h, if_pos h]
          refine mul_le_mul_of_nonneg_right (hew_nn m) (by
            have hmle : m ≤ n - 1 := (Finset.mem_Icc.mp hm).2
            exact_mod_cast hmle.trans (by omega))
        · rw [if_neg h, if_neg h]
      _ ≤ (n : ℝ) * (∑ m ∈ Icc (M + 1) (n - 1), if n < 2 * m then erdosWeight n m else 0) := le_refl _
      _ ≤ (n : ℝ) * ((n : ℝ)^3 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (by
          refine le_trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl)
              (fun m _ _ => ?_)) (right_half_kernel_sum_le n)
          split <;> (exact hew_nn m <;> exact le_refl 0))
        (by positivity)
    have hright : (∑ m ∈ Icc (M + 1) (n - 1), (if n < 2 * m then erdosWeight n m else 0) * (m : ℝ))
        ≤ 1 / (n : ℝ) := by
      linarith [hright_bound, hsqrt]
    exact hright
  -- left-half
  have hleft : (∑ m ∈ Icc (M + 1) (n - 1), (if 2 * m ≤ n then erdosWeight n m else 0) * (m : ℝ))
      ≤ 16 * sigmaQuadConst * tailH3 * Real.exp (C) * (1 / (n : ℝ)) := by
    have hcond : (∑ m ∈ Icc (M + 1) (n - 1),
        (if 2 * m ≤ n then erdosWeight n m else 0) * (m : ℝ))
        ≤ ∑ m ∈ Icc 1 (n - 1),
            if (Kn : ℝ) * Real.sqrt (n:ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
            then erdosWeight n m * (m : ℝ) else 0 := by
      refine Finset.sum_le_sum (fun m hm => ?_)
      rw [Finset.mem_Icc] at hm
      have hKnm : (Kn : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ) := by
        have hm_gt : (n:ℝ) ^ (2/3 : ℝ) < (m : ℝ) := by
          have hlt : (n:ℝ) ^ (2/3 : ℝ) < (M:ℝ) + 1 := by
            have := Nat.lt_floor_add_one ((n:ℝ) ^ (2/3 : ℝ))
            rw [← hMdef] at this; linarith
          have hge : (M:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hm.1
          linarith
        calc (Kn : ℝ) * Real.sqrt (n : ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) * Real.sqrt (n : ℝ) :=
              mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (Real.sqrt_nonneg _)
          _ = (n:ℝ) ^ (2/3 : ℝ) := by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos']; norm_num
          _ ≤ (m : ℝ) := le_of_lt hm_gt
      by_cases h2 : 2 * m ≤ n
      · rw [if_pos h2, if_pos ⟨hKnm, h2⟩]
      · rw [if_neg h2, if_neg (fun h => h2 h.2)]
    have hblock := weighted_left_half_tail_sum_le_block_majorants n Kn hnpos
    have hfinite : (∑ k ∈ range (numBlocks n),
        if Kn ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) else 0)
        ≤ (∑' j : ℕ, leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * Real.sqrt (n : ℝ))) := by
      -- All terms are nonnegative, and the finite sum (over k≥Kn) is a subset of the tsum (over j = k−Kn ≥ 0)
      have hsum_wt : Summable (fun j : ℕ =>
          leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * Real.sqrt (n : ℝ))) := by
        -- leftBlockMajorant k = 2·σQ·(k+1)²·exp(-(C/2)·k)
        -- multiplied by (k+1)·√n gives 2·σQ·√n·(k+1)³·exp(-(C/2)·k)
        -- which is summable since Σ (k+1)³·q^k converges for |q|<1
        have hq : ‖Real.exp (-(C / 2))‖ < 1 := by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_lt_one_iff.mpr (by nlinarith [C_pos])
        have hsum_cube := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hq
        -- (j+Kn+1)³ = ((j+Kn)+1)³ — use the bound (a+b)³ ≤ 8·a³·b³ for a,b≥1?
        -- Actually: (j+Kn+1)³ = ((j+1)+Kn)³. Use: (x+Kn)³ ≤ (Kn+1)³·(x+1)³ for x≥0 (elementary)
        -- But we can also just use absolute summability of the L³ form:
        have hsum_shift : Summable (fun j : ℕ =>
            ((j + Kn : ℕ) + 1 : ℝ)^3 * Real.exp (-(C / 2)) ^ (j + Kn)) := by
          -- j→j+Kn is an injective shift of a summable series
          refine (hsum_cube.comp_injective (add_right_injective Kn)).congr (fun j => ?_)
          simp [add_comm, add_left_comm, add_assoc]
        refine (hsum_shift.mul_left (2 * sigmaQuadConst * Real.sqrt (n : ℝ))).congr (fun j => ?_)
        rw [leftBlockMajorant, show Real.exp (-(C / 2) * ((j + Kn : ℕ) : ℝ))
            = Real.exp (-(C / 2)) ^ (j + Kn) by rw [← Real.exp_nat_mul]; ring]
        ring
      -- Set up the reindexing: each k ≥ Kn maps to j = k−Kn ≥ 0
      let s : Finset ℕ := (range (numBlocks n)).filter (fun k => Kn ≤ k)
      have heq : (∑ k ∈ range (numBlocks n),
          if Kn ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) else 0)
          = ∑ k ∈ s, leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by
        simp [s, Finset.sum_filter]
      rw [heq]
      -- The finite sum over s is ≤ the tsum over all j (since all terms ≥ 0)
      have himage : (∑ k ∈ s, leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)))
          = (∑ k ∈ s, leftBlockMajorant ((k - Kn) + Kn) * ((((k - Kn) + Kn : ℕ) + 1 : ℝ) * Real.sqrt (n : ℝ))) := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hkKn : Kn ≤ k := (Finset.mem_filter.mp hk).2
        rw [Nat.sub_add_cancel hkKn]
      rw [himage]
      -- Now apply sum_subset to extend to full tsum
      have hsubset : (s.image (fun k => k - Kn) : Set ℕ) ⊆ Set.univ := by simp
      refine le_trans (by
        refine Finset.sum_le_sum_of_subset ?_ (fun i _ _ => ?_)
        · -- the Finset s.image (k-Kn) maps injectively to ℕ
          intro i hi
          rw [Finset.mem_image] at hi
          obtain ⟨k, hk, rfl⟩ := hi
          -- this term is exactly matched to tsum index j = k−Kn
          exact Finset.mem_univ _
        · positivity) ?_
      -- Use sum_le_tsum: finite sum of nonnegative terms ≤ tsum
      exact hsum_wt.sum_le_tsum _
    have hweighted := leftBlockMajorant_weighted_shifted_tsum_le Kn (Real.sqrt (n : ℝ)) hs0
    have hKbound : Real.sqrt (n : ℝ) * ((Kn : ℝ) + 1) ^ 3 * Real.exp (-(C / 2) * (Kn : ℝ))
        ≤ 8 * Real.exp (C / 2) * (1 / ((n : ℝ) ^ 2)) := by
      have hKn_ge : (n:ℝ) ^ (1/6 : ℝ) - 1 ≤ (Kn : ℝ) := by
        have := Nat.lt_floor_add_one ((n:ℝ) ^ (1/6 : ℝ))
        rw [← hKndef] at this; linarith
      have hKn_cube : ((Kn : ℝ) + 1) ^ 3 ≤ 8 * Real.sqrt (n : ℝ) := by
        have hKn_le : (Kn : ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) := Nat.floor_le (by positivity)
        nlinarith [Real.sqrt_nonneg (n:ℝ), Real.sqrt_pos.mpr hnpos']
      calc Real.sqrt (n : ℝ) * ((Kn : ℝ) + 1) ^ 3 * Real.exp (-(C / 2) * (Kn : ℝ))
          ≤ Real.sqrt (n : ℝ) * (8 * Real.sqrt (n : ℝ)) * Real.exp (-(C / 2) * (Kn : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith
      _ = 8 * (n : ℝ) * Real.exp (-(C / 2) * (Kn : ℝ)) := by
        rw [Real.mul_self_sqrt (by positivity : 0 ≤ (n:ℝ))]; ring
      _ ≤ 8 * (n : ℝ) * (Real.exp (C / 2) * Real.exp (-(C / 2) * (n:ℝ) ^ (1/6 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        nlinarith
      _ = 8 * Real.exp (C / 2) * ((n:ℝ)^2 * Real.exp (-(C / 2) * (n:ℝ) ^ (1/6 : ℝ))) / (n : ℝ) := by
        ring
      _ ≤ 8 * Real.exp (C / 2) * (1 / (n : ℝ)) / (n : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        -- hsixth: n²·exp(-(C/2)·n^{1/6}) ≤ 1/n
        exact hsixth
      _ = 8 * Real.exp (C / 2) * (1 / ((n : ℝ) ^ 2)) := by ring
    calc (∑ m ∈ Icc (M + 1) (n - 1), (if 2 * m ≤ n then erdosWeight n m else 0) * (m : ℝ))
        ≤ ∑ m ∈ Icc 1 (n - 1),
            if (Kn : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
            then erdosWeight n m * (m : ℝ) else 0 := hcond
      _ ≤ ∑ k ∈ range (numBlocks n),
            if Kn ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ))
            else 0 := hblock
      _ ≤ (∑' j : ℕ, leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * Real.sqrt (n : ℝ))) := hfinite
      _ ≤ 2 * sigmaQuadConst * Real.sqrt (n : ℝ) * (((Kn : ℝ) + 1) ^ 3) * tailH3
          * Real.exp (-(C / 2) * (Kn : ℝ)) * Real.exp (C / 2) := hweighted
      _ = 2 * sigmaQuadConst * tailH3 * Real.exp (C / 2)
          * (Real.sqrt (n : ℝ) * ((Kn : ℝ) + 1) ^ 3 * Real.exp (-(C / 2) * (Kn : ℝ))) := by ring
      _ ≤ 2 * sigmaQuadConst * tailH3 * Real.exp (C / 2)
          * (8 * Real.exp (C / 2) * (1 / ((n : ℝ) ^ 2))) := by
        refine mul_le_mul_of_nonneg_left hKbound (by positivity)
      _ = 16 * sigmaQuadConst * tailH3 * Real.exp (C) * (1 / ((n : ℝ) ^ 2)) := by ring
      _ ≤ 16 * sigmaQuadConst * tailH3 * Real.exp (C) * (1 / (n : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : 1 / ((n : ℝ) ^ 2) ≤ 1 / (n : ℝ) := by
          refine (one_div_le_one_div (by positivity) (by positivity)).mpr ?_
          nlinarith
        exact this
  -- combine
  calc (∑ m ∈ Icc (M + 1) (n - 1), erdosWeight n m * (m : ℝ))
      = _ := hsum_split
    _ ≤ 1 / (n : ℝ) + 16 * sigmaQuadConst * tailH3 * Real.exp (C) * (1 / (n : ℝ)) :=
      add_le_add hright hleft
    _ = (1 + 16 * sigmaQuadConst * tailH3 * Real.exp (C)) / (n : ℝ) := by ring
    _ ≤ (1 + 16 * sigmaQuadConst * tailH3 * Real.exp (C) + 1) / (n : ℝ) :=
      (div_le_div_right hnpos').mpr (by nlinarith)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
