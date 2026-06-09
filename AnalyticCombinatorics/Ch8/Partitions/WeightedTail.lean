import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateApprox2
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernelClose

/-!
# Weighted far-erdos tail: helper lemmas

Sub-lemmas adapted from `ErdosKernelClose.lean` with `(m:ℝ)` weight.
The capstone `weighted_far_erdos_tail_le` is pending.
Opus-authored.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos
open Close

/-- `m ∈ block k` ⟹ `m ≤ (k+1)·√n`. -/
lemma m_le_block_bound {n m k : ℕ} (hn : 0 < n) (hmk : blockIndex n m = k) :
    (m : ℝ) ≤ (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hfloor_lt : (m : ℝ) / Real.sqrt (n : ℝ) < (k : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((m : ℝ) / Real.sqrt (n : ℝ))
    have hfloor_eq : ⌊(m : ℝ) / Real.sqrt (n : ℝ)⌋₊ = k := by
      simpa [blockIndex] using hmk
    simpa [hfloor_eq, Nat.cast_add, Nat.cast_one] using h
  have hmul : (m : ℝ) / Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) ≤ ((k : ℝ) + 1) * Real.sqrt (n : ℝ) :=
    mul_le_mul_of_nonneg_right hfloor_lt.le hsqrt_pos.le
  have hsimpl : (m : ℝ) / Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (m : ℝ) := by
    field_simp [hsqrt_pos.ne']
  rw [hsimpl] at hmul
  simpa [Nat.cast_add] using hmul

/-- Per-block weighted bound. -/
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
    rw [← Finset.sum_mul, mul_comm]
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

/-- Weighted adaptation of `left_half_tail_sum_le_block_majorants`. -/
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
        · simp [f, htail, hhalf]
          exact mul_nonneg (Erdos.erdosWeight_nonneg_of_mem hmI) (by positivity)
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

/-- Cubic moment H₃ = Σ (j+1)³·q^j. -/
noncomputable def tailH3 : ℝ :=
  ∑' j : ℕ, (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j

lemma tailH3_pos : 0 < tailH3 := by
  dsimp [tailH3]
  have hnonneg : ∀ j, 0 ≤ (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j := by
    intro j; positivity
  have hsumm : Summable (fun j : ℕ => (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3
      (by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have hneg : -(C / 2) < 0 := by nlinarith [C_pos]
        exact Real.exp_lt_one_iff.mpr hneg)
    set q := Real.exp (-(C / 2)) with hqdef
    have : (fun j : ℕ => (((j : ℕ).succ : ℝ) ^ 3) * q ^ j)
        = (fun n => q⁻¹ * ((n : ℝ)^3 * q ^ n)) ∘ Nat.succ := by
      ext j; simp [hqdef, mul_comm, add_comm, mul_left_comm, mul_assoc]
    rw [this]
    exact (h.comp_injective Nat.succ_injective).mul_right q⁻¹
  have h_first_le : 1 ≤ ∑' j : ℕ, (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j := by
    calc 1 = ((0 : ℕ).succ : ℝ)^3 * Real.exp (-(C / 2)) ^ 0 := by norm_num
      _ = (∑ j ∈ ({0} : Finset ℕ), (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j) := by simp
      _ ≤ ∑' j : ℕ, (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j :=
        hsumm.sum_le_tsum ({0} : Finset ℕ) (by
          intro j hj; simp at hj; exact hnonneg j)
  have hpos_one : (0 : ℝ) < 1 := by norm_num
  have : 1 ≤ tailH3 := by
    dsimp [tailH3]; exact h_first_le
  linarith

lemma tailH3_nonneg : 0 ≤ tailH3 := tailH3_pos.le

/-- Weighted block-majorant shift identity. -/
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
    have : (fun j : ℕ => (((j : ℕ).succ : ℝ)^3) * q ^ j) = (fun n => q⁻¹ * ((n : ℝ)^3 * q ^ n)) ∘ Nat.succ := by
      ext j; simp [hqdef, mul_comm, add_comm, mul_left_comm, mul_assoc]
    rw [this]
    exact (h.comp_injective Nat.succ_injective).mul_right q⁻¹
  calc (∑' j : ℕ, leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * s))
      = (∑' j : ℕ,
          2 * sigmaQuadConst * (((j + Kn : ℕ) + 1 : ℝ) ^ 2) * q ^ (j + Kn)
          * (((j + Kn : ℕ) + 1 : ℝ) * s)) := by
    refine tsum_congr (fun j => ?_)
    rw [leftBlockMajorant, show Real.exp (-(C / 2) * ((j + Kn : ℕ) : ℝ))
        = q ^ (j + Kn) by rw [hqdef, ← Real.exp_nat_mul]; ring]
    ring
  _ = 2 * sigmaQuadConst * s * q ^ Kn * (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by
    have hsum_shift : Summable (fun j : ℕ => (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by
      have hineq' : ∀ j, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j ≤ (((j : ℕ).succ : ℝ) ^ 3) * ((Kn : ℝ) + 1) ^ 3 * q ^ j := by
        intro j; refine mul_le_mul_of_nonneg_right ?_ (by positivity); nlinarith [Nat.cast_nonneg j, Nat.cast_nonneg Kn]
      have hpos_shift : ∀ j, 0 ≤ (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j := by intro j; positivity
      refine Summable.of_nonneg_of_le (fun j => hpos_shift j) (fun j => hineq' j) ?_
      simpa [Pi.mul_def, mul_assoc, mul_comm, mul_left_comm] using hsum.mul_right (((Kn : ℝ) + 1)^3)
    calc (∑' j : ℕ, 2 * sigmaQuadConst * (((j + Kn : ℕ) + 1 : ℝ) ^ 2) * q ^ (j + Kn)
          * (((j + Kn : ℕ) + 1 : ℝ) * s))
        = (∑' j : ℕ, (2 * sigmaQuadConst * s * q ^ Kn) * ((((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j)) := by
      refine tsum_congr (fun j => ?_); ring
    _ = (2 * sigmaQuadConst * s * q ^ Kn) * (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by
      rw [hsum_shift.tsum_mul_left (2 * sigmaQuadConst * s * q ^ Kn)]
    _ = 2 * sigmaQuadConst * s * q ^ Kn * (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by ring
    refine tsum_congr (fun j => ?_); ring
  _ ≤ 2 * sigmaQuadConst * s * q ^ Kn
      * (((Kn : ℝ) + 1) ^ 3 * (∑' j : ℕ, (((j : ℕ).succ : ℝ) ^ 3) * q ^ j)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hpos_a : ∀ j, 0 ≤ (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j := by intro j; positivity
    have hineq : ∀ j, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j
        ≤ (((Kn : ℝ) + 1) ^ 3 * (((j : ℕ).succ : ℝ) ^ 3)) * q ^ j := by
      intro j; refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      nlinarith [Nat.cast_nonneg j, Nat.cast_nonneg Kn]
    have ha : Summable (fun j : ℕ => (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) :=
      Summable.of_nonneg_of_le hpos_a hineq (hsum.mul_left (((Kn : ℝ) + 1)^3))
    have hbpos : ∀ j, 0 ≤ (((Kn : ℝ) + 1) ^ 3 * (((j : ℕ).succ : ℝ) ^ 3)) * q ^ j := by
      intro j; positivity
    have hpart : ∀ (u : Finset ℕ), ∑ j ∈ u, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j
        ≤ ∑' j : ℕ, (((Kn : ℝ) + 1) ^ 3 * (((j : ℕ).succ : ℝ) ^ 3)) * q ^ j := by
      intro u
      refine le_trans (Finset.sum_le_sum (fun j _ => hineq j)) ?_
      refine (hsum.mul_left (((Kn : ℝ) + 1)^3)).sum_le_tsum u (fun j hj => hbpos j)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j)
        ≤ ∑' j : ℕ, (((Kn : ℝ) + 1) ^ 3 * (((j : ℕ).succ : ℝ) ^ 3)) * q ^ j :=
      Real.tsum_le_of_sum_le hpos_a hpart
    _ = ((Kn : ℝ) + 1) ^ 3 * (∑' j : ℕ, (((j : ℕ).succ : ℝ) ^ 3) * q ^ j) := by
      rw [hsum.tsum_mul_left (((Kn : ℝ) + 1)^3)]
  _ = 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 * q ^ Kn := by
    rw [tailH3]; ring
  _ = 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3
      * Real.exp (-(C / 2) * (Kn : ℝ)) := by
    rw [hqdef, ← Real.exp_nat_mul]; ring
  _ ≤ 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3
      * Real.exp (-(C / 2) * (Kn : ℝ)) * Real.exp (C / 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_of_eq (by ring)

/-- **Weighted far-erdos tail**: Σ_{m>⌊n^{2/3}⌋} erdosWeight·m ≤ const/n.
    Pending — capstone assembly from the sub-lemmas above. -/
theorem weighted_far_erdos_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Icc (⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ + 1) (n - 1), erdosWeight n m * (m : ℝ)) ≤ K / (n : ℝ) := by
  sorry

end AnalyticCombinatorics.Ch8.Partitions.Erdos
