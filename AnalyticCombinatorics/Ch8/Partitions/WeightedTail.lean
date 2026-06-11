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

private lemma summable_succ_cube_geometric {q : ℝ} (hqpos : 0 < q) (hqlt1 : q < 1) :
    Summable (fun j : ℕ => (((j : ℕ).succ : ℝ) ^ 3) * q ^ j) := by
  have hnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact hqlt1
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hnorm
  have hsum_succ : Summable (fun j : ℕ => (((j : ℕ).succ : ℝ) ^ 3) * q ^ (j.succ)) :=
    h.comp_injective Nat.succ_injective
  refine (hsum_succ.mul_right q⁻¹).congr (fun j => ?_)
  rw [pow_succ' q j]
  field_simp [hqpos.ne']

private lemma shifted_cube_le (j K : ℕ) :
    (((j + K : ℕ) + 1 : ℝ) ^ 3) ≤
      (((j : ℕ).succ : ℝ) ^ 3) * (((K : ℝ) + 1) ^ 3) := by
  have hle : (((j + K : ℕ) + 1 : ℝ)) ≤ (((j : ℕ).succ : ℝ) * ((K : ℝ) + 1)) := by
    push_cast
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ)),
      (Nat.cast_nonneg K : (0 : ℝ) ≤ (K : ℝ)),
      mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
        (Nat.cast_nonneg K : (0 : ℝ) ≤ (K : ℝ))]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (((j + K : ℕ) + 1 : ℝ))) hle 3
  calc
    (((j + K : ℕ) + 1 : ℝ) ^ 3) ≤
        (((j : ℕ).succ : ℝ) * ((K : ℝ) + 1)) ^ 3 := hpow
    _ = (((j : ℕ).succ : ℝ) ^ 3) * (((K : ℝ) + 1) ^ 3) := by ring

private lemma summable_shifted_cube_geometric {q : ℝ} (hqpos : 0 < q) (hqlt1 : q < 1)
    (K : ℕ) :
    Summable (fun j : ℕ => (((j + K : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by
  have hsum : Summable (fun j : ℕ => (((j : ℕ).succ : ℝ) ^ 3) * q ^ j) :=
    summable_succ_cube_geometric hqpos hqlt1
  have hineq : ∀ j : ℕ,
      (((j + K : ℕ) + 1 : ℝ) ^ 3) * q ^ j ≤
        (((j : ℕ).succ : ℝ) ^ 3) * (((K : ℝ) + 1) ^ 3) * q ^ j := by
    intro j
    exact mul_le_mul_of_nonneg_right (shifted_cube_le j K) (by positivity)
  have hpos_shift : ∀ j : ℕ, 0 ≤ (((j + K : ℕ) + 1 : ℝ) ^ 3) * q ^ j := by
    intro j
    positivity
  refine Summable.of_nonneg_of_le hpos_shift hineq ?_
  simpa [Pi.mul_def, mul_assoc, mul_comm, mul_left_comm] using
    hsum.mul_right (((K : ℝ) + 1) ^ 3)

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
  have hsumm : Summable (fun j : ℕ => (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j) :=
    summable_succ_cube_geometric (q := Real.exp (-(C / 2))) (Real.exp_pos _)
      (by rw [Real.exp_lt_one_iff]; nlinarith [C_pos])
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
  set q := Real.exp (-(C / 2)) with hqdef
  have hqpos : 0 < q := by rw [hqdef]; exact Real.exp_pos _
  have hqlt1 : q < 1 := by
    rw [hqdef, Real.exp_lt_one_iff]
    nlinarith [C_pos]
  have hsum : Summable (fun j : ℕ => (((j : ℕ).succ : ℝ)^3) * q ^ j) :=
    summable_succ_cube_geometric hqpos hqlt1
  have hsum_shift : Summable (fun j : ℕ => (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) :=
    summable_shifted_cube_geometric hqpos hqlt1 Kn
  have hrewrite :
      (∑' j : ℕ, leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * s))
        = (2 * sigmaQuadConst * s * q ^ Kn) *
          (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by
    calc
      (∑' j : ℕ, leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * s))
          = ∑' j : ℕ,
              (2 * sigmaQuadConst * s * q ^ Kn) *
                ((((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by
            refine tsum_congr (fun j => ?_)
            rw [leftBlockMajorant, show Real.exp (-(C / 2) * ((j + Kn : ℕ) : ℝ))
                = q ^ (j + Kn) by
                  rw [hqdef, ← Real.exp_nat_mul]
                  congr 1
                  ring]
            rw [pow_add]
            norm_num [Nat.cast_add, Nat.cast_one]
            ring
      _ = (2 * sigmaQuadConst * s * q ^ Kn) *
          (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by
            rw [hsum_shift.tsum_mul_left (2 * sigmaQuadConst * s * q ^ Kn)]
  have htail : (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j)
      ≤ ((Kn : ℝ) + 1) ^ 3 * tailH3 := by
    have hbound : ∀ j : ℕ,
        (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j ≤
          (((Kn : ℝ) + 1) ^ 3) * ((((j : ℕ).succ : ℝ) ^ 3) * q ^ j) := by
      intro j
      calc
        (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j
            ≤ ((((j : ℕ).succ : ℝ) ^ 3) * (((Kn : ℝ) + 1) ^ 3)) * q ^ j :=
              mul_le_mul_of_nonneg_right (shifted_cube_le j Kn) (by positivity)
        _ = (((Kn : ℝ) + 1) ^ 3) * ((((j : ℕ).succ : ℝ) ^ 3) * q ^ j) := by ring
    have hdom : Summable (fun j : ℕ =>
        (((Kn : ℝ) + 1) ^ 3) * ((((j : ℕ).succ : ℝ) ^ 3) * q ^ j)) :=
      hsum.mul_left (((Kn : ℝ) + 1) ^ 3)
    calc
      (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j)
          ≤ ∑' j : ℕ,
              (((Kn : ℝ) + 1) ^ 3) * ((((j : ℕ).succ : ℝ) ^ 3) * q ^ j) :=
            Summable.tsum_le_tsum hbound hsum_shift hdom
      _ = ((Kn : ℝ) + 1) ^ 3 *
            (∑' j : ℕ, (((j : ℕ).succ : ℝ) ^ 3) * q ^ j) := by
            rw [hsum.tsum_mul_left (((Kn : ℝ) + 1) ^ 3)]
      _ = ((Kn : ℝ) + 1) ^ 3 * tailH3 := by
            rw [tailH3, hqdef]
  have hcoef_nonneg : 0 ≤ 2 * sigmaQuadConst * s * q ^ Kn := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) sigmaQuadConst_pos.le) hs.le)
      (pow_nonneg hqpos.le Kn)
  have hmain :
      (2 * sigmaQuadConst * s * q ^ Kn) *
        (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j)
      ≤ (2 * sigmaQuadConst * s * q ^ Kn) * (((Kn : ℝ) + 1) ^ 3 * tailH3) :=
    mul_le_mul_of_nonneg_left htail hcoef_nonneg
  have hge_exp : (1 : ℝ) ≤ Real.exp (C / 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [C_pos])
  calc
    (∑' j : ℕ, leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * s))
        = (2 * sigmaQuadConst * s * q ^ Kn) *
            (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := hrewrite
    _ ≤ (2 * sigmaQuadConst * s * q ^ Kn) * (((Kn : ℝ) + 1) ^ 3 * tailH3) := hmain
    _ = 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 * q ^ Kn := by ring
    _ = 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 *
          Real.exp (-(C / 2) * (Kn : ℝ)) := by
        rw [hqdef, ← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 *
          Real.exp (-(C / 2) * (Kn : ℝ)) * Real.exp (C / 2) := by
        have hbase_nonneg : 0 ≤ 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) *
            tailH3 * Real.exp (-(C / 2) * (Kn : ℝ)) := by
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (mul_nonneg (by norm_num) sigmaQuadConst_pos.le) hs.le)
                (by positivity))
              tailH3_nonneg)
            (Real.exp_pos _).le
        calc
          2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 *
              Real.exp (-(C / 2) * (Kn : ℝ))
              = 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 *
                  Real.exp (-(C / 2) * (Kn : ℝ)) * 1 := by ring
          _ ≤ 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 *
              Real.exp (-(C / 2) * (Kn : ℝ)) * Real.exp (C / 2) :=
                mul_le_mul_of_nonneg_left hge_exp hbase_nonneg

/-- **Weighted far-erdos tail**: Σ_{m>⌊n^{2/3}⌋} erdosWeight·m ≤ const/n.
    Finite weighted block tails are bounded by the shifted weighted majorant tsum. -/
private lemma finite_weighted_block_majorant_tail_le_shifted_tsum (N K : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (∑ k ∈ Finset.range N,
      if K ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * s) else 0) ≤
      ∑' j : ℕ, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := by
  classical
  let t := (Finset.range N).filter (fun k => K ≤ k)
  have hsum_filter :
      (∑ k ∈ Finset.range N,
        if K ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * s) else 0) =
        ∑ k ∈ t, leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * s) := by
    simp [t, Finset.sum_filter]
  let imageS : Finset ℕ := t.image (fun k => k - K)
  have hinj : Set.InjOn (fun k : ℕ => k - K) (↑t : Set ℕ) := by
    intro a ha b hb hsub
    have hKa : K ≤ a := by
      have hmem : a ∈ t := by simpa using ha
      exact (Finset.mem_filter.mp hmem).2
    have hKb : K ≤ b := by
      have hmem : b ∈ t := by simpa using hb
      exact (Finset.mem_filter.mp hmem).2
    calc
      a = (a - K) + K := (Nat.sub_add_cancel hKa).symm
      _ = (b - K) + K := by
        rw [show a - K = b - K from hsub]
      _ = b := Nat.sub_add_cancel hKb
  have hreindex :
      (∑ k ∈ t, leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * s)) =
        ∑ j ∈ imageS, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := by
    dsimp [imageS]
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro k hk
      have hKk : K ≤ k := (Finset.mem_filter.mp hk).2
      have hk_eq : k - K + K = k := Nat.sub_add_cancel hKk
      simp [hk_eq]
    · intro a ha b hb h
      exact hinj (by simpa using ha) (by simpa using hb) h
  have himage_subset : imageS ⊆ Finset.range N := by
    intro j hj
    dsimp [imageS] at hj
    rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
    have hkN : k < N := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    exact Finset.mem_range.mpr (by omega)
  have hterm_nonneg : ∀ j : ℕ,
      0 ≤ leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := by
    intro j
    exact mul_nonneg (leftBlockMajorant_nonneg (j + K)) (mul_nonneg (by positivity) hs)
  have hfinite_le_range :
      (∑ j ∈ imageS, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) ) ≤
        ∑ j ∈ Finset.range N, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
      (fun j _hj _hnot => hterm_nonneg j)
  have hshift_summable :
      Summable fun j : ℕ => leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := by
    set q := Real.exp (-(C / 2)) with hqdef
    have hqpos : 0 < q := by rw [hqdef]; exact Real.exp_pos _
    have hqlt1 : q < 1 := by
      rw [hqdef, Real.exp_lt_one_iff]
      nlinarith [C_pos]
    have hsum_shift : Summable (fun j : ℕ => (((j + K : ℕ) + 1 : ℝ) ^ 3) * q ^ j) :=
      summable_shifted_cube_geometric hqpos hqlt1 K
    refine (hsum_shift.mul_left (2 * sigmaQuadConst * s * q ^ K)).congr (fun j => ?_)
    rw [leftBlockMajorant, show Real.exp (-(C / 2) * ((j + K : ℕ) : ℝ)) = q ^ (j + K) by
      rw [hqdef, ← Real.exp_nat_mul]
      congr 1
      ring]
    rw [pow_add]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  have hprefix_le_tsum :
      (∑ j ∈ Finset.range N, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s))) ≤
        ∑' j : ℕ, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := by
    exact hshift_summable.sum_le_tsum (Finset.range N) (fun j _hj => hterm_nonneg j)
  calc
    (∑ k ∈ Finset.range N,
      if K ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * s) else 0)
        = ∑ k ∈ t, leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * s) := hsum_filter
    _ = ∑ j ∈ imageS, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := hreindex
    _ ≤ ∑ j ∈ Finset.range N, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := hfinite_le_range
    _ ≤ ∑' j : ℕ, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := hprefix_le_tsum

/-- **Weighted far-erdos tail**: Σ_{m>⌊n^{2/3}⌋} erdosWeight·m ≤ const/n. -/
theorem weighted_far_erdos_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Icc (⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ + 1) (n - 1), erdosWeight n m * (m : ℝ)) ≤ K / (n : ℝ) := by
  have hCpos := C_pos
  have hsQ : 0 ≤ sigmaQuadConst := sigmaQuadConst_pos.le
  have hH3 : 0 ≤ tailH3 := tailH3_nonneg
  have hKLnn : 0 ≤ 16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsQ) hH3) (Real.exp_pos _).le)
      (Real.exp_pos _).le
  refine ⟨1 + 16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) + 1,
    by linarith, ?_⟩
  filter_upwards [poly_mul_exp_neg_sqrt_le_inv (C / 10) (by linarith) 4,
    poly_mul_exp_neg_sixthRoot_le_inv (C / 2) (by linarith) 4,
    Filter.eventually_ge_atTop 2] with n hsqrt hsixth hn2
  have hn1 : 1 ≤ n := by omega
  have hn0' : 0 < n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hnge1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have hew_nn : ∀ m, 0 ≤ erdosWeight n m := fun m => by
    rw [erdosWeight]
    exact mul_nonneg (div_nonneg (sigmaR_nonneg m) (by positivity)) (Real.exp_pos _).le
  set M : ℕ := ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ with hMdef
  set Kn : ℕ := ⌊(n:ℝ) ^ (1/6 : ℝ)⌋₊ with hKndef
  have hsplit : ∀ m : ℕ, erdosWeight n m * (m : ℝ)
      = (if n < 2 * m then erdosWeight n m * (m : ℝ) else 0) +
        (if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0) := by
    intro m
    rcases lt_or_ge n (2 * m) with h | h
    · rw [if_pos h, if_neg (by omega)]
      ring
    · rw [if_neg (by omega), if_pos h]
      ring
  rw [Finset.sum_congr rfl (fun m _ => hsplit m), Finset.sum_add_distrib]
  have hright : (∑ m ∈ Finset.Icc (M + 1) (n - 1),
      if n < 2 * m then erdosWeight n m * (m : ℝ) else 0) ≤ 1 / (n:ℝ) := by
    have h1 : (∑ m ∈ Finset.Icc (M + 1) (n - 1),
        if n < 2 * m then erdosWeight n m * (m : ℝ) else 0)
        ≤ (n:ℝ) ^ 4 * Real.exp (-(C / 10) * Real.sqrt (n:ℝ)) := by
      calc
        (∑ m ∈ Finset.Icc (M + 1) (n - 1),
          if n < 2 * m then erdosWeight n m * (m : ℝ) else 0)
            ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
                if n < 2 * m then erdosWeight n m * (m : ℝ) else 0 := by
              refine Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.Icc_subset_Icc (by omega) le_rfl) (fun m _ _ => ?_)
              split_ifs
              · exact mul_nonneg (hew_nn m) (by positivity)
              · exact le_rfl
        _ ≤ (n:ℝ) * (∑ m ∈ Finset.Icc 1 (n - 1),
                if n < 2 * m then erdosWeight n m else 0) := by
              calc
                (∑ m ∈ Finset.Icc 1 (n - 1),
                  if n < 2 * m then erdosWeight n m * (m : ℝ) else 0)
                    ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
                        (n:ℝ) * (if n < 2 * m then erdosWeight n m else 0) := by
                      refine Finset.sum_le_sum (fun m hm => ?_)
                      by_cases hrightm : n < 2 * m
                      · rw [if_pos hrightm, if_pos hrightm]
                        have hmn : m ≤ n := by
                          have hmle : m ≤ n - 1 := (Finset.mem_Icc.mp hm).2
                          omega
                        have hmreal : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
                        have hmul := mul_le_mul_of_nonneg_left hmreal (hew_nn m)
                        nlinarith
                      · rw [if_neg hrightm, if_neg hrightm]
                        positivity
                _ = (n:ℝ) * (∑ m ∈ Finset.Icc 1 (n - 1),
                        if n < 2 * m then erdosWeight n m else 0) := by
                      rw [Finset.mul_sum]
        _ ≤ (n:ℝ) * ((n:ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (n:ℝ))) := by
              exact mul_le_mul_of_nonneg_left (right_half_kernel_sum_le n) (by positivity)
        _ = (n:ℝ) ^ 4 * Real.exp (-(C / 10) * Real.sqrt (n:ℝ)) := by ring
    linarith [h1, hsqrt]
  have hKn_le : (Kn:ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) := Nat.floor_le (by positivity)
  have h16le : (n:ℝ) ^ (1/6 : ℝ) ≤ (n:ℝ) := by
    calc
      (n:ℝ) ^ (1/6 : ℝ) ≤ (n:ℝ) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnge1 (by norm_num)
      _ = (n:ℝ) := Real.rpow_one _
  have hKnge : (n:ℝ) ^ (1/6 : ℝ) - 1 ≤ (Kn:ℝ) := by
    have := Nat.lt_floor_add_one ((n:ℝ) ^ (1/6 : ℝ))
    rw [← hKndef] at this
    linarith
  have hleft : (∑ m ∈ Finset.Icc (M + 1) (n - 1),
      if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0)
      ≤ 16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) * (1 / (n:ℝ)) := by
    have hcond : (∑ m ∈ Finset.Icc (M + 1) (n - 1),
        if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0)
        ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
            if (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (m:ℝ) ∧ 2 * m ≤ n
            then erdosWeight n m * (m : ℝ) else 0 := by
      calc
        (∑ m ∈ Finset.Icc (M + 1) (n - 1),
          if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0)
            ≤ ∑ m ∈ Finset.Icc (M + 1) (n - 1),
                if (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (m:ℝ) ∧ 2 * m ≤ n
                then erdosWeight n m * (m : ℝ) else 0 := by
              apply Finset.sum_le_sum
              intro m hm
              rw [Finset.mem_Icc] at hm
              have hKnm : (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (m:ℝ) := by
                have hm_gt : (n:ℝ) ^ (2/3 : ℝ) < (m:ℝ) := by
                  have hlt : (n:ℝ) ^ (2/3 : ℝ) < (M:ℝ) + 1 := by
                    have := Nat.lt_floor_add_one ((n:ℝ) ^ (2/3 : ℝ))
                    rw [← hMdef] at this
                    linarith
                  have hge : (M:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hm.1
                  linarith
                calc
                  (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) * Real.sqrt (n:ℝ) :=
                    mul_le_mul_of_nonneg_right hKn_le (Real.sqrt_nonneg _)
                  _ = (n:ℝ) ^ (2/3 : ℝ) := by
                    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
                    norm_num
                  _ ≤ (m:ℝ) := le_of_lt hm_gt
              by_cases h2 : 2 * m ≤ n
              · rw [if_pos h2, if_pos ⟨hKnm, h2⟩]
              · rw [if_neg h2, if_neg (fun h => h2 h.2)]
        _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc (by omega) le_rfl) (fun m _ _ => ?_)
          split_ifs
          · exact mul_nonneg (hew_nn m) (by positivity)
          · exact le_rfl
    have hchain : (∑ m ∈ Finset.Icc 1 (n - 1),
        if (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (m:ℝ) ∧ 2 * m ≤ n
        then erdosWeight n m * (m : ℝ) else 0)
        ≤ 2 * sigmaQuadConst * Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) * tailH3
          * Real.exp (-(C / 2) * (Kn:ℝ)) * Real.exp (C / 2) := by
      calc
        _ ≤ ∑ k ∈ Finset.range (numBlocks n),
              if Kn ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n:ℝ)) else 0 :=
            weighted_left_half_tail_sum_le_block_majorants n Kn hn0'
        _ ≤ ∑' j : ℕ, leftBlockMajorant (j + Kn) * ((((j + Kn : ℕ) + 1 : ℝ) * Real.sqrt (n:ℝ))) :=
            finite_weighted_block_majorant_tail_le_shifted_tsum (numBlocks n) Kn (Real.sqrt (n:ℝ))
              (Real.sqrt_nonneg _)
        _ ≤ _ := leftBlockMajorant_weighted_shifted_tsum_le Kn (Real.sqrt (n:ℝ)) hs0
    have hsqrt_le_n : Real.sqrt (n:ℝ) ≤ (n:ℝ) := by
      calc
        Real.sqrt (n:ℝ) = (n:ℝ) ^ (1/2 : ℝ) := by rw [Real.sqrt_eq_rpow]
        _ ≤ (n:ℝ) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hnge1 (by norm_num)
        _ = (n:ℝ) := Real.rpow_one _
    have hKn1le : (Kn:ℝ) + 1 ≤ 2 * (n:ℝ) := by
      nlinarith [hKn_le, h16le, hnge1]
    have hcubele : ((Kn:ℝ) + 1) ^ 3 ≤ 8 * (n:ℝ) ^ 3 := by
      have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (Kn:ℝ) + 1) hKn1le 3
      nlinarith
    have hpoly_le : Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) ≤ 8 * (n:ℝ) ^ 4 := by
      have hmul := mul_le_mul hsqrt_le_n hcubele
        (by positivity : 0 ≤ ((Kn:ℝ) + 1) ^ 3) (by positivity : 0 ≤ (n:ℝ))
      calc
        Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) ≤ (n:ℝ) * (8 * (n:ℝ) ^ 3) := hmul
        _ = 8 * (n:ℝ) ^ 4 := by ring
    have hexpKn : Real.exp (-(C / 2) * (Kn:ℝ))
        ≤ Real.exp (C / 2) * Real.exp (-(C / 2) * (n:ℝ) ^ (1/6 : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [hKnge, hCpos]
    have hKbound : Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) *
        Real.exp (-(C / 2) * (Kn:ℝ)) ≤ 8 * Real.exp (C / 2) * (1 / (n:ℝ)) := by
      calc
        Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) * Real.exp (-(C / 2) * (Kn:ℝ))
            ≤ (8 * (n:ℝ) ^ 4) *
                (Real.exp (C / 2) * Real.exp (-(C / 2) * (n:ℝ) ^ (1/6 : ℝ))) :=
              mul_le_mul hpoly_le hexpKn (Real.exp_pos _).le (by positivity)
        _ = 8 * Real.exp (C / 2) *
              ((n:ℝ) ^ 4 * Real.exp (-(C / 2) * (n:ℝ) ^ (1/6 : ℝ))) := by ring
        _ ≤ 8 * Real.exp (C / 2) * (1 / (n:ℝ)) :=
              mul_le_mul_of_nonneg_left hsixth (by positivity)
    have hcoef_nonneg : 0 ≤ 2 * sigmaQuadConst * tailH3 * Real.exp (C / 2) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsQ) hH3) (Real.exp_pos _).le
    calc
      (∑ m ∈ Finset.Icc (M + 1) (n - 1),
        if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0)
          ≤ 2 * sigmaQuadConst * Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) * tailH3
              * Real.exp (-(C / 2) * (Kn:ℝ)) * Real.exp (C / 2) := le_trans hcond hchain
      _ = 2 * sigmaQuadConst * tailH3 * Real.exp (C / 2) *
            (Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) *
              Real.exp (-(C / 2) * (Kn:ℝ))) := by ring
      _ ≤ 2 * sigmaQuadConst * tailH3 * Real.exp (C / 2) *
            (8 * Real.exp (C / 2) * (1 / (n:ℝ))) :=
          mul_le_mul_of_nonneg_left hKbound hcoef_nonneg
      _ = 16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) * (1 / (n:ℝ)) := by ring
  have hfinal : 1 / (n:ℝ) +
      16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) * (1 / (n:ℝ))
      ≤ (1 + 16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) + 1) / (n:ℝ) := by
    rw [add_div, add_div]
    have h16 : 16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) * (1 / (n:ℝ))
        = (16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2)) / (n:ℝ) := by ring
    rw [h16]
    linarith [show (0:ℝ) ≤ 1 / (n:ℝ) by positivity]
  linarith [hright, hleft, hfinal]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
