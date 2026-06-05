import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernel
import AnalyticCombinatorics.Ch8.Partitions.SigmaSummatory
import AnalyticCombinatorics.Ch8.Partitions.SigmaRecurrence

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

open Filter
open scoped BigOperators Topology Interval

noncomputable section

local notation "σR" => Sigma.sigmaR

def blockIndex (n m : ℕ) : ℕ :=
  ⌊(m : ℝ) / Real.sqrt (n : ℝ)⌋₊

def numBlocks (n : ℕ) : ℕ :=
  ⌊((n - 1 : ℕ) : ℝ) / Real.sqrt (n : ℝ)⌋₊ + 1

lemma blockIndex_lt_numBlocks {n m : ℕ} (hm : m ∈ Finset.Icc 1 (n - 1)) :
    blockIndex n m < numBlocks n := by
  have hm_le : m ≤ n - 1 := (Finset.mem_Icc.mp hm).2
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hdiv_le :
      (m : ℝ) / Real.sqrt (n : ℝ) ≤
        ((n - 1 : ℕ) : ℝ) / Real.sqrt (n : ℝ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm_le) hsqrt_nonneg
  have hfloor_le :
      ⌊(m : ℝ) / Real.sqrt (n : ℝ)⌋₊ ≤
        ⌊((n - 1 : ℕ) : ℝ) / Real.sqrt (n : ℝ)⌋₊ := by
    exact Nat.floor_mono hdiv_le
  dsimp [blockIndex, numBlocks]
  omega

lemma block_decomposition (n : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 (n - 1), f m) =
      ∑ k ∈ Finset.range (numBlocks n),
        ∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m := by
  classical
  exact (Finset.sum_fiberwise_of_maps_to
    (s := Finset.Icc 1 (n - 1))
    (t := Finset.range (numBlocks n))
    (g := blockIndex n)
    (f := f)
    (fun m hm => Finset.mem_range.mpr (blockIndex_lt_numBlocks hm))).symm

lemma block_subset_Icc_floor_succ_sqrt {n k m : ℕ}
    (hm : m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k)) :
    m ∈ Finset.Icc 1 ⌊((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)⌋₊ := by
  have hmI : m ∈ Finset.Icc 1 (n - 1) := (Finset.mem_filter.mp hm).1
  have hmk : blockIndex n m = k := (Finset.mem_filter.mp hm).2
  have hm_ge : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
  have hx_nonneg : 0 ≤ (m : ℝ) / Real.sqrt (n : ℝ) := by positivity
  have hfloor_lt :
      (m : ℝ) / Real.sqrt (n : ℝ) < (k : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((m : ℝ) / Real.sqrt (n : ℝ))
    have hfloor_eq : ⌊(m : ℝ) / Real.sqrt (n : ℝ)⌋₊ = k := by
      simpa [blockIndex] using hmk
    simpa [hfloor_eq, Nat.cast_add, Nat.cast_one] using h
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hm_lt :
      (m : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hfloor_lt.le hsqrt_nonneg
    have hleft :
        ((m : ℝ) / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) = (m : ℝ) := by
      by_cases hn : n = 0
      · subst hn
        have hm0 : m = 0 := by
          have hmle : m ≤ 0 := (Finset.mem_Icc.mp hmI).2
          omega
        simp [hm0]
      · have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := by
          exact (Real.sqrt_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)).ne'
        field_simp [hsqrt_ne]
    have hright :
        ((k : ℝ) + 1) * Real.sqrt (n : ℝ) =
          ((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ) := by
      norm_num
    simpa [hleft, hright] using hmul
  refine Finset.mem_Icc.mpr ⟨hm_ge, ?_⟩
  exact Nat.le_floor hm_lt

lemma sigma_block_le_floor_succ_sqrt (n k : ℕ) :
    (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), σR m) ≤
      ∑ m ∈ Finset.Icc 1 ⌊((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)⌋₊, σR m := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun m hm => block_subset_Icc_floor_succ_sqrt (n := n) (k := k) hm)
    (fun m _hm _hnot => Erdos.sigmaR_nonneg m)

lemma sigma_summatory_quadratic_bound_real :
    ∃ B : ℝ, 0 < B ∧
      ∀ x : ℝ, 1 ≤ x →
        (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, σR m) ≤ B * x ^ 2 := by
  rcases Erdos.sigma_summatory_quadratic_bound with ⟨B, hBpos, hB⟩
  refine ⟨B, hBpos, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hsq_le : (⌊x⌋₊ : ℝ) ^ 2 ≤ x ^ 2 := by
    exact (sq_le_sq₀ (by positivity : 0 ≤ (⌊x⌋₊ : ℝ)) hx0).mpr hfloor_le
  exact (hB ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left hsq_le hBpos.le)

def sigmaQuadConst : ℝ :=
  Classical.choose sigma_summatory_quadratic_bound_real

lemma sigmaQuadConst_pos : 0 < sigmaQuadConst :=
  (Classical.choose_spec sigma_summatory_quadratic_bound_real).1

lemma sigma_summatory_le_quad_real {x : ℝ} (hx : 1 ≤ x) :
    (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, σR m) ≤ sigmaQuadConst * x ^ 2 :=
  (Classical.choose_spec sigma_summatory_quadratic_bound_real).2 x hx

lemma sigma_block_le_const (n k : ℕ) :
      (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), σR m) ≤
        sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ) := by
  have hx1 : 1 ≤ ((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ) ∨
      ((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ) < 1 := le_or_gt 1 _
  rcases hx1 with hx1 | hxlt
  · have hsum := sigma_block_le_floor_succ_sqrt (n := n) (k := k)
    have hquad :=
      sigma_summatory_le_quad_real
        (x := ((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) hx1
    have hpow :
        (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) ^ 2 =
          ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
    calc
      (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), σR m)
          ≤ ∑ m ∈ Finset.Icc 1 ⌊((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)⌋₊, σR m := hsum
      _ ≤ sigmaQuadConst * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) ^ 2 := hquad
      _ = sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ) := by rw [hpow]; ring
  · have hfilter_empty :
        (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k) = ∅ := by
      ext m
      constructor
      · intro hm
        have hsub := block_subset_Icc_floor_succ_sqrt (n := n) (k := k) hm
        have hfloor0 : ⌊((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)⌋₊ = 0 := by
          exact Nat.floor_eq_zero.mpr hxlt
        have hmI := Finset.mem_Icc.mp hsub
        omega
      · intro hm
        simp at hm
    simpa [hfilter_empty] using
      (show 0 ≤ sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ) by
        exact mul_nonneg
          (mul_nonneg sigmaQuadConst_pos.le (sq_nonneg _))
          (by positivity))

lemma sqrt_drop_ge_half_scale {n m : ℕ} (hn : 0 < n) (hmn : m ≤ n) :
    (m : ℝ) / (2 * Real.sqrt (n : ℝ)) ≤
      Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ) := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hsub0 : 0 ≤ ((n - m : ℕ) : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos_of_pos (by exact_mod_cast hn)
  have hsqrt_sub_le :
      Real.sqrt ((n - m : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n m)
  have hdrop_nonneg :
      0 ≤ Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ) := by
    exact sub_nonneg.mpr hsqrt_sub_le
  have hsum_le :
      Real.sqrt (n : ℝ) + Real.sqrt ((n - m : ℕ) : ℝ) ≤
        2 * Real.sqrt (n : ℝ) := by
    nlinarith
  have hidentity :
      (m : ℝ) =
        (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)) *
          (Real.sqrt (n : ℝ) + Real.sqrt ((n - m : ℕ) : ℝ)) := by
    calc
      (m : ℝ)
          = (n : ℝ) - ((n - m : ℕ) : ℝ) := by
              rw [Nat.cast_sub hmn]
              ring
      _ = Real.sqrt (n : ℝ) ^ 2 - Real.sqrt ((n - m : ℕ) : ℝ) ^ 2 := by
              rw [Real.sq_sqrt hn0, Real.sq_sqrt hsub0]
      _ =
        (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)) *
          (Real.sqrt (n : ℝ) + Real.sqrt ((n - m : ℕ) : ℝ)) := by
              ring
  have hmul :
      (m : ℝ) ≤
        (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)) *
          (2 * Real.sqrt (n : ℝ)) := by
    rw [hidentity]
    exact mul_le_mul_of_nonneg_left hsum_le hdrop_nonneg
  exact (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (n : ℝ))).mpr hmul

lemma erdosWeight_le_model_left_half {n m : ℕ}
    (hn : 0 < n) (hmn : m < n) (hmhalf : 2 * m ≤ n) :
    erdosWeight n m ≤
      (2 / (n : ℝ)) * σR m *
        Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) := by
  have hn_pos_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden_pos_nat : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hden_pos : 0 < ((n - m : ℕ) : ℝ) := by exact_mod_cast hden_pos_nat
  have hden_ge_half : (n : ℝ) / 2 ≤ ((n - m : ℕ) : ℝ) := by
    have hmnle : m ≤ n := le_of_lt hmn
    rw [Nat.cast_sub hmnle]
    nlinarith [show (2 : ℝ) * (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmhalf]
  have hrecip :
      (1 : ℝ) / ((n - m : ℕ) : ℝ) ≤ 2 / (n : ℝ) := by
    calc
      (1 : ℝ) / ((n - m : ℕ) : ℝ)
          ≤ 1 / ((n : ℝ) / 2) :=
            one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) / 2) hden_ge_half
      _ = 2 / (n : ℝ) := by
            field_simp [hn_pos_real.ne']
  have hdrop :=
    sqrt_drop_ge_half_scale (n := n) (m := m) hn (le_of_lt hmn)
  have hexp :
      Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) ≤
        Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hCnonneg : 0 ≤ C := C_pos.le
    have hCmul := mul_le_mul_of_nonneg_left hdrop hCnonneg
    have hscale :
        C * ((m : ℝ) / (2 * Real.sqrt (n : ℝ))) =
          (C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ)) := by
      ring
    nlinarith
  have hsig_nonneg : 0 ≤ σR m := Erdos.sigmaR_nonneg m
  have hexp_nonneg :
      0 ≤ Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) :=
    (Real.exp_pos _).le
  calc
    erdosWeight n m
        = σR m * ((1 : ℝ) / ((n - m : ℕ) : ℝ)) *
            Real.exp (-C *
              (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) := by
            rw [erdosWeight]
            ring
    _ ≤ σR m * (2 / (n : ℝ)) *
            Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hrecip hsig_nonneg)
            hexp
            (Real.exp_pos _).le
            (mul_nonneg hsig_nonneg (by positivity : 0 ≤ 2 / (n : ℝ)))
    _ = (2 / (n : ℝ)) * σR m *
            Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) := by
          ring

lemma blockIndex_le_ratio (n m : ℕ) :
    (blockIndex n m : ℝ) ≤ (m : ℝ) / Real.sqrt (n : ℝ) := by
  dsimp [blockIndex]
  exact Nat.floor_le (by positivity : 0 ≤ (m : ℝ) / Real.sqrt (n : ℝ))

lemma model_exp_le_block_exp {n m k : ℕ} (hmk : blockIndex n m = k) :
    Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) ≤
      Real.exp (-(C / 2) * (k : ℝ)) := by
  apply Real.exp_le_exp.mpr
  have hk_le : (k : ℝ) ≤ (m : ℝ) / Real.sqrt (n : ℝ) := by
    simpa [hmk] using blockIndex_le_ratio n m
  have hC2_nonneg : 0 ≤ C / 2 := by linarith [C_pos]
  nlinarith [mul_le_mul_of_nonneg_left hk_le hC2_nonneg]

lemma erdosWeight_le_block_model_left_half {n m k : ℕ}
    (hn : 0 < n)
    (hm : m ∈ (Finset.Icc 1 (n - 1)).filter
      (fun m => blockIndex n m = k ∧ 2 * m ≤ n)) :
    erdosWeight n m ≤
      (2 / (n : ℝ)) * σR m * Real.exp (-(C / 2) * (k : ℝ)) := by
  have hm_filter := Finset.mem_filter.mp hm
  have hmI : m ∈ Finset.Icc 1 (n - 1) := hm_filter.1
  have hmk : blockIndex n m = k := hm_filter.2.1
  have hmhalf : 2 * m ≤ n := hm_filter.2.2
  have hmn : m < n := by
    have hmle : m ≤ n - 1 := (Finset.mem_Icc.mp hmI).2
    omega
  have hbase := erdosWeight_le_model_left_half (n := n) (m := m) hn hmn hmhalf
  have hexp := model_exp_le_block_exp (n := n) (m := m) (k := k) hmk
  have hcoef_nonneg : 0 ≤ (2 / (n : ℝ)) * σR m := by
    exact mul_nonneg (by positivity) (Erdos.sigmaR_nonneg m)
  calc
    erdosWeight n m
        ≤ (2 / (n : ℝ)) * σR m *
            Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) := hbase
    _ ≤ (2 / (n : ℝ)) * σR m * Real.exp (-(C / 2) * (k : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hexp hcoef_nonneg

lemma kernel_block_left_half_le (n k : ℕ) (hn : 0 < n) :
    (∑ m ∈ (Finset.Icc 1 (n - 1)).filter
      (fun m => blockIndex n m = k ∧ 2 * m ≤ n), erdosWeight n m) ≤
      2 * sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 *
        Real.exp (-(C / 2) * (k : ℝ)) := by
  classical
  let s := (Finset.Icc 1 (n - 1)).filter
    (fun m => blockIndex n m = k ∧ 2 * m ≤ n)
  let t := (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k)
  have hs_le :
      (∑ m ∈ s, erdosWeight n m) ≤
        ∑ m ∈ s, (2 / (n : ℝ)) * σR m * Real.exp (-(C / 2) * (k : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro m hm
    exact erdosWeight_le_block_model_left_half (n := n) (m := m) (k := k) hn (by simpa [s] using hm)
  have hfactor :
      (∑ m ∈ s, (2 / (n : ℝ)) * σR m * Real.exp (-(C / 2) * (k : ℝ))) =
        ((2 / (n : ℝ)) * Real.exp (-(C / 2) * (k : ℝ))) *
          (∑ m ∈ s, σR m) := by
    simp [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]
  have hsubset : s ⊆ t := by
    intro m hm
    simp [s, t] at hm ⊢
    exact ⟨hm.1, hm.2.1⟩
  have hsigma_s_le_t :
      (∑ m ∈ s, σR m) ≤ ∑ m ∈ t, σR m := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun m _hm _hnot => Erdos.sigmaR_nonneg m)
  have hblock := sigma_block_le_const n k
  have hcoef_nonneg :
      0 ≤ (2 / (n : ℝ)) * Real.exp (-(C / 2) * (k : ℝ)) := by
    positivity
  have hmain :
      ((2 / (n : ℝ)) * Real.exp (-(C / 2) * (k : ℝ))) *
          (∑ m ∈ s, σR m) ≤
        ((2 / (n : ℝ)) * Real.exp (-(C / 2) * (k : ℝ))) *
          (sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ)) := by
    exact mul_le_mul_of_nonneg_left (hsigma_s_le_t.trans (by simpa [t] using hblock)) hcoef_nonneg
  calc
    (∑ m ∈ s, erdosWeight n m)
        ≤ ∑ m ∈ s, (2 / (n : ℝ)) * σR m *
            Real.exp (-(C / 2) * (k : ℝ)) := hs_le
    _ = ((2 / (n : ℝ)) * Real.exp (-(C / 2) * (k : ℝ))) *
          (∑ m ∈ s, σR m) := hfactor
    _ ≤ ((2 / (n : ℝ)) * Real.exp (-(C / 2) * (k : ℝ))) *
          (sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ)) := hmain
    _ = 2 * sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 *
          Real.exp (-(C / 2) * (k : ℝ)) := by
          field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn]

lemma sqrt_sub_le_nine_tenths_sqrt {n r : ℕ} (hr : 2 * r ≤ n) :
    Real.sqrt (r : ℝ) ≤ (9 / 10 : ℝ) * Real.sqrt (n : ℝ) := by
  have hr_nonneg : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hright_nonneg : 0 ≤ (9 / 10 : ℝ) * Real.sqrt (n : ℝ) := by positivity
  have hsq :
      Real.sqrt (r : ℝ) ^ 2 ≤
        ((9 / 10 : ℝ) * Real.sqrt (n : ℝ)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ (r : ℝ))]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
    norm_num
    nlinarith [show (2 : ℝ) * (r : ℝ) ≤ (n : ℝ) by exact_mod_cast hr]
  exact (sq_le_sq₀ hr_nonneg hright_nonneg).mp hsq

lemma sqrt_drop_ge_right_half {n m : ℕ}
    (hmn : m ≤ n) (hright : n < 2 * m) :
    (1 / 10 : ℝ) * Real.sqrt (n : ℝ) ≤
      Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ) := by
  have hsub_half : 2 * (n - m) ≤ n := by omega
  have hsqrt_le :=
    sqrt_sub_le_nine_tenths_sqrt (n := n) (r := n - m) hsub_half
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

lemma erdosWeight_le_right_half {n m : ℕ}
    (hm : m ∈ Finset.Icc 1 (n - 1)) (hright : n < 2 * m) :
    erdosWeight n m ≤
      (n : ℝ) ^ 2 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
  have hmI := Finset.mem_Icc.mp hm
  have hm_pos : 1 ≤ m := hmI.1
  have hmn : m < n := by omega
  have hmn_le : m ≤ n := le_of_lt hmn
  have hden_pos_nat : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hden_pos : 0 < ((n - m : ℕ) : ℝ) := by exact_mod_cast hden_pos_nat
  have hden_ge_one : (1 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by
    exact_mod_cast hden_pos_nat
  have hsig := Erdos.sigmaR_le_square (n := m) hm_pos
  have hm_le_n_real : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn_le
  have hm_sq_le_n_sq : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity : 0 ≤ (m : ℝ)) (by positivity : 0 ≤ (n : ℝ))).mpr hm_le_n_real
  have hsig_le_n_sq : σR m ≤ (n : ℝ) ^ 2 := hsig.trans hm_sq_le_n_sq
  have hfrac_le :
      σR m / ((n - m : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hfrac_le_sig : σR m / ((n - m : ℕ) : ℝ) ≤ σR m := by
      rw [div_le_iff₀ hden_pos]
      have hmul := mul_le_mul_of_nonneg_left hden_ge_one (Erdos.sigmaR_nonneg m)
      simpa [one_mul] using hmul
    exact hfrac_le_sig.trans hsig_le_n_sq
  have hdrop := sqrt_drop_ge_right_half (n := n) (m := m) hmn_le hright
  have hexp :
      Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) ≤
        Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hCmul := mul_le_mul_of_nonneg_left hdrop C_pos.le
    nlinarith
  have hfrac_nonneg :
      0 ≤ σR m / ((n - m : ℕ) : ℝ) :=
    div_nonneg (Erdos.sigmaR_nonneg m) hden_pos.le
  calc
    erdosWeight n m
        = σR m / ((n - m : ℕ) : ℝ) *
            Real.exp (-C *
              (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) := rfl
    _ ≤ (n : ℝ) ^ 2 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
          exact mul_le_mul hfrac_le hexp (Real.exp_pos _).le (by positivity)

lemma right_half_kernel_sum_le (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if n < 2 * m then erdosWeight n m else 0) ≤
      (n : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
  classical
  let Bn : ℝ := (n : ℝ) ^ 2 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ))
  have hterm :
      ∀ m ∈ Finset.Icc 1 (n - 1),
        (if n < 2 * m then erdosWeight n m else 0) ≤ Bn := by
    intro m hm
    by_cases hright : n < 2 * m
    · simpa [Bn, hright] using erdosWeight_le_right_half (n := n) (m := m) hm hright
    · have hBn_nonneg : 0 ≤ Bn := by
        dsimp [Bn]
        positivity
      simp [hright, hBn_nonneg]
  have hsum :
      (∑ m ∈ Finset.Icc 1 (n - 1),
        if n < 2 * m then erdosWeight n m else 0) ≤
        ∑ m ∈ Finset.Icc 1 (n - 1), Bn := by
    exact Finset.sum_le_sum hterm
  have hcard : ((Finset.Icc 1 (n - 1)).card : ℝ) ≤ (n : ℝ) := by
    have hcard_nat : (Finset.Icc 1 (n - 1)).card ≤ n := by
      have hsubset : Finset.Icc 1 (n - 1) ⊆ Finset.range n := by
        intro m hm
        have hmge : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hmle : m ≤ n - 1 := (Finset.mem_Icc.mp hm).2
        exact Finset.mem_range.mpr (by omega)
      have h := Finset.card_le_card hsubset
      rw [Finset.card_range] at h
      exact h
    exact_mod_cast hcard_nat
  calc
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if n < 2 * m then erdosWeight n m else 0)
        ≤ ∑ m ∈ Finset.Icc 1 (n - 1), Bn := hsum
    _ = ((Finset.Icc 1 (n - 1)).card : ℝ) * Bn := by
          simp [Bn, nsmul_eq_mul]
    _ ≤ (n : ℝ) * Bn := by
          exact mul_le_mul_of_nonneg_right hcard (by dsimp [Bn]; positivity)
    _ = (n : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
          dsimp [Bn]
          ring

lemma nat_cube_mul_exp_neg_sqrt_tendsto_zero :
    Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)))
      atTop
      (𝓝 0) := by
  have hC10 : 0 < C / 10 := by linarith [C_pos]
  have hreal :
      Tendsto
        (fun x : ℝ => x ^ (6 : ℝ) * Real.exp (-(C / 10) * x))
        atTop
        (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (6 : ℝ) (C / 10) hC10
  have hsqrt_nat :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  refine (hreal.comp hsqrt_nat).congr' ?_
  filter_upwards with n
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hpow : Real.sqrt (n : ℝ) ^ (6 : ℝ) = (n : ℝ) ^ 3 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc
      Real.sqrt (n : ℝ) ^ 6 = (Real.sqrt (n : ℝ) ^ 2) ^ 3 := by ring
      _ = (n : ℝ) ^ 3 := by rw [Real.sq_sqrt hn0]
  change
    Real.sqrt (n : ℝ) ^ (6 : ℝ) *
        Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) =
      (n : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ))
  rw [hpow]

lemma right_half_kernel_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        ∑ m ∈ Finset.Icc 1 (n - 1),
          if n < 2 * m then erdosWeight n m else 0)
      atTop
      (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    nat_cube_mul_exp_neg_sqrt_tendsto_zero ?_ ?_
  · filter_upwards with n
    exact Erdos.erdos_kernel_cut_sum_nonneg n (fun m => n < 2 * m)
  · filter_upwards with n
    exact right_half_kernel_sum_le n

def leftBlockMajorant (k : ℕ) : ℝ :=
  2 * sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 *
    Real.exp (-(C / 2) * (k : ℝ))

lemma leftBlockMajorant_nonneg (k : ℕ) : 0 ≤ leftBlockMajorant k := by
  dsimp [leftBlockMajorant]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) sigmaQuadConst_pos.le)
      (sq_nonneg _))
    (Real.exp_pos _).le

lemma exp_neg_half_C_nat_eq_pow (k : ℕ) :
    Real.exp (-(C / 2) * (k : ℝ)) =
      (Real.exp (-(C / 2))) ^ k := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma summable_leftBlockMajorant : Summable leftBlockMajorant := by
  let r : ℝ := Real.exp (-(C / 2))
  have hr_pos : 0 < r := by dsimp [r]; positivity
  have hr_lt_one : ‖r‖ < 1 := by
    have hneg : -(C / 2) < 0 := by linarith [C_pos]
    have h : Real.exp (-(C / 2)) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
    simpa [r, abs_of_pos hr_pos] using h
  have h2 : Summable fun k : ℕ => ((k : ℝ) ^ 2) * r ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr_lt_one
  have h1 : Summable fun k : ℕ => ((k : ℝ) ^ 1) * r ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr_lt_one
  have h0 : Summable fun k : ℕ => ((k : ℝ) ^ 0) * r ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hr_lt_one
  have hpoly :
      Summable fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ 2) * r ^ k := by
    have hsum := (h2.add (h1.mul_left 2)).add h0
    refine hsum.congr ?_
    intro k
    norm_num
    ring
  refine hpoly.mul_left (2 * sigmaQuadConst) |>.congr ?_
  intro k
  dsimp [leftBlockMajorant, r]
  rw [exp_neg_half_C_nat_eq_pow k]
  ring

lemma tail_block_index_ge {n K k m : ℕ} (hn : 0 < n)
    (hm : m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k))
    (htail : (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ)) :
    K ≤ k := by
  have hmk : blockIndex n m = k := (Finset.mem_filter.mp hm).2
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos_of_pos (by exact_mod_cast hn)
  have hK_le_ratio : (K : ℝ) ≤ (m : ℝ) / Real.sqrt (n : ℝ) := by
    rw [le_div_iff₀' hsqrt_pos]
    simpa [mul_comm] using htail
  have hratio_lt : (m : ℝ) / Real.sqrt (n : ℝ) < (k : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((m : ℝ) / Real.sqrt (n : ℝ))
    have hfloor_eq : ⌊(m : ℝ) / Real.sqrt (n : ℝ)⌋₊ = k := by
      simpa [blockIndex] using hmk
    simpa [hfloor_eq, Nat.cast_add, Nat.cast_one] using h
  have hK_lt : (K : ℝ) < (k : ℝ) + 1 := lt_of_le_of_lt hK_le_ratio hratio_lt
  exact Nat.le_of_lt_succ (by exact_mod_cast hK_lt)

lemma left_half_tail_sum_le_block_majorants (n K : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
      then erdosWeight n m
      else 0) ≤
      ∑ k ∈ Finset.range (numBlocks n),
        if K ≤ k then leftBlockMajorant k else 0 := by
  classical
  let f : ℕ → ℝ := fun m =>
    if (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
    then erdosWeight n m
    else 0
  have hdecomp := block_decomposition n f
  rw [hdecomp]
  refine Finset.sum_le_sum ?_
  intro k hk
  by_cases hKk : K ≤ k
  · have hterm_le :
        ∀ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
          f m ≤ if 2 * m ≤ n then erdosWeight n m else 0 := by
      intro m hm
      have hmI : m ∈ Finset.Icc 1 (n - 1) := (Finset.mem_filter.mp hm).1
      by_cases hhalf : 2 * m ≤ n
      · by_cases htail : (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ)
        · simp [f, htail, hhalf]
        · simp [f, htail, hhalf, Erdos.erdosWeight_nonneg_of_mem hmI]
      · simp [f, hhalf]
    have hsum_le_half :
        (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m) ≤
          ∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
            if 2 * m ≤ n then erdosWeight n m else 0 := by
      exact Finset.sum_le_sum hterm_le
    have hhalf_eq :
        (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
            if 2 * m ≤ n then erdosWeight n m else 0) =
          ∑ m ∈ (Finset.Icc 1 (n - 1)).filter
            (fun m => blockIndex n m = k ∧ 2 * m ≤ n), erdosWeight n m := by
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro m hm
      by_cases hb : blockIndex n m = k
      · by_cases hh : 2 * m ≤ n <;> simp [hb, hh]
      · simp [hb]
    calc
      (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m)
          ≤ ∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
            if 2 * m ≤ n then erdosWeight n m else 0 := hsum_le_half
      _ = ∑ m ∈ (Finset.Icc 1 (n - 1)).filter
            (fun m => blockIndex n m = k ∧ 2 * m ≤ n), erdosWeight n m := hhalf_eq
      _ ≤ leftBlockMajorant k := by
            simpa [leftBlockMajorant] using kernel_block_left_half_le n k hn
      _ = (if K ≤ k then leftBlockMajorant k else 0) := by simp [hKk]
  · have hzero :
        ∀ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m = 0 := by
      intro m hm
      by_cases htail : (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ)
      · have hge := tail_block_index_ge (n := n) (K := K) (k := k) (m := m) hn hm htail
        exact False.elim (hKk hge)
      · simp [f, htail]
    calc
      (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m)
          = 0 := Finset.sum_eq_zero hzero
      _ ≤ (if K ≤ k then leftBlockMajorant k else 0) := by simp [hKk]

lemma finite_block_majorant_tail_le_shifted_tsum (N K : ℕ) :
    (∑ k ∈ Finset.range N, if K ≤ k then leftBlockMajorant k else 0) ≤
      ∑' j : ℕ, leftBlockMajorant (j + K) := by
  classical
  let s := (Finset.range N).filter (fun k => K ≤ k)
  have hsum_filter :
      (∑ k ∈ Finset.range N, if K ≤ k then leftBlockMajorant k else 0) =
        ∑ k ∈ s, leftBlockMajorant k := by
    simp [s, Finset.sum_filter]
  let imageS : Finset ℕ := s.image (fun k => k - K)
  have hinj : Set.InjOn (fun k : ℕ => k - K) (↑s : Set ℕ) := by
    intro a ha b hb hsub
    have hKa : K ≤ a := by
      have hmem : a ∈ s := by simpa using ha
      exact (Finset.mem_filter.mp hmem).2
    have hKb : K ≤ b := by
      have hmem : b ∈ s := by simpa using hb
      exact (Finset.mem_filter.mp hmem).2
    have hsub' : a - K = b - K := hsub
    calc
      a = (a - K) + K := (Nat.sub_add_cancel hKa).symm
      _ = (b - K) + K := by rw [hsub']
      _ = b := Nat.sub_add_cancel hKb
  have hreindex :
      (∑ k ∈ s, leftBlockMajorant k) =
        ∑ j ∈ imageS, leftBlockMajorant (j + K) := by
    dsimp [imageS]
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro k hk
      have hKk : K ≤ k := (Finset.mem_filter.mp hk).2
      congr 1
      omega
    · intro a ha b hb h
      exact hinj (by simpa using ha) (by simpa using hb) h
  have himage_subset : imageS ⊆ Finset.range N := by
    intro j hj
    dsimp [imageS] at hj
    rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
    have hkN : k < N := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    exact Finset.mem_range.mpr (by omega)
  have hfinite_le_range :
      (∑ j ∈ imageS, leftBlockMajorant (j + K)) ≤
        ∑ j ∈ Finset.range N, leftBlockMajorant (j + K) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
      (fun j _hj _hnot => leftBlockMajorant_nonneg (j + K))
  have hshift_summable : Summable fun j : ℕ => leftBlockMajorant (j + K) := by
    exact summable_leftBlockMajorant.comp_injective (fun a b h => by omega)
  have hprefix_le_tsum :
      (∑ j ∈ Finset.range N, leftBlockMajorant (j + K)) ≤
        ∑' j : ℕ, leftBlockMajorant (j + K) := by
    exact hshift_summable.sum_le_tsum (Finset.range N)
      (fun j _hj => leftBlockMajorant_nonneg (j + K))
  calc
    (∑ k ∈ Finset.range N, if K ≤ k then leftBlockMajorant k else 0)
        = ∑ k ∈ s, leftBlockMajorant k := hsum_filter
    _ = ∑ j ∈ imageS, leftBlockMajorant (j + K) := hreindex
    _ ≤ ∑ j ∈ Finset.range N, leftBlockMajorant (j + K) := hfinite_le_range
    _ ≤ ∑' j : ℕ, leftBlockMajorant (j + K) := hprefix_le_tsum

lemma left_half_kernel_tail :
    ∀ ε > 0, ∃ R > 0, ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 (n - 1),
        if R * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
        then erdosWeight n m
        else 0) ≤ ε := by
  intro ε hε
  have htail_tendsto :
      Tendsto (fun K : ℕ => ∑' j : ℕ, leftBlockMajorant (j + K))
        atTop (𝓝 0) :=
    tendsto_sum_nat_add leftBlockMajorant
  have htail_eventually :
      ∀ᶠ K : ℕ in atTop, (∑' j : ℕ, leftBlockMajorant (j + K)) < ε :=
    (tendsto_order.1 htail_tendsto).2 ε hε
  rcases (htail_eventually.and (eventually_ge_atTop (1 : ℕ))).exists with
    ⟨K, hKeps, hKpos⟩
  refine ⟨(K : ℝ), by exact_mod_cast hKpos, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < n := by omega
  calc
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
      then erdosWeight n m
      else 0)
        ≤ ∑ k ∈ Finset.range (numBlocks n),
            if K ≤ k then leftBlockMajorant k else 0 :=
          left_half_tail_sum_le_block_majorants n K hnpos
    _ ≤ ∑' j : ℕ, leftBlockMajorant (j + K) :=
          finite_block_majorant_tail_le_shifted_tsum (numBlocks n) K
    _ ≤ ε := hKeps.le

theorem erdos_kernel_tail :
    ∀ ε > 0, ∃ R > 0, ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 (n - 1),
        if R * Real.sqrt (n : ℝ) ≤ (m : ℝ)
        then erdosWeight n m
        else 0) ≤ ε := by
  intro ε hε
  have hhalfε : 0 < ε / 2 := by linarith
  rcases left_half_kernel_tail (ε / 2) hhalfε with ⟨R, hRpos, hleft⟩
  have hright :
      ∀ᶠ n : ℕ in atTop,
        (∑ m ∈ Finset.Icc 1 (n - 1),
          if n < 2 * m then erdosWeight n m else 0) < ε / 2 :=
    (tendsto_order.1 right_half_kernel_tendsto_zero).2 (ε / 2) hhalfε
  refine ⟨R, hRpos, ?_⟩
  filter_upwards [hleft, hright] with n hnleft hnright
  have hsplit :
      (∑ m ∈ Finset.Icc 1 (n - 1),
        if R * Real.sqrt (n : ℝ) ≤ (m : ℝ)
        then erdosWeight n m
        else 0) ≤
        (∑ m ∈ Finset.Icc 1 (n - 1),
          if R * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
          then erdosWeight n m
          else 0) +
        (∑ m ∈ Finset.Icc 1 (n - 1),
          if n < 2 * m then erdosWeight n m else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro m hm
    by_cases htail : R * Real.sqrt (n : ℝ) ≤ (m : ℝ)
    · by_cases hhalf : 2 * m ≤ n
      · have hnotright : ¬ n < 2 * m := by omega
        simp [htail, hhalf, hnotright]
      · have hrightm : n < 2 * m := by omega
        simp [htail, hhalf, hrightm]
    · have hright_nonneg :
          0 ≤ (if n < 2 * m then erdosWeight n m else 0) := by
        by_cases hr : n < 2 * m
        · have hmI := Finset.mem_Icc.mp hm
          simp [hr, Erdos.erdosWeight_nonneg_of_mem hm]
        · simp [hr]
      by_cases hhalf : 2 * m ≤ n
      · simp [htail, hhalf, hright_nonneg]
      · have hrightm : n < 2 * m := by omega
        simp [htail, hhalf, hrightm, Erdos.erdosWeight_nonneg_of_mem hm]
  linarith

/-!
Targets still to close in this file:

* `erdos_kernel_tail`
* `erdos_kernel_window`
* `erdos_kernel_total`

The proved lemmas above are the block decomposition and the per-block summatory
bound needed for the tail route.
-/

end

end AnalyticCombinatorics.Ch8.Partitions.Erdos.Close
