import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernel
import AnalyticCombinatorics.Ch8.Partitions.KernelBarriers
import AnalyticCombinatorics.Ch8.Partitions.RenewalSpine
import AnalyticCombinatorics.Ch8.Partitions.RenewalHitPot
import AnalyticCombinatorics.Ch8.Partitions.DefectSummable
import AnalyticCombinatorics.Ch8.Partitions.MassRateApprox2
import AnalyticCombinatorics.Ch8.Partitions.BarrierLimit

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

set_option maxHeartbeats 1000000 in
/-- **Residual is block-summable** (`herr`): `|dres n| ≤ errFn (rnk n)` eventually, with `errFn ≥ 0`
summable.  This is the "small summable residual" input both endgame routes need.  Scale via
`rnk_sqrt_bounds`: `(j/3)² ≤ n < ((j+1)/3)²`, `1/n ≤ 9/j² ≤ 36/(j+1)²`, `n² < ((j+1)/3)⁴ ≤ (16/81)j⁴`,
`e^{−C√n} ≤ e^{−Cj/3}`. -/
theorem dres_block_bound :
    ∃ errFn : ℕ → ℝ, (∀ j, 0 ≤ errFn j) ∧ Summable errFn ∧
      ∀ᶠ n in Filter.atTop, |dres n| ≤ errFn (rnk n) := by
  obtain ⟨M, hMpos, hMev⟩ := u_limsup_finite
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  have hCpos := C_pos
  refine ⟨fun j => 72 * M * K / ((j : ℝ) + 1) ^ 2
      + (32 / 81) * (j : ℝ) ^ 4 * Real.exp (-(C / 3) * (j : ℝ)), ?_, ?_, ?_⟩
  · intro j; have hM := hMpos.le; have hK := hKpos.le; positivity
  · apply Summable.add
    · exact summable_const_div_succ_sq (72 * M * K)
    · have h := summable_pow_mul_exp_neg (show (0 : ℝ) < C / 3 by linarith) 4
      exact (h.mul_left (32 / 81)).congr (fun j => by ring)
  · have hhalf : ∀ᶠ n : ℕ in Filter.atTop, K / (n : ℝ) ≤ 1 / 2 := by
      have htend : Filter.Tendsto (fun n : ℕ => K / (n : ℝ)) Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
      exact htend.eventually_le_const (by norm_num)
    filter_upwards [hMev, hKev, hhalf, Filter.eventually_ge_atTop 2]
      with n hMn hKn hhalfn hn2
    have hn1 : (1 : ℕ) ≤ n := by omega
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    -- kernelMass ≥ 1/2 > 0
    obtain ⟨hSlo, _⟩ := abs_le.1 hKn
    have hSge : (1 : ℝ) / 2 ≤ kernelMass n := by linarith [hhalfn]
    have hSpos : (0 : ℝ) < kernelMass n := by linarith
    -- nonneg facts
    have hu0 : 0 ≤ u n := (u_pos hn1).le
    have hb0 : 0 ≤ boundaryTerm n := boundaryTerm_nonneg n
    have hSabs : |kernelMass n - 1| ≤ K / (n : ℝ) := hKn
    -- sqrt/scale bounds
    obtain ⟨hjle, hjlt⟩ := rnk_sqrt_bounds n
    have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hnR
    have hj1 : (1 : ℝ) ≤ (rnk n : ℝ) := by
      have h3 : (3 : ℝ) ≤ (rnk n : ℝ) := by
        have : (3 : ℝ) ≤ 3 * Real.sqrt (n : ℝ) := by linarith
        calc (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
          _ ≤ (rnk n : ℝ) := by
              rw [Nat.cast_le]; unfold rnk; exact Nat.le_floor (by push_cast; linarith)
      linarith
    have hjpos : (0 : ℝ) < (rnk n : ℝ) := by linarith
    have hsqrt_lb : (rnk n : ℝ) / 3 ≤ Real.sqrt (n : ℝ) := by linarith
    have hsqrt_ub : Real.sqrt (n : ℝ) < ((rnk n : ℝ) + 1) / 3 := by linarith
    have hsqsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
    -- n ≥ (j/3)²  ⟹  1/n ≤ 9/j²
    have hn_lb : ((rnk n : ℝ) / 3) ^ 2 ≤ (n : ℝ) := by
      rw [← hsqsq]; apply pow_le_pow_left₀ (by positivity) hsqrt_lb
    have hinv : (1 : ℝ) / (n : ℝ) ≤ 9 / (rnk n : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hnpos (by positivity)]
      nlinarith [hn_lb, hjpos]
    -- n < ((j+1)/3)²  ⟹  n² < ((j+1)/3)⁴
    have hn_ub : (n : ℝ) < (((rnk n : ℝ) + 1) / 3) ^ 2 := by
      rw [← hsqsq]; apply pow_lt_pow_left₀ hsqrt_ub hsqrtpos.le (by norm_num)
    have hnsq_ub : (n : ℝ) ^ 2 < (((rnk n : ℝ) + 1) / 3) ^ 4 := by
      have h4 : (((rnk n : ℝ) + 1) / 3) ^ 4 = ((((rnk n : ℝ) + 1) / 3) ^ 2) ^ 2 := by ring
      rw [h4]; apply pow_lt_pow_left₀ hn_ub (by positivity) (by norm_num)
    -- e^{−C√n} ≤ e^{−Cj/3}
    have hexp : Real.exp (-C * Real.sqrt (n : ℝ)) ≤ Real.exp (-(C / 3) * (rnk n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have : (C / 3) * (rnk n : ℝ) ≤ C * Real.sqrt (n : ℝ) := by nlinarith [hsqrt_lb, hCpos.le]
      linarith
    -- σ(n) ≤ n²  ⟹  boundaryTerm n ≤ n² e^{−C√n}
    have hb_ub : boundaryTerm n ≤ (n : ℝ) ^ 2 * Real.exp (-C * Real.sqrt (n : ℝ)) := by
      unfold boundaryTerm
      apply mul_le_mul_of_nonneg_right (sigmaR_le_square hn1) (Real.exp_nonneg _)
    -- the dres bound
    rw [dres_eq (by omega)]
    have hform : |u n - (u n - boundaryTerm n) / kernelMass n|
        = |u n * (kernelMass n - 1) + boundaryTerm n| / kernelMass n := by
      have hinside : u n - (u n - boundaryTerm n) / kernelMass n
          = (u n * (kernelMass n - 1) + boundaryTerm n) / kernelMass n := by
        field_simp; ring
      rw [hinside, abs_div, abs_of_pos hSpos]
    rw [hform]
    -- numerator ≤ M·(K/n) + boundaryTerm n
    have hnum : |u n * (kernelMass n - 1) + boundaryTerm n| ≤ M * (K / (n : ℝ)) + boundaryTerm n := by
      calc |u n * (kernelMass n - 1) + boundaryTerm n|
          ≤ |u n * (kernelMass n - 1)| + |boundaryTerm n| := abs_add_le _ _
        _ = u n * |kernelMass n - 1| + boundaryTerm n := by
            rw [abs_mul, abs_of_nonneg hu0, abs_of_nonneg hb0]
        _ ≤ M * (K / (n : ℝ)) + boundaryTerm n := by
            have hstep : u n * |kernelMass n - 1| ≤ M * (K / (n : ℝ)) :=
              le_trans (mul_le_mul_of_nonneg_left hSabs hu0)
                (mul_le_mul_of_nonneg_right hMn (by positivity))
            linarith [hstep]
    -- divide by S ≥ 1/2 and bound by errFn
    have hdiv : |u n * (kernelMass n - 1) + boundaryTerm n| / kernelMass n
        ≤ 2 * (M * (K / (n : ℝ)) + boundaryTerm n) := by
      rw [div_le_iff₀ hSpos]
      have hmkb : 0 ≤ M * (K / (n : ℝ)) + boundaryTerm n :=
        add_nonneg (mul_nonneg hMpos.le (div_nonneg hKpos.le hnpos.le)) hb0
      nlinarith [hnum, hSge, hmkb]
    refine le_trans hdiv ?_
    -- 2(MK/n + b) ≤ errFn (rnk n)
    have hMK : 0 ≤ M * K := by positivity
    have hinv2 : (1 : ℝ) / (n : ℝ) ≤ 36 / ((rnk n : ℝ) + 1) ^ 2 := by
      have h9 : (9 : ℝ) / (rnk n : ℝ) ^ 2 ≤ 36 / ((rnk n : ℝ) + 1) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hj1]
      linarith [hinv, h9]
    have ht1 : 2 * (M * (K / (n : ℝ))) ≤ 72 * M * K / ((rnk n : ℝ) + 1) ^ 2 := by
      have hrw : 2 * (M * (K / (n : ℝ))) = 2 * M * K * (1 / (n : ℝ)) := by ring
      rw [hrw]
      calc 2 * M * K * (1 / (n : ℝ))
          ≤ 2 * M * K * (36 / ((rnk n : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_left hinv2 (by positivity)
        _ = 72 * M * K / ((rnk n : ℝ) + 1) ^ 2 := by ring
    have ht2 : 2 * boundaryTerm n ≤ (32 / 81) * (rnk n : ℝ) ^ 4 * Real.exp (-(C / 3) * (rnk n : ℝ)) := by
      have hb2 : boundaryTerm n ≤ (((rnk n : ℝ) + 1) / 3) ^ 4 * Real.exp (-(C / 3) * (rnk n : ℝ)) := by
        calc boundaryTerm n ≤ (n : ℝ) ^ 2 * Real.exp (-C * Real.sqrt (n : ℝ)) := hb_ub
          _ ≤ (((rnk n : ℝ) + 1) / 3) ^ 4 * Real.exp (-(C / 3) * (rnk n : ℝ)) := by
              apply mul_le_mul (le_of_lt hnsq_ub) hexp (Real.exp_nonneg _) (by positivity)
      have hpoly : (((rnk n : ℝ) + 1) / 3) ^ 4 ≤ (16 / 81) * (rnk n : ℝ) ^ 4 := by
        have hle : (rnk n : ℝ) + 1 ≤ 2 * (rnk n : ℝ) := by linarith [hj1]
        have hexp4 : ((rnk n : ℝ) + 1) ^ 4 ≤ 16 * (rnk n : ℝ) ^ 4 := by
          nlinarith [pow_le_pow_left₀ (show (0:ℝ) ≤ (rnk n : ℝ) + 1 by positivity) hle 4]
        rw [div_pow, show (3:ℝ) ^ 4 = 81 by norm_num]
        linarith [hexp4]
      calc 2 * boundaryTerm n
          ≤ 2 * ((((rnk n : ℝ) + 1) / 3) ^ 4 * Real.exp (-(C / 3) * (rnk n : ℝ))) := by linarith
        _ ≤ 2 * ((16 / 81) * (rnk n : ℝ) ^ 4 * Real.exp (-(C / 3) * (rnk n : ℝ))) := by
            gcongr
        _ = (32 / 81) * (rnk n : ℝ) ^ 4 * Real.exp (-(C / 3) * (rnk n : ℝ)) := by ring
    linarith [ht1, ht2]

/-- The fixed window `(√n, 2√n]` carries a uniform positive kernel mass (the `a₀=1` instance of
`erdos_kernel_fixed_window_pos`, exposed explicitly so window steps `m>√n` apply `window_rank_drop`). -/
lemma kernelWindow_one_two_pos :
    ∃ ν : ℝ, 0 < ν ∧ ∀ᶠ n : ℕ in atTop, ν ≤ kernelWindow 1 2 n := by
  have hC := C_pos
  have hIpos : 0 < Model.modelIntegral C 1 2 := by
    rw [Model.modelIntegral]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · have hc : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
        have h1 : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y :=
          continuous_const.mul continuous_id
        have h2 : Continuous fun y : ℝ => Real.exp (-(C / 2) * y) :=
          Real.continuous_exp.comp (continuous_const.mul continuous_id)
        exact h1.mul h2
      exact hc.intervalIntegrable _ _
    · intro y hy
      have hy1 : (1 : ℝ) < y := hy.1
      have hπ : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
      have he : (0 : ℝ) < Real.exp (-(C / 2) * y) := Real.exp_pos _
      nlinarith [mul_pos (mul_pos hπ (by linarith : (0:ℝ) < y)) he]
    · norm_num
  refine ⟨Model.modelIntegral C 1 2 / 2, by positivity, ?_⟩
  have hwin := Model.erdos_kernel_window (a := 1) (b := 2) zero_le_one one_lt_two
  have hev := (tendsto_order.1 hwin).1 (Model.modelIntegral C 1 2 / 2) (by linarith)
  filter_upwards [hev] with n hn
  exact hn.le

/-- **Leave probability** (`hP_leave`): a uniform positive mass of the normalized kernel goes to
strictly lower rank.  Window steps `m ∈ (√n, 2√n]` carry mass `≥ ν` (`kernelWindow_one_two_pos`) and
drop rank (`window_rank_drop`); dividing by `kernelMass n ≤ 2` gives `≥ ν/2`. -/
theorem hP_leave_partition :
    ∃ μ : ℝ, 0 < μ ∧ ∀ᶠ n : ℕ in atTop,
      μ ≤ ∑ k ∈ (Finset.range n).filter (fun k => rnk k < rnk n), Pker n k := by
  obtain ⟨ν, hνpos, hνmass⟩ := kernelWindow_one_two_pos
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  have hone : ∀ᶠ n : ℕ in atTop, K / (n : ℝ) ≤ 1 / 2 := by
    have htend : Filter.Tendsto (fun n : ℕ => K / (n : ℝ)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    exact htend.eventually_le_const (by norm_num)
  refine ⟨ν / 2, by positivity, ?_⟩
  filter_upwards [hνmass, hKev, hone, Filter.eventually_ge_atTop 2] with n hνn hKn hKn1 hn2
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨hSlo, hSup⟩ := abs_le.1 hKn
  have hS2 : kernelMass n ≤ 2 := by linarith [hSup, hKn1]
  have hSge : (1 : ℝ) / 2 ≤ kernelMass n := by linarith [hSlo, hKn1]
  have hSpos : (0 : ℝ) < kernelMass n := by linarith
  -- main inequality: kernelWindow 1 2 n / kernelMass n ≤ leave-sum
  have hkey : kernelWindow 1 2 n / kernelMass n
      ≤ ∑ k ∈ (Finset.range n).filter (fun k => rnk k < rnk n), Pker n k := by
    -- reindex the window mass to predecessor coordinate and embed into the rank-drop filter
    have hreflect : kernelWindow 1 2 n / kernelMass n
        = ∑ k ∈ Finset.Icc 1 (n - 1),
            (if 1 * Real.sqrt (n : ℝ) < ((n - k : ℕ) : ℝ)
                ∧ ((n - k : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ)
              then Pker n k else 0) := by
      rw [kernelWindow, ← sum_Icc_reflect_sub n
        (fun m => if 1 * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ 2 * Real.sqrt (n : ℝ)
          then erdosWeight n m else 0), Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      by_cases hw : 1 * Real.sqrt (n : ℝ) < ((n - k : ℕ) : ℝ)
          ∧ ((n - k : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ)
      · rw [if_pos hw, if_pos hw]
        unfold Pker; rw [if_pos ⟨hk.1, by omega⟩]
      · rw [if_neg hw, if_neg hw, zero_div]
    rw [hreflect, ← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hk1, hk2⟩, hw1, hw2⟩ := hk
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have hd := window_rank_drop (n := n) (m := n - k) (by omega) (by omega) (by
        rw [one_mul] at hw1; exact hw1)
      rwa [Nat.sub_sub_self (by omega : k ≤ n)] at hd
    · intro k _ _; exact Pker_nonneg n k
  refine le_trans ?_ hkey
  rw [le_div_iff₀ hSpos]
  nlinarith [hνn, hS2, hνpos]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
