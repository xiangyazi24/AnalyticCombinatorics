import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MuNumModel
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentSharp

/-!
# Second cross error for the `muNum` two-term expansion

`∑_{1≤m≤⌊n^{2/3}⌋} |modelSummand n m| · |rhoDrop n m − rhoDropModel n m| ≤ K/n`.

The `modelSummand·(rhoDrop − rhoDropModel)` cross term: the `modelSummand` magnitude
(`|modelSummand| ≤ (1/n)g₀ + (1/n²)g₁ + (C/(8n²√n))g₂`) times the second-order `ρ`-drop error
(`|rhoDrop − rhoDropModel| ≤ 3m³/(√n)⁵`, `rhoDrop_sub_model_le`), expanded into the three shifted
Lambert moments `M₃,M₄,M₅` and bounded by `sigmaMoment_le_power_sharp`.  Sibling of
`main_kernel_error_rhoModel_le`, one fewer kernel factor.  Opus-authored.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Summability of the guarded Lambert summand `m^r σ(m) e^{−tm}` (`t>0`). -/
private lemma mre_summable_sigma_exp (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ =>
      if m = 0 then (0:ℝ) else (m:ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))) := by
  have hnorm : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hg := summable_pow_sigma_geometric r (r := Real.exp (-t)) hnorm
  refine hg.congr ?_
  intro m
  rcases eq_or_ne m 0 with h | h
  · subst h; simp [Sigma.sigmaR]
  · rw [if_neg h, abs_of_pos (Real.exp_pos _)]
    have hpow : Real.exp (-t) ^ m = Real.exp (-t * (m:ℝ)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hpow]

/-- `|modelSummand|` magnitude bound (triangle inequality on its three terms). -/
private lemma mre_abs_modelSummand_le (n m : ℕ) :
    |modelSummand n m|
      ≤ (1 / (n:ℝ)) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 0 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (1 / (n:ℝ) ^ 2) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 1 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))) := by
  have hCpos : 0 < C := C_pos
  rcases eq_or_ne m 0 with h | h
  · subst h; simp [modelSummand]
  · rw [modelSummand, if_neg h, if_neg h, if_neg h, if_neg h]
    rw [abs_mul, abs_mul, abs_of_nonneg (sigmaR_nonneg m), abs_of_pos (Real.exp_pos _)]
    have hcoef : |1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 - C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))|
        ≤ 1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 + C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ)) := by
      have h1 : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
      have h2 : (0:ℝ) ≤ (m:ℝ) / (n:ℝ) ^ 2 := by positivity
      have h3 : (0:ℝ) ≤ C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ)) := by positivity
      rw [abs_le]; constructor <;> linarith
    calc Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
            |1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 - C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))|
        ≤ Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
            (1 / (n:ℝ) + (m:ℝ) / (n:ℝ) ^ 2 + C * (m:ℝ) ^ 2 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) :=
          mul_le_mul_of_nonneg_left hcoef
            (mul_nonneg (sigmaR_nonneg m) (Real.exp_pos _).le)
      _ = _ := by ring

/-- `|rhoDrop − rhoDropModel|` magnitude (from `rhoDrop_sub_model_le`, abs form). -/
private lemma mre_abs_rhoDrop_sub_le {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    |rhoDrop n m - rhoDropModel n m| ≤ 3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 :=
  rhoDrop_sub_model_le hn hm

/-- The three-moment bound for the second cross error. -/
private theorem mre_moment_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ((3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
        + (3 / ((n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))
        + (3 * C / (8 * (n:ℝ) ^ 5)) * sigmaMoment 5 (massLam / Real.sqrt (n:ℝ)))
        ≤ K / (n:ℝ) := by
  obtain ⟨K3, hK3nn, hK3⟩ := sigmaMoment_le_power_sharp 3
  obtain ⟨K4, hK4nn, hK4⟩ := sigmaMoment_le_power_sharp 4
  obtain ⟨K5, hK5nn, hK5⟩ := sigmaMoment_le_power_sharp 5
  set lam : ℝ := massLam with hlamdef
  have hlam0 : 0 < lam := by simpa [hlamdef] using massLam_pos
  set B : ℝ := 3 * K3 / lam ^ 5 + 3 * K4 / lam ^ 6 + 3 * C * K5 / (8 * lam ^ 7) with hBdef
  refine ⟨B + 1, by have := C_pos; positivity, ?_⟩
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (1:ℝ) ≤ (n : ℝ) ∧ lam ^ 2 ≤ (n : ℝ) := by
    rw [Filter.eventually_atTop]
    refine ⟨max 1 ⌈lam ^ 2⌉₊, fun n hn => ?_⟩
    refine ⟨by exact_mod_cast (le_trans (le_max_left _ _) hn), ?_⟩
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast (le_trans (le_max_right _ _) hn))
  filter_upwards [hev] with n hn
  obtain ⟨hn1r, hnlam⟩ := hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have hs1 : 1 ≤ Real.sqrt (n:ℝ) := by
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (n:ℝ) := Real.sqrt_le_sqrt hn1r
  set s : ℝ := Real.sqrt (n:ℝ) with hsdef
  have hspos : 0 < s := by simpa [hsdef] using hs0
  have hs1' : 1 ≤ s := by simpa [hsdef] using hs1
  have hs2 : s ^ 2 = (n:ℝ) := by rw [hsdef, Real.sq_sqrt hnpos.le]
  set t : ℝ := lam / s with htdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one hspos, ← Real.sqrt_sq hlam0.le, hsdef]
    exact Real.sqrt_le_sqrt hnlam
  have hM3 := hK3 t ht0 ht1
  have hM4 := hK4 t ht0 ht1
  have hM5 := hK5 t ht0 ht1
  have hden_ns : (n:ℝ) ≤ (n:ℝ) * s := by nlinarith [hnpos, hs1']
  have c4_nonneg : 0 ≤ 3 * K4 / lam ^ 6 := by positivity
  have c5_nonneg : 0 ≤ 3 * C * K5 / (8 * lam ^ 7) := by
    have := C_pos; positivity
  have b3 :
      (3 / ((n:ℝ) ^ 3 * s)) * sigmaMoment 3 t ≤ (3 * K3 / lam ^ 5) / (n:ℝ) := by
    have hcoef : 0 ≤ 3 / ((n:ℝ) ^ 3 * s) := by positivity
    calc (3 / ((n:ℝ) ^ 3 * s)) * sigmaMoment 3 t
        ≤ (3 / ((n:ℝ) ^ 3 * s)) * (K3 / t ^ 5) := mul_le_mul_of_nonneg_left hM3 hcoef
      _ = (3 * K3 / lam ^ 5) / (n:ℝ) := by rw [htdef, ← hs2]; field_simp
  have b4 :
      (3 / ((n:ℝ) ^ 4 * s)) * sigmaMoment 4 t ≤ (3 * K4 / lam ^ 6) / (n:ℝ) := by
    have hcoef : 0 ≤ 3 / ((n:ℝ) ^ 4 * s) := by positivity
    calc (3 / ((n:ℝ) ^ 4 * s)) * sigmaMoment 4 t
        ≤ (3 / ((n:ℝ) ^ 4 * s)) * (K4 / t ^ 6) := mul_le_mul_of_nonneg_left hM4 hcoef
      _ = (3 * K4 / lam ^ 6) / ((n:ℝ) * s) := by rw [htdef, ← hs2]; field_simp
      _ ≤ (3 * K4 / lam ^ 6) / (n:ℝ) := div_le_div_of_nonneg_left c4_nonneg hnpos hden_ns
  have b5 :
      (3 * C / (8 * (n:ℝ) ^ 5)) * sigmaMoment 5 t ≤ (3 * C * K5 / (8 * lam ^ 7)) / (n:ℝ) := by
    have hCpos := C_pos
    have hcoef : 0 ≤ 3 * C / (8 * (n:ℝ) ^ 5) := by positivity
    calc (3 * C / (8 * (n:ℝ) ^ 5)) * sigmaMoment 5 t
        ≤ (3 * C / (8 * (n:ℝ) ^ 5)) * (K5 / t ^ 7) := mul_le_mul_of_nonneg_left hM5 hcoef
      _ = (3 * C * K5 / (8 * lam ^ 7)) / ((n:ℝ) * s) := by rw [htdef, ← hs2]; field_simp
      _ ≤ (3 * C * K5 / (8 * lam ^ 7)) / (n:ℝ) := div_le_div_of_nonneg_left c5_nonneg hnpos hden_ns
  have hsum :
      (3 * K3 / lam ^ 5) / (n:ℝ) + (3 * K4 / lam ^ 6) / (n:ℝ)
        + (3 * C * K5 / (8 * lam ^ 7)) / (n:ℝ) = B / (n:ℝ) := by
    rw [hBdef]; ring
  calc
    (3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
        + (3 / ((n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))
        + (3 * C / (8 * (n:ℝ) ^ 5)) * sigmaMoment 5 (massLam / Real.sqrt (n:ℝ))
      = (3 / ((n:ℝ) ^ 3 * s)) * sigmaMoment 3 t
        + (3 / ((n:ℝ) ^ 4 * s)) * sigmaMoment 4 t
        + (3 * C / (8 * (n:ℝ) ^ 5)) * sigmaMoment 5 t := by rw [hsdef, htdef, hlamdef]
    _ ≤ (3 * K3 / lam ^ 5) / (n:ℝ) + (3 * K4 / lam ^ 6) / (n:ℝ)
          + (3 * C * K5 / (8 * lam ^ 7)) / (n:ℝ) := by linarith [b3, b4, b5]
    _ = B / (n:ℝ) := hsum
    _ ≤ (B + 1) / (n:ℝ) := by
        rw [show (B + 1) / (n:ℝ) = B / (n:ℝ) + 1 / (n:ℝ) by ring]
        exact le_add_of_nonneg_right (by positivity)

/-- **Second cross error**: `∑_{1≤m≤⌊n^{2/3}⌋} |modelSummand|·|rhoDrop − rhoDropModel| ≤ K/n`. -/
theorem main_model_rho_error_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (∑ m ∈ Finset.Icc 1 ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊,
        |modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
      ≤ K / (n:ℝ) := by
  obtain ⟨K, hKpos, hKbound⟩ := mre_moment_bound
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [hKbound, Filter.eventually_ge_atTop 1] with n hKb hn1
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have ht0 : 0 < massLam / Real.sqrt (n:ℝ) := div_pos massLam_pos hs0
  set M : ℕ := ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ with hM
  have hMn : M ≤ n := by
    rw [hM]
    have hle : (n:ℝ) ^ (2/3 : ℝ) ≤ (n:ℝ) := by
      have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      calc (n:ℝ) ^ (2/3 : ℝ) ≤ (n:ℝ) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ = (n:ℝ) := by rw [Real.rpow_one]
    calc ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ ≤ ⌊(n:ℝ)⌋₊ := Nat.floor_mono hle
      _ = n := Nat.floor_natCast n
  -- step 1: pointwise bound  |modelSummand|·|drop-err| ≤ (abs bound)·(3m³/√n⁵)
  have hstep1 :
      (∑ m ∈ Finset.Icc 1 M, |modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
      ≤ ∑ m ∈ Finset.Icc 1 M,
          (((1 / (n:ℝ)) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 0 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
            + (1 / (n:ℝ) ^ 2) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 1 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
            + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
          * (3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5)) := by
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmle⟩ := hm
    have hmn : m ≤ n := le_trans hmle hMn
    have habs := mre_abs_modelSummand_le n m
    have hrho := mre_abs_rhoDrop_sub_le hn1 hmn
    exact mul_le_mul habs hrho (abs_nonneg _) (le_trans (abs_nonneg _) habs)
  -- step 2: rearrange each summand into the three moment summands
  have hrw : ∀ m : ℕ,
      (((1 / (n:ℝ)) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 0 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (1 / (n:ℝ) ^ 2) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 1 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
      * (3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5))
      = (3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 3 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 / ((n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 4 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 * C / (8 * (n:ℝ) ^ 5)) * (if m = 0 then (0:ℝ) else (m:ℝ) ^ 5 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))) := by
    intro m
    rcases eq_or_ne m 0 with h | h
    · subst h; simp
    · rw [if_neg h, if_neg h, if_neg h, if_neg h, if_neg h, if_neg h]
      set s := Real.sqrt (n:ℝ) with hsd
      have hs2 : s ^ 2 = (n:ℝ) := Real.sq_sqrt hnpos.le
      have hsne : s ≠ 0 := by rw [hsd]; exact hs0.ne'
      rw [← hs2]
      field_simp
  rw [Finset.sum_congr rfl (fun m _ => hrw m), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hstep1
  -- step 3: each finite divisor sum ≤ the full Lambert moment
  have hfin : ∀ r : ℕ,
      (∑ m ∈ Finset.Icc 1 M,
        (if m = 0 then (0:ℝ) else (m:ℝ) ^ r * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
      ≤ sigmaMoment r (massLam / Real.sqrt (n:ℝ)) := by
    intro r
    have hge0 : ∀ k : ℕ, 0 ≤
        (if k = 0 then (0:ℝ) else (k:ℝ) ^ r * Sigma.sigmaR k * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (k:ℝ))) := by
      intro k
      rcases eq_or_ne k 0 with h | h
      · simp [h]
      · rw [if_neg h]
        exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg k)) (Real.exp_pos _).le
    have hsumm := mre_summable_sigma_exp r ht0
    have hle := sum_le_hasSum (Finset.Icc 1 M) (fun k _ => hge0 k) hsumm.hasSum
    rw [sigmaMoment]
    refine le_trans (le_of_eq ?_) hle
    apply Finset.sum_congr rfl
    intro m _; rfl
  -- step 4: combine
  have hmono :
      (3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * (∑ m ∈ Finset.Icc 1 M, (if m = 0 then (0:ℝ) else (m:ℝ) ^ 3 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
        + (3 / ((n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) * (∑ m ∈ Finset.Icc 1 M, (if m = 0 then (0:ℝ) else (m:ℝ) ^ 4 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
        + (3 * C / (8 * (n:ℝ) ^ 5)) * (∑ m ∈ Finset.Icc 1 M, (if m = 0 then (0:ℝ) else (m:ℝ) ^ 5 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
      ≤ (3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
        + (3 / ((n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))
        + (3 * C / (8 * (n:ℝ) ^ 5)) * sigmaMoment 5 (massLam / Real.sqrt (n:ℝ)) := by
    have hC := C_pos
    gcongr <;> [exact hfin 3; exact hfin 4; exact hfin 5]
  exact le_trans hstep1 (le_trans hmono hKb)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
