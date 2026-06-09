import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MuNumModel
import AnalyticCombinatorics.Ch8.Partitions.MassRateApprox2
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentSharp

/-!
# Main-range cross error for the `muNum` two-term expansion

`∑_{1≤m≤⌊n^{2/3}⌋} |erdosWeight n m − modelSummand n m| · |rhoDropModel n m| ≤ K/n`.

The `(erdosWeight − modelSummand)·rhoDropModel` cross term of `muNum − muNumModel`: the kernel error
(`erdosWeight_sub_model_le`) times the two-term `ρ`-drop model, expanded into the six shifted Lambert
moments `M₃,M₄,M₄,M₅,M₅,M₆` and bounded by `sigmaMoment_le_power_sharp`.
ChatGPT-drafted (R-series), recovered from `/tmp/ans_four_main_lemmas.txt` and verified.
-/

noncomputable section

open Filter Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 4000000

private lemma weighted_summable_sigma_exp (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ =>
      if m = 0 then (0:ℝ) else (m:ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))) := by
  have hnorm : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hg := summable_pow_sigma_geometric r (r := Real.exp (-t)) hnorm
  refine hg.congr ?_
  intro m
  rcases eq_or_ne m 0 with h | h
  · subst h
    simp [Sigma.sigmaR]
  · rw [if_neg h, abs_of_pos (Real.exp_pos _)]
    have hpow : Real.exp (-t) ^ m = Real.exp (-t * (m:ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hpow]

private lemma weighted_mainCut_cond :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℕ, 1 ≤ m → m ≤ ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ →
      2 * m ≤ n ∧ 4 * C * (m:ℝ) ^ 2 ≤ Real.sqrt (n:ℝ) ^ 3 := by
  have hCpos : 0 < C := C_pos
  rw [Filter.eventually_atTop]
  refine ⟨max 8 (⌈(4 * C) ^ 6⌉₊ + 1), fun n hn m hm1 hmle => ?_⟩
  have hn8 : 8 ≤ n := le_trans (le_max_left _ _) hn
  have hnC : ⌈(4 * C) ^ 6⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hp23 : (0:ℝ) ≤ (n:ℝ) ^ (2/3 : ℝ) := Real.rpow_nonneg hnpos.le _
  have hmr : (m:ℝ) ≤ (n:ℝ) ^ (2/3 : ℝ) :=
    le_trans (by exact_mod_cast hmle) (Nat.floor_le hp23)
  have hmr0 : (0:ℝ) ≤ (m:ℝ) := by positivity
  have hcubrt : (2:ℝ) ≤ (n:ℝ) ^ (1/3 : ℝ) := by
    have h8 : (8:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn8
    have hmono : (8:ℝ) ^ (1/3 : ℝ) ≤ (n:ℝ) ^ (1/3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h8 (by norm_num)
    have h83 : (8:ℝ) ^ (1/3 : ℝ) = 2 := by
      rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, ← Real.rpow_natCast 2 3,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [h83] at hmono
  have hsixrt : 4 * C ≤ (n:ℝ) ^ (1/6 : ℝ) := by
    have hbase : ((4 * C) ^ 6 : ℝ) ≤ (n:ℝ) := by
      have h1 : ((4 * C) ^ 6 : ℝ) ≤ (⌈(4 * C) ^ 6⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈(4 * C) ^ 6⌉₊ : ℕ):ℝ) ≤ (n:ℝ) := by
        have : ⌈(4 * C) ^ 6⌉₊ ≤ n := by omega
        exact_mod_cast this
      linarith
    have hmono : ((4 * C) ^ 6 : ℝ) ^ (1/6 : ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbase (by norm_num)
    have hid : ((4 * C) ^ 6 : ℝ) ^ (1/6 : ℝ) = 4 * C := by
      rw [← Real.rpow_natCast (4 * C) 6, ← Real.rpow_mul (by positivity)]
      norm_num
    rwa [hid] at hmono
  have hn1 : (n:ℝ) = (n:ℝ) ^ (1/3 : ℝ) * (n:ℝ) ^ (2/3 : ℝ) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hsqrtcube : Real.sqrt (n:ℝ) ^ 3 =
      ((n:ℝ) ^ (2/3 : ℝ)) ^ 2 * (n:ℝ) ^ (1/6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((n:ℝ) ^ (1/2 : ℝ)) 3,
      ← Real.rpow_mul hnpos.le, ← Real.rpow_natCast ((n:ℝ) ^ (2/3 : ℝ)) 2,
      ← Real.rpow_mul hnpos.le, ← Real.rpow_add hnpos]
    norm_num
  refine ⟨?_, ?_⟩
  · have hreal : 2 * (m:ℝ) ≤ (n:ℝ) := by
      calc 2 * (m:ℝ) ≤ 2 * (n:ℝ) ^ (2/3 : ℝ) := by linarith
        _ ≤ (n:ℝ) ^ (1/3 : ℝ) * (n:ℝ) ^ (2/3 : ℝ) := by
            apply mul_le_mul_of_nonneg_right hcubrt hp23
        _ = (n:ℝ) := hn1.symm
    exact_mod_cast hreal
  · have hm2 : (m:ℝ) ^ 2 ≤ ((n:ℝ) ^ (2/3 : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ hmr0 hmr 2
    calc 4 * C * (m:ℝ) ^ 2 ≤ 4 * C * ((n:ℝ) ^ (2/3 : ℝ)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hm2 (by positivity)
      _ ≤ (n:ℝ) ^ (1/6 : ℝ) * ((n:ℝ) ^ (2/3 : ℝ)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hsixrt (by positivity)
      _ = Real.sqrt (n:ℝ) ^ 3 := by rw [hsqrtcube]; ring

private lemma rhoDropModel_abs_le_poly (n m : ℕ) :
    |rhoDropModel n m|
      ≤ 3 * ((m : ℝ) / (2 * Real.sqrt (n : ℝ))
        + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3)) := by
  rw [rhoDropModel, abs_mul, show |(3 : ℝ)| = 3 by norm_num]
  have hnn :
      0 ≤ (m : ℝ) / (2 * Real.sqrt (n : ℝ))
        + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3) := by
    positivity
  rw [abs_of_nonneg hnn]

private theorem weighted_model_error_moment_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (3 * C ^ 2 + 5 * C + 2) *
        ((3 / (2 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) *
            sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
        + (3 / (8 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 3)) *
            sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))
        + (3 / (2 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 2)) *
            sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))
        + (3 / (8 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 4)) *
            sigmaMoment 5 (massLam / Real.sqrt (n:ℝ))
        + (3 / (2 * (n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) *
            sigmaMoment 5 (massLam / Real.sqrt (n:ℝ))
        + (3 / (8 * (n:ℝ) ^ 4 * Real.sqrt (n:ℝ) ^ 3)) *
            sigmaMoment 6 (massLam / Real.sqrt (n:ℝ)))
        ≤ K / (n:ℝ) := by
  obtain ⟨K3, hK3nn, hK3⟩ := sigmaMoment_le_power_sharp 3
  obtain ⟨K4, hK4nn, hK4⟩ := sigmaMoment_le_power_sharp 4
  obtain ⟨K5, hK5nn, hK5⟩ := sigmaMoment_le_power_sharp 5
  obtain ⟨K6, hK6nn, hK6⟩ := sigmaMoment_le_power_sharp 6
  set lam : ℝ := massLam with hlamdef
  set A : ℝ := 3 * C ^ 2 + 5 * C + 2 with hAdef
  set B : ℝ :=
    A *
      (3 * K3 / (2 * lam ^ 5)
      + 3 * K4 / (8 * lam ^ 6)
      + 3 * K4 / (2 * lam ^ 6)
      + 3 * K5 / (8 * lam ^ 7)
      + 3 * K5 / (2 * lam ^ 7)
      + 3 * K6 / (8 * lam ^ 8)) with hBdef
  have hlam0 : 0 < lam := by simpa [hlamdef] using massLam_pos
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    nlinarith [C_pos, sq_nonneg C]
  refine ⟨B + 1, by positivity, ?_⟩
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (1:ℝ) ≤ (n : ℝ) ∧ lam ^ 2 ≤ (n : ℝ) := by
    rw [Filter.eventually_atTop]
    refine ⟨max 1 ⌈lam ^ 2⌉₊, fun n hn => ?_⟩
    refine ⟨by exact_mod_cast (le_trans (le_max_left _ _) hn), ?_⟩
    have h2 : (⌈lam ^ 2⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_trans (le_max_right _ _) hn)
    exact le_trans (Nat.le_ceil _) h2
  filter_upwards [hev] with n hn
  obtain ⟨hn1r, hnlam⟩ := hn
  have hn1 : 1 ≤ n := by exact_mod_cast hn1r
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have hs1 : 1 ≤ Real.sqrt (n:ℝ) := by
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (n:ℝ) := Real.sqrt_le_sqrt hn1r
  set s : ℝ := Real.sqrt (n:ℝ) with hsdef
  have hspos : 0 < s := by simpa [hsdef] using hs0
  have hs1' : 1 ≤ s := by simpa [hsdef] using hs1
  have hs2 : s ^ 2 = (n:ℝ) := by
    rw [hsdef, Real.sq_sqrt hnpos.le]
  set t : ℝ := lam / s with htdef
  have ht0 : 0 < t := by
    rw [htdef]
    positivity
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one hspos, ← Real.sqrt_sq hlam0.le, hsdef]
    exact Real.sqrt_le_sqrt hnlam
  have hM3 := hK3 t ht0 ht1
  have hM4 := hK4 t ht0 ht1
  have hM5 := hK5 t ht0 ht1
  have hM6 := hK6 t ht0 ht1
  have hden_ns : (n:ℝ) ≤ (n:ℝ) * s := by
    nlinarith [hnpos, hs1']
  have c4a_nonneg : 0 ≤ 3 * K4 / (8 * lam ^ 6) := by positivity
  have c5a_nonneg : 0 ≤ 3 * K5 / (8 * lam ^ 7) := by positivity
  have c6_nonneg : 0 ≤ 3 * K6 / (8 * lam ^ 8) := by positivity
  have b3 :
      (3 / (2 * (n:ℝ) ^ 3 * s)) * sigmaMoment 3 t
        ≤ (3 * K3 / (2 * lam ^ 5)) / (n:ℝ) := by
    have hcoef : 0 ≤ 3 / (2 * (n:ℝ) ^ 3 * s) := by positivity
    calc
      (3 / (2 * (n:ℝ) ^ 3 * s)) * sigmaMoment 3 t
          ≤ (3 / (2 * (n:ℝ) ^ 3 * s)) * (K3 / t ^ 5) :=
            mul_le_mul_of_nonneg_left hM3 hcoef
      _ = (3 * K3 / (2 * lam ^ 5)) / (n:ℝ) := by
        rw [htdef, ← hs2]
        field_simp
  have b4a :
      (3 / (8 * (n:ℝ) ^ 3 * s ^ 3)) * sigmaMoment 4 t
        ≤ (3 * K4 / (8 * lam ^ 6)) / (n:ℝ) := by
    have hcoef : 0 ≤ 3 / (8 * (n:ℝ) ^ 3 * s ^ 3) := by positivity
    calc
      (3 / (8 * (n:ℝ) ^ 3 * s ^ 3)) * sigmaMoment 4 t
          ≤ (3 / (8 * (n:ℝ) ^ 3 * s ^ 3)) * (K4 / t ^ 6) :=
            mul_le_mul_of_nonneg_left hM4 hcoef
      _ = (3 * K4 / (8 * lam ^ 6)) / ((n:ℝ) * s) := by
        rw [htdef, ← hs2]
        field_simp
      _ ≤ (3 * K4 / (8 * lam ^ 6)) / (n:ℝ) :=
        div_le_div_of_nonneg_left c4a_nonneg hnpos hden_ns
  have b4b :
      (3 / (2 * (n:ℝ) ^ 3 * s ^ 2)) * sigmaMoment 4 t
        ≤ (3 * K4 / (2 * lam ^ 6)) / (n:ℝ) := by
    have hcoef : 0 ≤ 3 / (2 * (n:ℝ) ^ 3 * s ^ 2) := by positivity
    calc
      (3 / (2 * (n:ℝ) ^ 3 * s ^ 2)) * sigmaMoment 4 t
          ≤ (3 / (2 * (n:ℝ) ^ 3 * s ^ 2)) * (K4 / t ^ 6) :=
            mul_le_mul_of_nonneg_left hM4 hcoef
      _ = (3 * K4 / (2 * lam ^ 6)) / (n:ℝ) := by
        rw [htdef, ← hs2]
        field_simp
  have b5a :
      (3 / (8 * (n:ℝ) ^ 3 * s ^ 4)) * sigmaMoment 5 t
        ≤ (3 * K5 / (8 * lam ^ 7)) / (n:ℝ) := by
    have hcoef : 0 ≤ 3 / (8 * (n:ℝ) ^ 3 * s ^ 4) := by positivity
    calc
      (3 / (8 * (n:ℝ) ^ 3 * s ^ 4)) * sigmaMoment 5 t
          ≤ (3 / (8 * (n:ℝ) ^ 3 * s ^ 4)) * (K5 / t ^ 7) :=
            mul_le_mul_of_nonneg_left hM5 hcoef
      _ = (3 * K5 / (8 * lam ^ 7)) / ((n:ℝ) * s) := by
        rw [htdef, ← hs2]
        field_simp
      _ ≤ (3 * K5 / (8 * lam ^ 7)) / (n:ℝ) :=
        div_le_div_of_nonneg_left c5a_nonneg hnpos hden_ns
  have b5b :
      (3 / (2 * (n:ℝ) ^ 4 * s)) * sigmaMoment 5 t
        ≤ (3 * K5 / (2 * lam ^ 7)) / (n:ℝ) := by
    have hcoef : 0 ≤ 3 / (2 * (n:ℝ) ^ 4 * s) := by positivity
    calc
      (3 / (2 * (n:ℝ) ^ 4 * s)) * sigmaMoment 5 t
          ≤ (3 / (2 * (n:ℝ) ^ 4 * s)) * (K5 / t ^ 7) :=
            mul_le_mul_of_nonneg_left hM5 hcoef
      _ = (3 * K5 / (2 * lam ^ 7)) / (n:ℝ) := by
        rw [htdef, ← hs2]
        field_simp
  have b6 :
      (3 / (8 * (n:ℝ) ^ 4 * s ^ 3)) * sigmaMoment 6 t
        ≤ (3 * K6 / (8 * lam ^ 8)) / (n:ℝ) := by
    have hcoef : 0 ≤ 3 / (8 * (n:ℝ) ^ 4 * s ^ 3) := by positivity
    calc
      (3 / (8 * (n:ℝ) ^ 4 * s ^ 3)) * sigmaMoment 6 t
          ≤ (3 / (8 * (n:ℝ) ^ 4 * s ^ 3)) * (K6 / t ^ 8) :=
            mul_le_mul_of_nonneg_left hM6 hcoef
      _ = (3 * K6 / (8 * lam ^ 8)) / ((n:ℝ) * s) := by
        rw [htdef, ← hs2]
        field_simp
      _ ≤ (3 * K6 / (8 * lam ^ 8)) / (n:ℝ) :=
        div_le_div_of_nonneg_left c6_nonneg hnpos hden_ns
  have hsum :
      (3 / (2 * (n:ℝ) ^ 3 * s)) * sigmaMoment 3 t
        + (3 / (8 * (n:ℝ) ^ 3 * s ^ 3)) * sigmaMoment 4 t
        + (3 / (2 * (n:ℝ) ^ 3 * s ^ 2)) * sigmaMoment 4 t
        + (3 / (8 * (n:ℝ) ^ 3 * s ^ 4)) * sigmaMoment 5 t
        + (3 / (2 * (n:ℝ) ^ 4 * s)) * sigmaMoment 5 t
        + (3 / (8 * (n:ℝ) ^ 4 * s ^ 3)) * sigmaMoment 6 t
        ≤
      (3 * K3 / (2 * lam ^ 5)
        + 3 * K4 / (8 * lam ^ 6)
        + 3 * K4 / (2 * lam ^ 6)
        + 3 * K5 / (8 * lam ^ 7)
        + 3 * K5 / (2 * lam ^ 7)
        + 3 * K6 / (8 * lam ^ 8)) / (n:ℝ) := by
    rw [show
      (3 * K3 / (2 * lam ^ 5)
        + 3 * K4 / (8 * lam ^ 6)
        + 3 * K4 / (2 * lam ^ 6)
        + 3 * K5 / (8 * lam ^ 7)
        + 3 * K5 / (2 * lam ^ 7)
        + 3 * K6 / (8 * lam ^ 8)) / (n:ℝ)
      =
      (3 * K3 / (2 * lam ^ 5)) / (n:ℝ)
        + (3 * K4 / (8 * lam ^ 6)) / (n:ℝ)
        + (3 * K4 / (2 * lam ^ 6)) / (n:ℝ)
        + (3 * K5 / (8 * lam ^ 7)) / (n:ℝ)
        + (3 * K5 / (2 * lam ^ 7)) / (n:ℝ)
        + (3 * K6 / (8 * lam ^ 8)) / (n:ℝ) by ring]
    linarith
  calc
    (3 * C ^ 2 + 5 * C + 2) *
        ((3 / (2 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) *
            sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
        + (3 / (8 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 3)) *
            sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))
        + (3 / (2 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 2)) *
            sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))
        + (3 / (8 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 4)) *
            sigmaMoment 5 (massLam / Real.sqrt (n:ℝ))
        + (3 / (2 * (n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) *
            sigmaMoment 5 (massLam / Real.sqrt (n:ℝ))
        + (3 / (8 * (n:ℝ) ^ 4 * Real.sqrt (n:ℝ) ^ 3)) *
            sigmaMoment 6 (massLam / Real.sqrt (n:ℝ)))
      =
    A *
        ((3 / (2 * (n:ℝ) ^ 3 * s)) * sigmaMoment 3 t
        + (3 / (8 * (n:ℝ) ^ 3 * s ^ 3)) * sigmaMoment 4 t
        + (3 / (2 * (n:ℝ) ^ 3 * s ^ 2)) * sigmaMoment 4 t
        + (3 / (8 * (n:ℝ) ^ 3 * s ^ 4)) * sigmaMoment 5 t
        + (3 / (2 * (n:ℝ) ^ 4 * s)) * sigmaMoment 5 t
        + (3 / (8 * (n:ℝ) ^ 4 * s ^ 3)) * sigmaMoment 6 t) := by
        simp [hAdef, hsdef, htdef, hlamdef]
    _ ≤ A *
      ((3 * K3 / (2 * lam ^ 5)
        + 3 * K4 / (8 * lam ^ 6)
        + 3 * K4 / (2 * lam ^ 6)
        + 3 * K5 / (8 * lam ^ 7)
        + 3 * K5 / (2 * lam ^ 7)
        + 3 * K6 / (8 * lam ^ 8)) / (n:ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hA_nonneg
    _ = B / (n:ℝ) := by
        rw [hBdef]
        ring
    _ ≤ (B + 1) / (n:ℝ) := by
        have hsplit : (B + 1) / (n:ℝ) = B / (n:ℝ) + 1 / (n:ℝ) := by ring
        rw [hsplit]
        exact le_add_of_nonneg_right (by positivity)

theorem main_kernel_error_rhoModel_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (∑ m ∈ Finset.Icc 1 ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊,
        |erdosWeight n m - modelSummand n m| * |rhoDropModel n m|)
      ≤ K / (n:ℝ) := by
  obtain ⟨K, hKpos, hKbound⟩ := weighted_model_error_moment_bound
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [weighted_mainCut_cond, hKbound, Filter.eventually_ge_atTop 1] with n hcond hKb hn1
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have ht0 : 0 < massLam / Real.sqrt (n:ℝ) := div_pos massLam_pos hs0
  set M : ℕ := ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ with hM
  have hstep1 :
      (∑ m ∈ Finset.Icc 1 M,
        |erdosWeight n m - modelSummand n m| * |rhoDropModel n m|)
      ≤
      ∑ m ∈ Finset.Icc 1 M,
        (Sigma.sigmaR m * ((3 * C ^ 2 + 5 * C + 2) *
          Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
          ((m:ℝ) ^ 2 / (n:ℝ) ^ 3
            + (m:ℝ) ^ 3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))
            + (m:ℝ) ^ 4 / (n:ℝ) ^ 4)))
        *
        (3 * ((m : ℝ) / (2 * Real.sqrt (n : ℝ))
          + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))) := by
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmle⟩ := hm
    obtain ⟨h2m, hsmall⟩ := hcond m hm1 hmle
    have herr := erdosWeight_sub_model_le hn1 hm1 h2m hsmall
    have hrho := rhoDropModel_abs_le_poly n m
    exact mul_le_mul herr hrho (abs_nonneg _)
      (by have := sigmaR_nonneg m; have := C_pos; positivity)
  have hrw : ∀ m : ℕ,
      (Sigma.sigmaR m * ((3 * C ^ 2 + 5 * C + 2) *
          Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
          ((m:ℝ) ^ 2 / (n:ℝ) ^ 3
            + (m:ℝ) ^ 3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))
            + (m:ℝ) ^ 4 / (n:ℝ) ^ 4)))
        *
        (3 * ((m : ℝ) / (2 * Real.sqrt (n : ℝ))
          + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3)))
      =
      (3 * C ^ 2 + 5 * C + 2) *
        ((3 / (2 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) *
            ((m:ℝ) ^ 3 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 / (8 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 3)) *
            ((m:ℝ) ^ 4 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 / (2 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 2)) *
            ((m:ℝ) ^ 4 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 / (8 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 4)) *
            ((m:ℝ) ^ 5 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 / (2 * (n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) *
            ((m:ℝ) ^ 5 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 / (8 * (n:ℝ) ^ 4 * Real.sqrt (n:ℝ) ^ 3)) *
            ((m:ℝ) ^ 6 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))) := by
    intro m
    ring
  rw [Finset.sum_congr rfl (fun m _ => hrw m), ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hstep1
  have hfin : ∀ r : ℕ,
      (∑ m ∈ Finset.Icc 1 M,
        (m:ℝ) ^ r * Sigma.sigmaR m *
          Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
      ≤ sigmaMoment r (massLam / Real.sqrt (n:ℝ)) := by
    intro r
    have hge0 : ∀ k : ℕ, 0 ≤
        (if k = 0 then (0:ℝ)
         else (k:ℝ) ^ r * Sigma.sigmaR k *
           Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (k:ℝ))) := by
      intro k
      rcases eq_or_ne k 0 with h | h
      · simp [h]
      · rw [if_neg h]
        exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg k)) (Real.exp_pos _).le
    have hsumm := weighted_summable_sigma_exp r ht0
    have hle := sum_le_hasSum (Finset.Icc 1 M) (fun k _ => hge0 k) hsumm.hasSum
    rw [sigmaMoment]
    refine le_trans (le_of_eq ?_) hle
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [if_neg (by omega : ¬ m = 0)]
  have hmono :
      (3 * C ^ 2 + 5 * C + 2) *
        ((3 / (2 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) *
            (∑ m ∈ Finset.Icc 1 M,
              (m:ℝ) ^ 3 * Sigma.sigmaR m *
                Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 / (8 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 3)) *
            (∑ m ∈ Finset.Icc 1 M,
              (m:ℝ) ^ 4 * Sigma.sigmaR m *
                Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 / (2 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 2)) *
            (∑ m ∈ Finset.Icc 1 M,
              (m:ℝ) ^ 4 * Sigma.sigmaR m *
                Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 / (8 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 4)) *
            (∑ m ∈ Finset.Icc 1 M,
              (m:ℝ) ^ 5 * Sigma.sigmaR m *
                Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 / (2 * (n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) *
            (∑ m ∈ Finset.Icc 1 M,
              (m:ℝ) ^ 5 * Sigma.sigmaR m *
                Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
        + (3 / (8 * (n:ℝ) ^ 4 * Real.sqrt (n:ℝ) ^ 3)) *
            (∑ m ∈ Finset.Icc 1 M,
              (m:ℝ) ^ 6 * Sigma.sigmaR m *
                Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
      ≤
      (3 * C ^ 2 + 5 * C + 2) *
        ((3 / (2 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) *
            sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
        + (3 / (8 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 3)) *
            sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))
        + (3 / (2 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 2)) *
            sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))
        + (3 / (8 * (n:ℝ) ^ 3 * Real.sqrt (n:ℝ) ^ 4)) *
            sigmaMoment 5 (massLam / Real.sqrt (n:ℝ))
        + (3 / (2 * (n:ℝ) ^ 4 * Real.sqrt (n:ℝ))) *
            sigmaMoment 5 (massLam / Real.sqrt (n:ℝ))
        + (3 / (8 * (n:ℝ) ^ 4 * Real.sqrt (n:ℝ) ^ 3)) *
            sigmaMoment 6 (massLam / Real.sqrt (n:ℝ))) := by
    have hcoef : 0 ≤ 3 * C ^ 2 + 5 * C + 2 := by nlinarith [C_pos, sq_nonneg C]
    apply mul_le_mul_of_nonneg_left _ hcoef
    gcongr <;> [exact hfin 3; exact hfin 4; exact hfin 4; exact hfin 5; exact hfin 5; exact hfin 6]
  exact le_trans hstep1 (le_trans hmono hKb)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
