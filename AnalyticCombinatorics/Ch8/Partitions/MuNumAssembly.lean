import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MuNumExpansion
import AnalyticCombinatorics.Ch8.Partitions.MuNumMainError
import AnalyticCombinatorics.Ch8.Partitions.MuNumModelRhoError
import AnalyticCombinatorics.Ch8.Partitions.WeightedTail

/-!
# Assembly of the two-term expansion for `muNum`

This file only assembles the banked estimates:

* the infinite model two-term expansion,
* the two main-range errors,
* the weighted Erdős far tail,
* and a local model-product tail.
-/

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

private lemma assembly_abs_add_three_le (a b c : ℝ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 := abs_add_le (a + b) c
  have h2 := abs_add_le a b
  nlinarith

private lemma assembly_abs_add_four_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := assembly_abs_add_three_le a b c
  nlinarith

private lemma assembly_summable_sigma_exp (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ =>
      if m = 0 then (0 : ℝ) else
        (m : ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))) := by
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
    have hpow : Real.exp (-t) ^ m = Real.exp (-t * (m : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hpow]

/-- The model Lambert tail after the cutoff `M`. -/
private def assemblyGTail (n M k m : ℕ) : ℝ :=
  if m ≤ M then (0 : ℝ)
  else if m = 0 then (0 : ℝ)
  else (m : ℝ) ^ k * Sigma.sigmaR m *
    Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ))

private lemma assemblyGTail_nonneg (n M k m : ℕ) :
    0 ≤ assemblyGTail n M k m := by
  rw [assemblyGTail]
  split
  · rfl
  · split
    · rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le

private lemma assembly_summable_gTail (n M k : ℕ)
    {t : ℝ} (ht : massLam / Real.sqrt (n : ℝ) = t) (htp : 0 < t) :
    Summable (fun m => assemblyGTail n M k m) := by
  refine Summable.of_nonneg_of_le (assemblyGTail_nonneg n M k) (fun m => ?_)
    (assembly_summable_sigma_exp k htp)
  rw [assemblyGTail, ← ht]
  split
  · split
    · rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
  · exact le_rfl

private lemma assemblyGTail_eq_bare (n M k : ℕ) :
    (∑' m : ℕ, assemblyGTail n M k m)
      = ∑' m : ℕ, (if m ≤ M then (0 : ℝ)
          else (m : ℝ) ^ k * Sigma.sigmaR m *
            Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ))) := by
  apply tsum_congr
  intro m
  rw [assemblyGTail]
  rcases le_or_gt m M with h | h
  · rw [if_pos h, if_pos h]
  · rw [if_neg (not_le.mpr h), if_neg (not_le.mpr h), if_neg (by omega : ¬ m = 0)]

/-- Geometric extraction for the divisor-weighted Lambert tail. -/
private lemma assembly_sigma_geom_tail_le (k : ℕ) {t : ℝ} (ht : 0 < t) (M : ℕ) :
    (∑' m : ℕ, (if m ≤ M then (0 : ℝ)
        else (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))))
      ≤ Real.exp (-(t / 2) * (M : ℝ)) * sigmaMoment k (t / 2) := by
  have ht2 : 0 < t / 2 := by linarith
  have hg0 := assembly_summable_sigma_exp k ht
  have hg2 := assembly_summable_sigma_exp k ht2
  set f : ℕ → ℝ := fun m => if m ≤ M then (0 : ℝ)
      else (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m : ℝ)) with hfdef
  set g : ℕ → ℝ := fun m => Real.exp (-(t / 2) * (M : ℝ)) *
      (if m = 0 then (0 : ℝ) else
        (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(t / 2) * (m : ℝ))) with hgdef
  have hfnn : ∀ m, 0 ≤ f m := by
    intro m
    rw [hfdef]
    dsimp only
    split
    · rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
  have hfle0 : ∀ m, f m ≤ (if m = 0 then (0 : ℝ)
      else (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))) := by
    intro m
    rw [hfdef]
    dsimp only
    rcases le_or_gt m M with h | h
    · rw [if_pos h]
      split
      · rfl
      · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
    · rw [if_neg (not_le.mpr h), if_neg (by omega : ¬ m = 0)]
  have hfsumm : Summable f := Summable.of_nonneg_of_le hfnn hfle0 hg0
  have hgsumm : Summable g := hg2.mul_left _
  have hbound : ∀ m, f m ≤ g m := by
    intro m
    rw [hfdef, hgdef]
    dsimp only
    rcases le_or_gt m M with h | h
    · rw [if_pos h]
      apply mul_nonneg (Real.exp_pos _).le
      split
      · rfl
      · exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg m)) (Real.exp_pos _).le
    · rw [if_neg (not_le.mpr h), if_neg (by omega : ¬ m = 0)]
      have hexp : Real.exp (-t * (m : ℝ))
          ≤ Real.exp (-(t / 2) * (M : ℝ)) * Real.exp (-(t / 2) * (m : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hmM : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast h.le
        nlinarith [hmM, ht]
      calc
        (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))
            ≤ (m : ℝ) ^ k * Sigma.sigmaR m *
                (Real.exp (-(t / 2) * (M : ℝ)) * Real.exp (-(t / 2) * (m : ℝ))) :=
              mul_le_mul_of_nonneg_left hexp
                (mul_nonneg (by positivity) (sigmaR_nonneg m))
        _ = Real.exp (-(t / 2) * (M : ℝ)) *
              ((m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(t / 2) * (m : ℝ))) := by ring
  calc
    (∑' m, f m) ≤ ∑' m : ℕ, g m := Summable.tsum_le_tsum hbound hfsumm hgsumm
    _ = Real.exp (-(t / 2) * (M : ℝ)) *
          ∑' m : ℕ, (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-(t / 2) * (m : ℝ))) := by
        rw [hg2.tsum_mul_left (Real.exp (-(t / 2) * (M : ℝ)))]
    _ = Real.exp (-(t / 2) * (M : ℝ)) * sigmaMoment k (t / 2) := by
        rw [sigmaMoment]

private lemma rhoDropModel_nonneg (n m : ℕ) :
    0 ≤ rhoDropModel n m := by
  rw [rhoDropModel]
  positivity

private lemma rhoDrop_nonneg {n m : ℕ} (_hm : m ≤ n) :
    0 ≤ rhoDrop n m := by
  rw [rhoDrop]
  have hsqrt : Real.sqrt (((n - m : ℕ) : ℝ)) ≤ Real.sqrt (n : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.sub_le n m
  nlinarith

private lemma rhoDrop_le_three_mul_div_sqrt {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    rhoDrop n m ≤ 3 * (m : ℝ) / Real.sqrt (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  set u : ℝ := Real.sqrt (((n - m : ℕ) : ℝ)) with hudef
  have hs0 : 0 < s := by
    rw [hsdef]
    exact Real.sqrt_pos.mpr hnpos
  have hs2 : s ^ 2 = (n : ℝ) := by
    rw [hsdef]
    exact Real.sq_sqrt hnpos.le
  have hu2 : u ^ 2 = ((n - m : ℕ) : ℝ) := by
    rw [hudef]
    exact Real.sq_sqrt (by positivity)
  have hus : u ≤ s := by
    rw [hudef, hsdef]
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.sub_le n m
  have hu0 : 0 ≤ u := by
    rw [hudef]
    exact Real.sqrt_nonneg _
  have hprod : u ^ 2 ≤ u * s := by
    calc u ^ 2 = u * u := by ring
      _ ≤ u * s := mul_le_mul_of_nonneg_left hus hu0
  have hsubadd : ((n - m : ℕ) : ℝ) + (m : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hm
  have hmul : (s - u) * s ≤ (m : ℝ) := by
    calc
      (s - u) * s = s ^ 2 - u * s := by ring
      _ ≤ s ^ 2 - u ^ 2 := by linarith
      _ = (m : ℝ) := by
        rw [hs2, hu2]
        linarith
  have hdrop : Real.sqrt (n : ℝ) - Real.sqrt (((n - m : ℕ) : ℝ))
      ≤ (m : ℝ) / Real.sqrt (n : ℝ) := by
    rw [← hsdef, ← hudef]
    rw [le_div_iff₀ hs0]
    exact hmul
  rw [rhoDrop]
  calc
    3 * (Real.sqrt (n : ℝ) - Real.sqrt (((n - m : ℕ) : ℝ)))
        ≤ 3 * ((m : ℝ) / Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hdrop (by norm_num : (0 : ℝ) ≤ 3)
    _ = 3 * (m : ℝ) / Real.sqrt (n : ℝ) := by ring

private lemma main_cut_two_mul_le {n m : ℕ} (hn8 : 8 ≤ n)
    (hmle : m ≤ ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊) :
    2 * m ≤ n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hp23 : (0 : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hnpos.le _
  have hmr : (m : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) :=
    le_trans (by exact_mod_cast hmle) (Nat.floor_le hp23)
  have hcubrt : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    have h8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
    have hmono : (8 : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h8 (by norm_num)
    have h83 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast 2 3,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [h83] at hmono
  have hn_factor : (n : ℝ) =
      (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hreal : 2 * (m : ℝ) ≤ (n : ℝ) := by
    calc
      2 * (m : ℝ) ≤ 2 * (n : ℝ) ^ (2 / 3 : ℝ) := by linarith
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcubrt hp23
      _ = (n : ℝ) := hn_factor.symm
  exact_mod_cast hreal

private lemma rhoDrop_sub_model_le_model_of_main
    {n m : ℕ} (hn8 : 8 ≤ n) (hm1 : 1 ≤ m)
    (hmle : m ≤ ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊) :
    |rhoDrop n m - rhoDropModel n m| ≤ |rhoDropModel n m| := by
  have hn1 : 1 ≤ n := by omega
  have h2m : 2 * m ≤ n := main_cut_two_mul_le hn8 hmle
  have hmn : m ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hs4 : Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
    rw [show Real.sqrt (n : ℝ) ^ 4 = (Real.sqrt (n : ℝ) ^ 2) ^ 2 by ring, hs2]
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm1
  have h2mR : 2 * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2m
  have h2m2 : 2 * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [h2mR, sq_nonneg ((n : ℝ) - 2 * (m : ℝ)),
      sq_nonneg (m : ℝ)]
  have hcore : (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5
      ≤ (m : ℝ) / (2 * Real.sqrt (n : ℝ)) := by
    rw [div_le_div_iff₀ (pow_pos hs0 5) (mul_pos (by norm_num) hs0)]
    rw [show (m : ℝ) ^ 3 * (2 * Real.sqrt (n : ℝ))
        = (2 * (m : ℝ) ^ 2) * ((m : ℝ) * Real.sqrt (n : ℝ)) by ring]
    rw [show (m : ℝ) * Real.sqrt (n : ℝ) ^ 5
        = (Real.sqrt (n : ℝ) ^ 4) * ((m : ℝ) * Real.sqrt (n : ℝ)) by ring]
    rw [hs4]
    exact mul_le_mul_of_nonneg_right h2m2 (mul_nonneg hmpos.le hs0.le)
  calc
    |rhoDrop n m - rhoDropModel n m|
        ≤ 3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 := rhoDrop_sub_model_le hn1 hmn
    _ = 3 * ((m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5) := by ring
    _ ≤ 3 * ((m : ℝ) / (2 * Real.sqrt (n : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hcore (by norm_num : (0 : ℝ) ≤ 3)
    _ ≤ rhoDropModel n m := by
        rw [rhoDropModel]
        have hrest : 0 ≤ (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3) := by positivity
        nlinarith
    _ = |rhoDropModel n m| := (abs_of_nonneg (rhoDropModel_nonneg n m)).symm

/-- The second-order cross term on the main range. -/
private theorem main_second_order_cross_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊,
        |erdosWeight n m - modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
      ≤ K / (n : ℝ) := by
  obtain ⟨K, hKpos, hK⟩ := main_kernel_error_rhoModel_le
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [hK, Filter.eventually_ge_atTop 8] with n hKn hn8
  calc
    (∑ m ∈ Finset.Icc 1 ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊,
        |erdosWeight n m - modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
      ≤ ∑ m ∈ Finset.Icc 1 ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊,
        |erdosWeight n m - modelSummand n m| * |rhoDropModel n m| := by
          refine Finset.sum_le_sum ?_
          intro m hm
          rw [Finset.mem_Icc] at hm
          exact mul_le_mul_of_nonneg_left
            (rhoDrop_sub_model_le_model_of_main hn8 hm.1 hm.2)
            (abs_nonneg _)
    _ ≤ K / (n : ℝ) := hKn

/-- The far `muNum` tail follows from the weighted Erdős tail. -/
private theorem muNum_far_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc (⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ + 1) (n - 1),
        erdosWeight n m * rhoDrop n m) ≤ K / (n : ℝ) := by
  obtain ⟨K, hKpos, hK⟩ := weighted_far_erdos_tail_le
  refine ⟨3 * K, by positivity, ?_⟩
  filter_upwards [hK, Filter.eventually_ge_atTop 1] with n hKn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  have hcoef_le : 3 / Real.sqrt (n : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hs0]
    nlinarith
  set M : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ with hMdef
  have hpoint : ∀ m ∈ Finset.Icc (M + 1) (n - 1),
      erdosWeight n m * rhoDrop n m
        ≤ (3 / Real.sqrt (n : ℝ)) * (erdosWeight n m * (m : ℝ)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmI : m ∈ Finset.Icc 1 (n - 1) := by
      rw [Finset.mem_Icc]
      omega
    have hmn : m ≤ n := by omega
    have hew : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hmI
    have hrho := rhoDrop_le_three_mul_div_sqrt hn1 hmn
    calc
      erdosWeight n m * rhoDrop n m
          ≤ erdosWeight n m * (3 * (m : ℝ) / Real.sqrt (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hrho hew
      _ = (3 / Real.sqrt (n : ℝ)) * (erdosWeight n m * (m : ℝ)) := by ring
  calc
    (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m * rhoDrop n m)
        ≤ ∑ m ∈ Finset.Icc (M + 1) (n - 1),
            (3 / Real.sqrt (n : ℝ)) * (erdosWeight n m * (m : ℝ)) :=
          Finset.sum_le_sum hpoint
    _ = (3 / Real.sqrt (n : ℝ)) *
          (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m * (m : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (3 / Real.sqrt (n : ℝ)) * (K / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hKn (by positivity)
    _ ≤ 3 * (K / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef_le (by positivity)
    _ = (3 * K) / (n : ℝ) := by ring

private lemma model_product_abs_le (n m : ℕ) :
    |modelSummand n m * rhoDropModel n m|
      ≤ (3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 1 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 2 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
            + 3 * C / (16 * (n : ℝ) ^ 3)) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 3 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (3 * C / (64 * (n : ℝ) ^ 4)) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 4 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ))) := by
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    simp [modelSummand]
  · rw [modelSummand_mul_rhoDropModel_expand hm]
    set base : ℝ := Sigma.sigmaR m *
      Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)) with hbase
    have hbase_nonneg : 0 ≤ base := by
      rw [hbase]
      exact mul_nonneg (sigmaR_nonneg m) (Real.exp_pos _).le
    set a1 : ℝ := (3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) * (m : ℝ) with ha1
    set a2 : ℝ := (15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) * (m : ℝ) ^ 2 with ha2
    set a3 : ℝ := (3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)) * (m : ℝ) ^ 3 with ha3
    set b3 : ℝ := (3 * C / (16 * (n : ℝ) ^ 3)) * (m : ℝ) ^ 3 with hb3
    set a4 : ℝ := (3 * C / (64 * (n : ℝ) ^ 4)) * (m : ℝ) ^ 4 with ha4
    have ha1nn : 0 ≤ a1 := by rw [ha1]; positivity
    have ha2nn : 0 ≤ a2 := by rw [ha2]; positivity
    have ha3nn : 0 ≤ a3 := by rw [ha3]; positivity
    have hb3nn : 0 ≤ b3 := by rw [hb3]; have := C_pos; positivity
    have ha4nn : 0 ≤ a4 := by rw [ha4]; have := C_pos; positivity
    have hpoly :
        |a1 + a2 + (a3 - b3) + (-a4)| ≤ a1 + a2 + (a3 + b3) + a4 := by
      calc
        |a1 + a2 + (a3 - b3) + (-a4)|
            ≤ |a1| + |a2| + |a3 - b3| + |-a4| :=
              assembly_abs_add_four_le a1 a2 (a3 - b3) (-a4)
        _ ≤ a1 + a2 + (a3 + b3) + a4 := by
          have hsub : |a3 - b3| ≤ a3 + b3 := by
            rw [abs_le]
            constructor <;> nlinarith
          rw [abs_of_nonneg ha1nn, abs_of_nonneg ha2nn, abs_neg, abs_of_nonneg ha4nn]
          linarith
    have hrewrite :
        ( (3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) * (m : ℝ)
          + (15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) * (m : ℝ) ^ 2
          + ((3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
              - 3 * C / (16 * (n : ℝ) ^ 3)) * (m : ℝ) ^ 3)
          + ((-3 * C / (64 * (n : ℝ) ^ 4)) * (m : ℝ) ^ 4))
        = a1 + a2 + (a3 - b3) + (-a4) := by
      rw [ha1, ha2, ha3, hb3, ha4]
      ring
    calc
      |base *
          ( (3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) * (m : ℝ)
            + (15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) * (m : ℝ) ^ 2
            + ((3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
                - 3 * C / (16 * (n : ℝ) ^ 3)) * (m : ℝ) ^ 3)
            + ((-3 * C / (64 * (n : ℝ) ^ 4)) * (m : ℝ) ^ 4))|
          = base *
              |a1 + a2 + (a3 - b3) + (-a4)| := by
            rw [hrewrite, abs_mul, abs_of_nonneg hbase_nonneg]
      _ ≤ base * (a1 + a2 + (a3 + b3) + a4) :=
            mul_le_mul_of_nonneg_left hpoly hbase_nonneg
      _ =
        (3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) *
          ((m : ℝ) ^ 1 * Sigma.sigmaR m *
            Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) *
          ((m : ℝ) ^ 2 * Sigma.sigmaR m *
            Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
            + 3 * C / (16 * (n : ℝ) ^ 3)) *
          ((m : ℝ) ^ 3 * Sigma.sigmaR m *
            Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (3 * C / (64 * (n : ℝ) ^ 4)) *
          ((m : ℝ) ^ 4 * Sigma.sigmaR m *
            Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ))) := by
            rw [hbase, ha1, ha2, ha3, hb3, ha4]
            ring
      _ =
        (3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 1 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 2 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
            + 3 * C / (16 * (n : ℝ) ^ 3)) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 3 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ)))
        + (3 * C / (64 * (n : ℝ) ^ 4)) *
          (if m = 0 then (0 : ℝ) else
            (m : ℝ) ^ 4 * Sigma.sigmaR m *
              Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ))) := by
            rw [if_neg hm, if_neg hm, if_neg hm, if_neg hm]

private lemma summable_model_rhoDropModel_guarded {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun m : ℕ =>
      if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have ht0 : 0 < massLam / Real.sqrt (n : ℝ) := div_pos massLam_pos hs0
  let g : ℕ → ℕ → ℝ := fun k m =>
    if m = 0 then (0 : ℝ) else
      (m : ℝ) ^ k * Sigma.sigmaR m *
        Real.exp (-(massLam / Real.sqrt (n : ℝ)) * (m : ℝ))
  have hgs (k : ℕ) : Summable (g k) := by
    dsimp [g]
    exact assembly_summable_sigma_exp k ht0
  let c1 : ℝ := 3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))
  let c2 : ℝ := 15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))
  let c3 : ℝ := 3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
    + 3 * C / (16 * (n : ℝ) ^ 3)
  let c4 : ℝ := 3 * C / (64 * (n : ℝ) ^ 4)
  have hdom : Summable (fun m : ℕ => c1 * g 1 m + c2 * g 2 m + c3 * g 3 m + c4 * g 4 m) := by
    refine (((hgs 1).mul_left c1).add ((hgs 2).mul_left c2)).add
      ((hgs 3).mul_left c3) |>.add ((hgs 4).mul_left c4) |>.congr ?_
    intro m
    ring
  have hnorm : Summable (fun m : ℕ =>
      ‖(if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)‖) := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hdom
    rw [Real.norm_eq_abs]
    rcases eq_or_ne m 0 with hm | hm
    · subst hm
      simp [g, c1, c2, c3, c4]
    · rw [if_neg hm]
      simpa [g, c1, c2, c3, c4] using model_product_abs_le n m
  exact summable_norm_iff.mp hnorm

private lemma summable_model_rhoDropModel_tail {n M : ℕ} (hn : 1 ≤ n) :
    Summable (fun m : ℕ =>
      if m ≤ M then (0 : ℝ)
      else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m) := by
  have hsumm := summable_model_rhoDropModel_guarded (n := n) hn
  have hheadsumm : Summable (fun m : ℕ =>
      if m ≤ M then (if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
      else 0) :=
    summable_of_ne_finset_zero (s := Finset.range (M + 1)) (fun b hb => by
      rw [Finset.mem_range] at hb
      rw [if_neg (by omega : ¬ b ≤ M)])
  refine (hsumm.sub hheadsumm).congr ?_
  intro m
  by_cases hm : m ≤ M
  · simp [hm]
  · simp [hm]

private lemma model_rhoDropModel_tsum_split (n M : ℕ) (hn : 1 ≤ n) :
    (∑' m : ℕ, if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
      = (∑ m ∈ Finset.Icc 1 M, modelSummand n m * rhoDropModel n m)
        + (∑' m : ℕ,
            if m ≤ M then (0 : ℝ)
            else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m) := by
  have hsumm := summable_model_rhoDropModel_guarded (n := n) hn
  have hheadsumm : Summable (fun m : ℕ =>
      if m ≤ M then (if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
      else 0) :=
    summable_of_ne_finset_zero (s := Finset.range (M + 1)) (fun b hb => by
      rw [Finset.mem_range] at hb
      rw [if_neg (by omega : ¬ b ≤ M)])
  have htailsumm := summable_model_rhoDropModel_tail (n := n) (M := M) hn
  have hhead : (∑' m : ℕ,
      if m ≤ M then (if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m)
      else 0)
      = ∑ m ∈ Finset.Icc 1 M, modelSummand n m * rhoDropModel n m := by
    rw [tsum_eq_sum (s := Finset.Icc 1 M) (fun b hb => by
      rw [Finset.mem_Icc] at hb
      by_cases hbM : b ≤ M
      · have hb0 : b = 0 := by omega
        simp [hb0]
      · simp [hbM])]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [if_pos hm.2, if_neg (by omega : m ≠ 0)]
  rw [← hhead, ← hheadsumm.tsum_add htailsumm]
  apply tsum_congr
  intro m
  by_cases hm : m ≤ M
  · simp [hm]
  · simp [hm]

set_option maxHeartbeats 8000000 in
-- The model-product tail repeats the expensive sixth-root and power-denominator algebra.
/-- The model-product tail past the `n^(2/3)` cutoff. -/
private theorem model_rhoDropModel_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑' m : ℕ,
        if m ≤ ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ then (0 : ℝ)
        else |modelSummand n m * rhoDropModel n m|)
      ≤ K / (n : ℝ) := by
  obtain ⟨K1, hK1nn, hK1⟩ := sigmaMoment_le_power_sharp 1
  obtain ⟨K2, hK2nn, hK2⟩ := sigmaMoment_le_power_sharp 2
  obtain ⟨K3, hK3nn, hK3⟩ := sigmaMoment_le_power_sharp 3
  obtain ⟨K4, hK4nn, hK4⟩ := sigmaMoment_le_power_sharp 4
  have hlam0 : 0 < massLam := massLam_pos
  have hCpos : 0 < C := C_pos
  set B : ℝ :=
    12 * K1 / massLam ^ 3
      + 30 * K2 / massLam ^ 4
      + (12 + 6 * C) * K3 / massLam ^ 5
      + 3 * C * K4 / massLam ^ 6 with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    positivity
  refine ⟨B + 1, by linarith, ?_⟩
  filter_upwards [poly_mul_exp_neg_sixthRoot_le_inv (massLam / 4) (by positivity) 0,
    Filter.eventually_ge_atTop (max 8 ⌈massLam ^ 2⌉₊)] with n hpoly hnge
  have hn8 : 8 ≤ n := le_trans (le_max_left _ _) hnge
  have hnlamc : ⌈massLam ^ 2⌉₊ ≤ n := le_trans (le_max_right _ _) hnge
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hnge1
  have htp : 0 < massLam / Real.sqrt (n : ℝ) := div_pos hlam0 hs0
  have hlamle : massLam ≤ Real.sqrt (n : ℝ) := by
    calc
      massLam = Real.sqrt (massLam ^ 2) := (Real.sqrt_sq hlam0.le).symm
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by
        have : (⌈massLam ^ 2⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlamc
        linarith [Nat.le_ceil (massLam ^ 2)])
  have ht2pos : 0 < massLam / Real.sqrt (n : ℝ) / 2 := by positivity
  have ht2le1 : massLam / Real.sqrt (n : ℝ) / 2 ≤ 1 := by
    rw [div_div, div_le_one (by positivity)]
    nlinarith [hlamle, hs1, hlam0]
  set M : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ with hMdef
  have hsummgT : ∀ k, Summable (fun m => assemblyGTail n M k m) :=
    fun k => assembly_summable_gTail n M k rfl htp
  let c1 : ℝ := 3 / (2 * (n : ℝ) * Real.sqrt (n : ℝ))
  let c2 : ℝ := 15 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))
  let c3 : ℝ := 3 / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) ^ 3)
    + 3 * C / (16 * (n : ℝ) ^ 3)
  let c4 : ℝ := 3 * C / (64 * (n : ℝ) ^ 4)
  have hpt : ∀ m,
      (if m ≤ M then (0 : ℝ) else |modelSummand n m * rhoDropModel n m|)
        ≤ c1 * assemblyGTail n M 1 m + c2 * assemblyGTail n M 2 m
          + c3 * assemblyGTail n M 3 m + c4 * assemblyGTail n M 4 m := by
    intro m
    by_cases hmM : m ≤ M
    · simp [hmM, assemblyGTail, c1, c2, c3, c4]
    · rw [if_neg hmM, assemblyGTail, assemblyGTail, assemblyGTail, assemblyGTail,
        if_neg hmM, if_neg hmM, if_neg hmM, if_neg hmM]
      simpa [c1, c2, c3, c4] using model_product_abs_le n m
  have hdomsumm : Summable (fun m => c1 * assemblyGTail n M 1 m + c2 * assemblyGTail n M 2 m
      + c3 * assemblyGTail n M 3 m + c4 * assemblyGTail n M 4 m) := by
    refine ((((hsummgT 1).mul_left c1).add ((hsummgT 2).mul_left c2)).add
      ((hsummgT 3).mul_left c3)).add ((hsummgT 4).mul_left c4) |>.congr ?_
    intro m
    ring
  have htailsumm : Summable (fun m : ℕ =>
      if m ≤ M then (0 : ℝ) else |modelSummand n m * rhoDropModel n m|) :=
    Summable.of_nonneg_of_le (fun m => by split <;> positivity) hpt hdomsumm
  have hsplit :
      (∑' m : ℕ, if m ≤ M then (0 : ℝ) else |modelSummand n m * rhoDropModel n m|)
        ≤ c1 * (∑' m, assemblyGTail n M 1 m)
          + c2 * (∑' m, assemblyGTail n M 2 m)
          + c3 * (∑' m, assemblyGTail n M 3 m)
          + c4 * (∑' m, assemblyGTail n M 4 m) := by
    calc
      (∑' m : ℕ, if m ≤ M then (0 : ℝ) else |modelSummand n m * rhoDropModel n m|)
          ≤ ∑' m : ℕ, (c1 * assemblyGTail n M 1 m + c2 * assemblyGTail n M 2 m
              + c3 * assemblyGTail n M 3 m + c4 * assemblyGTail n M 4 m) :=
            Summable.tsum_le_tsum hpt htailsumm hdomsumm
      _ = c1 * (∑' m, assemblyGTail n M 1 m)
          + c2 * (∑' m, assemblyGTail n M 2 m)
          + c3 * (∑' m, assemblyGTail n M 3 m)
          + c4 * (∑' m, assemblyGTail n M 4 m) := by
            let f1 : ℕ → ℝ := fun m => c1 * assemblyGTail n M 1 m
            let f2 : ℕ → ℝ := fun m => c2 * assemblyGTail n M 2 m
            let f3 : ℕ → ℝ := fun m => c3 * assemblyGTail n M 3 m
            let f4 : ℕ → ℝ := fun m => c4 * assemblyGTail n M 4 m
            have hf1 : Summable f1 := (hsummgT 1).mul_left c1
            have hf2 : Summable f2 := (hsummgT 2).mul_left c2
            have hf3 : Summable f3 := (hsummgT 3).mul_left c3
            have hf4 : Summable f4 := (hsummgT 4).mul_left c4
            calc
              (∑' m : ℕ,
                (c1 * assemblyGTail n M 1 m + c2 * assemblyGTail n M 2 m
                  + c3 * assemblyGTail n M 3 m + c4 * assemblyGTail n M 4 m))
                  = ∑' m : ℕ, (f1 m + f2 m + (f3 m + f4 m)) := by
                    apply tsum_congr
                    intro m
                    simp [f1, f2, f3, f4]
                    ring
              _ = (∑' m, f1 m) + (∑' m, f2 m) + ((∑' m, f3 m) + (∑' m, f4 m)) := by
                    rw [← hf1.tsum_add hf2]
                    rw [← hf3.tsum_add hf4]
                    rw [← (hf1.add hf2).tsum_add (hf3.add hf4)]
              _ = c1 * (∑' m, assemblyGTail n M 1 m)
                  + c2 * (∑' m, assemblyGTail n M 2 m)
                  + c3 * (∑' m, assemblyGTail n M 3 m)
                  + c4 * (∑' m, assemblyGTail n M 4 m) := by
                    simp [f1, f2, f3, f4, tsum_mul_left]
                    ring
  have hTk : ∀ k, (∑' m, assemblyGTail n M k m)
      ≤ Real.exp (-(massLam / Real.sqrt (n : ℝ) / 2) * (M : ℝ)) *
          sigmaMoment k (massLam / Real.sqrt (n : ℝ) / 2) := by
    intro k
    rw [assemblyGTail_eq_bare]
    exact assembly_sigma_geom_tail_le k htp M
  have hE : Real.exp (-(massLam / Real.sqrt (n : ℝ) / 2) * (M : ℝ))
      ≤ Real.exp (-(massLam / 4) * (n : ℝ) ^ (1 / 6 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hM_ge : ((M : ℝ)) ≥ (n : ℝ) ^ (2 / 3 : ℝ) - 1 := by
      have := Nat.lt_floor_add_one ((n : ℝ) ^ (2 / 3 : ℝ))
      rw [← hMdef] at this
      linarith
    have hn23ge2 : (2 : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by
      have hx0 : 0 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hnpos.le _
      have hcube : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (n : ℝ) ^ 2 := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul hnpos.le,
          show (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
      have hge : (64 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have h8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
        nlinarith [h8]
      nlinarith [hcube, hge, hx0, mul_nonneg hx0 hx0,
        sq_nonneg ((n : ℝ) ^ (2 / 3 : ℝ) - 2),
        sq_nonneg ((n : ℝ) ^ (2 / 3 : ℝ) + 1)]
    have hMhalf : (1 / 2 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) ≤ (M : ℝ) := by
      nlinarith [hM_ge, hn23ge2]
    have hsqrt_rpow : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    have hsplitpow : (n : ℝ) ^ (2 / 3 : ℝ)
        = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add hnpos]
      norm_num
    have hkey : (massLam / 4) * (n : ℝ) ^ (1 / 6 : ℝ)
        ≤ massLam / Real.sqrt (n : ℝ) / 2 * (M : ℝ) := by
      rw [hsqrt_rpow]
      have hpos12 : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hnpos _
      calc
        (massLam / 4) * (n : ℝ) ^ (1 / 6 : ℝ)
            = massLam / (n : ℝ) ^ (1 / 2 : ℝ) / 2 *
                ((1 / 2 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) := by
              rw [hsplitpow]
              field_simp
              ring
        _ ≤ massLam / (n : ℝ) ^ (1 / 2 : ℝ) / 2 * (M : ℝ) := by
              exact mul_le_mul_of_nonneg_left hMhalf (by positivity)
    nlinarith [hkey]
  have hsharp1 := hK1 _ ht2pos ht2le1
  have hsharp2 := hK2 _ ht2pos ht2le1
  have hsharp3 := hK3 _ ht2pos ht2le1
  have hsharp4 := hK4 _ ht2pos ht2le1
  have hp3 : (massLam / Real.sqrt (n : ℝ) / 2) ^ 3
      = massLam ^ 3 / (8 * (n : ℝ) * Real.sqrt (n : ℝ)) := by
    rw [div_div]
    field_simp [hs0.ne', hlam0.ne']
    nlinarith [hs2]
  have hp4 : (massLam / Real.sqrt (n : ℝ) / 2) ^ 4
      = massLam ^ 4 / (16 * (n : ℝ) ^ 2) := by
    rw [div_div]
    field_simp [hs0.ne', hlam0.ne']
    nlinarith [hs2]
  have hp5 : (massLam / Real.sqrt (n : ℝ) / 2) ^ 5
      = massLam ^ 5 / (32 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ)) := by
    rw [div_div]
    field_simp [hs0.ne', hlam0.ne']
    nlinarith [hs2]
  have hp6 : (massLam / Real.sqrt (n : ℝ) / 2) ^ 6
      = massLam ^ 6 / (64 * (n : ℝ) ^ 3) := by
    have hs6 : Real.sqrt (n : ℝ) ^ 6 = (n : ℝ) ^ 3 := by
      rw [show Real.sqrt (n : ℝ) ^ 6 = (Real.sqrt (n : ℝ) ^ 2) ^ 3 by ring, hs2]
    rw [div_div]
    field_simp [hs0.ne', hlam0.ne']
    rw [hs6]
    ring
  set E : ℝ := Real.exp (-(massLam / Real.sqrt (n : ℝ) / 2) * (M : ℝ)) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hsqle : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    nlinarith [hs2, hs1, mul_nonneg hs0.le (sub_nonneg.mpr hs1)]
  have hinv_sqrt_le_one : 1 / Real.sqrt (n : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hs0]
    nlinarith
  have hinv_n_le_one : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hnpos]
    nlinarith
  have e1 : c1 * (∑' m, assemblyGTail n M 1 m) ≤ E * (12 * K1 / massLam ^ 3) := by
    calc
      c1 * (∑' m, assemblyGTail n M 1 m)
          ≤ c1 * (E * sigmaMoment 1 (massLam / Real.sqrt (n : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (hTk 1) (by dsimp [c1]; positivity)
      _ ≤ c1 * (E * (K1 / (massLam / Real.sqrt (n : ℝ) / 2) ^ 3)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp1 hEpos.le)
              (by dsimp [c1]; positivity)
      _ = E * (12 * K1 / massLam ^ 3) := by
            rw [hp3]
            dsimp [c1]
            field_simp
            ring
  have e2 : c2 * (∑' m, assemblyGTail n M 2 m) ≤ E * (30 * K2 / massLam ^ 4) := by
    calc
      c2 * (∑' m, assemblyGTail n M 2 m)
          ≤ c2 * (E * sigmaMoment 2 (massLam / Real.sqrt (n : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (hTk 2) (by dsimp [c2]; positivity)
      _ ≤ c2 * (E * (K2 / (massLam / Real.sqrt (n : ℝ) / 2) ^ 4)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp2 hEpos.le)
              (by dsimp [c2]; positivity)
      _ = E * (30 * K2 / (massLam ^ 4 * Real.sqrt (n : ℝ))) := by
            rw [hp4]
            dsimp [c2]
            field_simp
            ring
      _ ≤ E * (30 * K2 / massLam ^ 4) := by
            apply mul_le_mul_of_nonneg_left _ hEpos.le
            calc
              30 * K2 / (massLam ^ 4 * Real.sqrt (n : ℝ))
                  = (30 * K2 / massLam ^ 4) * (1 / Real.sqrt (n : ℝ)) := by
                    field_simp [hs0.ne', hlam0.ne']
              _ ≤ (30 * K2 / massLam ^ 4) * 1 := by
                    exact mul_le_mul_of_nonneg_left hinv_sqrt_le_one (by positivity)
              _ = 30 * K2 / massLam ^ 4 := by ring
  have e3 : c3 * (∑' m, assemblyGTail n M 3 m)
      ≤ E * ((12 + 6 * C) * K3 / massLam ^ 5) := by
    calc
      c3 * (∑' m, assemblyGTail n M 3 m)
          ≤ c3 * (E * sigmaMoment 3 (massLam / Real.sqrt (n : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (hTk 3) (by dsimp [c3]; have := C_pos; positivity)
      _ ≤ c3 * (E * (K3 / (massLam / Real.sqrt (n : ℝ) / 2) ^ 5)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp3 hEpos.le)
              (by dsimp [c3]; have := C_pos; positivity)
      _ = E * (12 * K3 / (massLam ^ 5 * (Real.sqrt (n : ℝ)) ^ 2)
            + 6 * C * K3 / (massLam ^ 5 * Real.sqrt (n : ℝ))) := by
            rw [hp5]
            dsimp [c3]
            have hs3 : Real.sqrt (n : ℝ) ^ 3 = (n : ℝ) * Real.sqrt (n : ℝ) := by
              rw [show Real.sqrt (n : ℝ) ^ 3 = Real.sqrt (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) by ring,
                hs2]
            field_simp [hs0.ne', hlam0.ne']
            rw [hs3]
            ring_nf
      _ ≤ E * ((12 + 6 * C) * K3 / massLam ^ 5) := by
            apply mul_le_mul_of_nonneg_left _ hEpos.le
            have hden1 : 12 * K3 / (massLam ^ 5 * (Real.sqrt (n : ℝ)) ^ 2)
                ≤ 12 * K3 / massLam ^ 5 := by
              calc
                12 * K3 / (massLam ^ 5 * (Real.sqrt (n : ℝ)) ^ 2)
                    = (12 * K3 / massLam ^ 5) *
                        ((1 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt (n : ℝ))) := by
                      field_simp [hs0.ne', hlam0.ne']
                _ ≤ (12 * K3 / massLam ^ 5) * 1 := by
                      have hprod_inv : (1 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt (n : ℝ)) ≤ 1 := by
                        nlinarith [hinv_sqrt_le_one,
                          div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hs0.le]
                      exact mul_le_mul_of_nonneg_left hprod_inv (by positivity)
                _ = 12 * K3 / massLam ^ 5 := by ring
            have hden2 : 6 * C * K3 / (massLam ^ 5 * Real.sqrt (n : ℝ))
                ≤ 6 * C * K3 / massLam ^ 5 := by
              calc
                6 * C * K3 / (massLam ^ 5 * Real.sqrt (n : ℝ))
                    = (6 * C * K3 / massLam ^ 5) * (1 / Real.sqrt (n : ℝ)) := by
                      field_simp [hs0.ne', hlam0.ne']
                _ ≤ (6 * C * K3 / massLam ^ 5) * 1 := by
                      exact mul_le_mul_of_nonneg_left hinv_sqrt_le_one (by positivity)
                _ = 6 * C * K3 / massLam ^ 5 := by ring
            calc
              12 * K3 / (massLam ^ 5 * (Real.sqrt (n : ℝ)) ^ 2)
                  + 6 * C * K3 / (massLam ^ 5 * Real.sqrt (n : ℝ))
                  ≤ 12 * K3 / massLam ^ 5 + 6 * C * K3 / massLam ^ 5 := by
                    linarith
              _ = (12 + 6 * C) * K3 / massLam ^ 5 := by ring
  have e4 : c4 * (∑' m, assemblyGTail n M 4 m) ≤ E * (3 * C * K4 / massLam ^ 6) := by
    calc
      c4 * (∑' m, assemblyGTail n M 4 m)
          ≤ c4 * (E * sigmaMoment 4 (massLam / Real.sqrt (n : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left (hTk 4) (by dsimp [c4]; have := C_pos; positivity)
      _ ≤ c4 * (E * (K4 / (massLam / Real.sqrt (n : ℝ) / 2) ^ 6)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsharp4 hEpos.le)
              (by dsimp [c4]; have := C_pos; positivity)
      _ = E * (3 * C * K4 / (massLam ^ 6 * (n : ℝ))) := by
            rw [hp6]
            dsimp [c4]
            field_simp [hnpos.ne', hlam0.ne']
      _ ≤ E * (3 * C * K4 / massLam ^ 6) := by
            apply mul_le_mul_of_nonneg_left _ hEpos.le
            calc
              3 * C * K4 / (massLam ^ 6 * (n : ℝ))
                  = (3 * C * K4 / massLam ^ 6) * (1 / (n : ℝ)) := by
                    field_simp [hnpos.ne', hlam0.ne']
              _ ≤ (3 * C * K4 / massLam ^ 6) * 1 := by
                    exact mul_le_mul_of_nonneg_left hinv_n_le_one (by positivity)
              _ = 3 * C * K4 / massLam ^ 6 := by ring
  calc
    (∑' m : ℕ, if m ≤ M then (0 : ℝ) else |modelSummand n m * rhoDropModel n m|)
        ≤ c1 * (∑' m, assemblyGTail n M 1 m)
          + c2 * (∑' m, assemblyGTail n M 2 m)
          + c3 * (∑' m, assemblyGTail n M 3 m)
          + c4 * (∑' m, assemblyGTail n M 4 m) := hsplit
    _ ≤ E * (12 * K1 / massLam ^ 3) + E * (30 * K2 / massLam ^ 4)
          + E * ((12 + 6 * C) * K3 / massLam ^ 5)
          + E * (3 * C * K4 / massLam ^ 6) := by
        linarith [e1, e2, e3, e4]
    _ = E * B := by
        rw [hBdef]
        ring
    _ ≤ Real.exp (-(massLam / 4) * (n : ℝ) ^ (1 / 6 : ℝ)) * B := by
        exact mul_le_mul_of_nonneg_right hE hBnn
    _ ≤ (1 / (n : ℝ)) * B := by
        apply mul_le_mul_of_nonneg_right _ hBnn
        have hp := hpoly
        rw [pow_zero, one_mul] at hp
        exact hp
    _ = B / (n : ℝ) := by ring
    _ ≤ (B + 1) / (n : ℝ) := by
        rw [show (B + 1) / (n : ℝ) = B / (n : ℝ) + 1 / (n : ℝ) by ring]
        exact le_add_of_nonneg_right (by positivity)

private lemma muNum_split_main_tail (n M : ℕ) (hMle : M ≤ n - 1) :
    muNum n =
      (∑ m ∈ Finset.Icc 1 M, erdosWeight n m * rhoDrop n m)
      + (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m * rhoDrop n m) := by
  have e1 : Finset.Icc 1 M = Finset.Ioc 0 M := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have e2 : Finset.Icc (M + 1) (n - 1) = Finset.Ioc M (n - 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have e3 : Finset.Icc 1 (n - 1) = Finset.Ioc 0 (n - 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [muNum, e1, e2, e3, Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMle]

/-- The numerator has the required two-term expansion. -/
theorem muNum_two_term :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |muNum n - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
      ≤ K / (n : ℝ) := by
  obtain ⟨Kmodel, hKmodelpos, hKmodel⟩ := model_sum_two_term_asymp
  obtain ⟨Kmain, hKmainpos, hKmain⟩ := main_kernel_error_rhoModel_le
  obtain ⟨Krho, hKrhopos, hKrho⟩ := main_model_rho_error_le
  obtain ⟨Kcross, hKcrosspos, hKcross⟩ := main_second_order_cross_le
  obtain ⟨Ktail, hKtailpos, hKtail⟩ := muNum_far_tail_le
  obtain ⟨Kmtail, hKmtailpos, hKmtail⟩ := model_rhoDropModel_tail_le
  refine ⟨Kmodel + Kmain + Krho + Kcross + Ktail + Kmtail, by linarith, ?_⟩
  filter_upwards [hKmodel, hKmain, hKrho, hKcross, hKtail, hKmtail,
    Filter.eventually_ge_atTop 8] with n hmodel hmain hrho hcross htail hmtail hn8
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  set M : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ with hMdef
  have hMlt : M < n := by
    have h1 : (M : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by
      rw [hMdef]
      exact Nat.floor_le (Real.rpow_nonneg hnpos.le _)
    have h2 : (n : ℝ) ^ (2 / 3 : ℝ) < (n : ℝ) := by
      calc
        (n : ℝ) ^ (2 / 3 : ℝ) < (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < n)) (by norm_num)
        _ = (n : ℝ) := Real.rpow_one _
    have : (M : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast this
  have hMle : M ≤ n - 1 := by omega
  set modelT : ℝ :=
    ∑' m : ℕ, if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m
    with hmodelTdef
  set modelTail : ℝ :=
    ∑' m : ℕ,
      if m ≤ M then (0 : ℝ)
      else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m
    with hmodelTaildef
  set mainE : ℝ := ∑ m ∈ Finset.Icc 1 M, erdosWeight n m * rhoDrop n m with hmainEdef
  set mainM : ℝ := ∑ m ∈ Finset.Icc 1 M, modelSummand n m * rhoDropModel n m with hmainMdef
  set tailE : ℝ :=
    ∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m * rhoDrop n m with htailEdef
  set L : ℝ := 3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ) with hLdef
  have hmuSplit : muNum n = mainE + tailE := by
    rw [hmainEdef, htailEdef]
    exact muNum_split_main_tail n M hMle
  have hmodelSplit : modelT = mainM + modelTail := by
    rw [hmodelTdef, hmainMdef, hmodelTaildef]
    exact model_rhoDropModel_tsum_split n M hn1
  have hmainErr : |mainE - mainM| ≤ (Kmain + Krho + Kcross) / (n : ℝ) := by
    rw [hmainEdef, hmainMdef, ← Finset.sum_sub_distrib]
    calc
      |∑ m ∈ Finset.Icc 1 M,
          (erdosWeight n m * rhoDrop n m - modelSummand n m * rhoDropModel n m)|
          ≤ ∑ m ∈ Finset.Icc 1 M,
              |erdosWeight n m * rhoDrop n m - modelSummand n m * rhoDropModel n m| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 M,
            (|erdosWeight n m - modelSummand n m| * |rhoDropModel n m|
              + |modelSummand n m| * |rhoDrop n m - rhoDropModel n m|
              + |erdosWeight n m - modelSummand n m| * |rhoDrop n m - rhoDropModel n m|) := by
            refine Finset.sum_le_sum ?_
            intro m hm
            have hrewrite :
                erdosWeight n m * rhoDrop n m - modelSummand n m * rhoDropModel n m
                  = (erdosWeight n m - modelSummand n m) * rhoDropModel n m
                    + modelSummand n m * (rhoDrop n m - rhoDropModel n m)
                    + (erdosWeight n m - modelSummand n m) *
                        (rhoDrop n m - rhoDropModel n m) := by
              ring
            rw [hrewrite]
            calc
              |(erdosWeight n m - modelSummand n m) * rhoDropModel n m
                    + modelSummand n m * (rhoDrop n m - rhoDropModel n m)
                    + (erdosWeight n m - modelSummand n m) *
                        (rhoDrop n m - rhoDropModel n m)|
                  ≤ |(erdosWeight n m - modelSummand n m) * rhoDropModel n m|
                    + |modelSummand n m * (rhoDrop n m - rhoDropModel n m)|
                    + |(erdosWeight n m - modelSummand n m) *
                        (rhoDrop n m - rhoDropModel n m)| :=
                      assembly_abs_add_three_le _ _ _
              _ =
                |erdosWeight n m - modelSummand n m| * |rhoDropModel n m|
                  + |modelSummand n m| * |rhoDrop n m - rhoDropModel n m|
                  + |erdosWeight n m - modelSummand n m| *
                      |rhoDrop n m - rhoDropModel n m| := by
                    rw [abs_mul, abs_mul, abs_mul]
      _ = (∑ m ∈ Finset.Icc 1 M,
            |erdosWeight n m - modelSummand n m| * |rhoDropModel n m|)
          + (∑ m ∈ Finset.Icc 1 M,
            |modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
          + (∑ m ∈ Finset.Icc 1 M,
            |erdosWeight n m - modelSummand n m| * |rhoDrop n m - rhoDropModel n m|) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ Kmain / (n : ℝ) + Krho / (n : ℝ) + Kcross / (n : ℝ) := by
            rw [hMdef]
            linarith [hmain, hrho, hcross]
      _ = (Kmain + Krho + Kcross) / (n : ℝ) := by ring
  have htailEnn : 0 ≤ tailE := by
    rw [htailEdef]
    refine Finset.sum_nonneg ?_
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmI : m ∈ Finset.Icc 1 (n - 1) := by
      rw [Finset.mem_Icc]
      omega
    have hmn : m ≤ n := by omega
    exact mul_nonneg (erdosWeight_nonneg_of_mem hmI) (rhoDrop_nonneg hmn)
  have htailEabs : |tailE| ≤ Ktail / (n : ℝ) := by
    rw [abs_of_nonneg htailEnn, htailEdef, hMdef]
    exact htail
  have htailSumm := summable_model_rhoDropModel_tail (n := n) (M := M) hn1
  have hmodelTailAbs : |modelTail| ≤ Kmtail / (n : ℝ) := by
    rw [hmodelTaildef]
    have hnorm_eq :
        (∑' i : ℕ, ‖if i ≤ M then (0 : ℝ)
          else if i = 0 then (0 : ℝ) else modelSummand n i * rhoDropModel n i‖)
        =
        (∑' m : ℕ, if m ≤ M then (0 : ℝ)
          else |modelSummand n m * rhoDropModel n m|) := by
      refine tsum_congr ?_
      intro m
      by_cases hm : m ≤ M
      · simp [hm]
      · have hm0 : m ≠ 0 := by omega
        simp [hm, hm0, Real.norm_eq_abs]
    calc
      |∑' m : ℕ,
          if m ≤ M then (0 : ℝ)
          else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m|
          = ‖∑' m : ℕ,
              if m ≤ M then (0 : ℝ)
              else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m‖ := by
                rw [Real.norm_eq_abs]
      _ ≤ ∑' i : ℕ, ‖if i ≤ M then (0 : ℝ)
          else if i = 0 then (0 : ℝ) else modelSummand n i * rhoDropModel n i‖ :=
            norm_tsum_le_tsum_norm htailSumm.norm
      _ = ∑' m : ℕ, if m ≤ M then (0 : ℝ)
          else |modelSummand n m * rhoDropModel n m| := hnorm_eq
      _ ≤ Kmtail / (n : ℝ) := hmtail
  have hdecomp : muNum n - L = (modelT - L) + (mainE - mainM) + tailE - modelTail := by
    rw [hmuSplit, hmodelSplit]
    ring
  have hmodelAbs : |modelT - L| ≤ Kmodel / (n : ℝ) := by
    rw [hmodelTdef, hLdef]
    exact hmodel
  calc
    |muNum n - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
        = |muNum n - L| := by rw [hLdef]
    _ = |(modelT - L) + (mainE - mainM) + tailE - modelTail| := by rw [hdecomp]
    _ ≤ |(modelT - L) + (mainE - mainM) + tailE| + |modelTail| := by
        rw [sub_eq_add_neg]
        exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ (|modelT - L| + |mainE - mainM| + |tailE|) + |modelTail| := by
        gcongr
        exact assembly_abs_add_three_le _ _ _
    _ ≤ Kmodel / (n : ℝ) + (Kmain + Krho + Kcross) / (n : ℝ)
          + Ktail / (n : ℝ) + Kmtail / (n : ℝ) := by
        linarith [hmodelAbs, hmainErr, htailEabs, hmodelTailAbs]
    _ = (Kmodel + Kmain + Krho + Kcross + Ktail + Kmtail) / (n : ℝ) := by ring

/-- The normalized drift has the same two-term expansion. -/
theorem muTilde_two_term :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |muTilde n - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
      ≤ K / (n : ℝ) := by
  exact muTilde_expansion_of_muNum muNum_two_term

end AnalyticCombinatorics.Ch8.Partitions.Erdos
