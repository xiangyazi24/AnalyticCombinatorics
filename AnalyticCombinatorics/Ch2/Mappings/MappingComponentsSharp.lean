import Mathlib
import AnalyticCombinatorics.Ch2.Mappings.MappingComponents
import AnalyticCombinatorics.Ch2.Mappings.RamanujanQ
import AnalyticCombinatorics.Ch2.Mappings.RamanujanQSharp

/-!
# Sharp logarithmic asymptotic for mapping components

The expected number of connected components in a uniform random mapping on
`n` labels is asymptotic to `(1 / 2) log n`.
-/

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

namespace Sharp

-- The finite-sum comparisons below combine several imported analytic bounds;
-- a larger heartbeat budget avoids brittleness in the final asymptotic squeeze.
set_option maxHeartbeats 800000

private lemma componentLogScale_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / 2) atTop atTop := by
  exact Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma gaussianKernel_sum_le_one_add_sqrt {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range n, gaussianKernel n k) ≤
      1 + Real.sqrt (Real.pi * (n : ℝ) / 2) := by
  calc
    (∑ k ∈ Finset.range n, gaussianKernel n k) ≤
        1 + ∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x :=
      sum_gaussianKernel_range_le_one_add_integral hn
    _ ≤ 1 + ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x := by
      exact add_le_add (le_refl 1) (integral_gaussianKernel_Ioc_le_Ioi hn)
    _ = 1 + Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 := by
      rw [integral_gaussianKernel_Ioi hn]
    _ = 1 + Real.sqrt (Real.pi * (n : ℝ) / 2) := by
      rw [gaussian_halfline_value_eq_sqrt_pi_mul_nat_div_two hn]

private lemma gaussianKernel_sum_div_nat_sqrt_succ_le_three {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range n, gaussianKernel n k) /
        (((Nat.sqrt n + 1 : ℕ) : ℝ)) ≤ 3 := by
  have hden_pos : (0 : ℝ) < ((Nat.sqrt n + 1 : ℕ) : ℝ) := by positivity
  have hsqrt_le_den :
      Real.sqrt (n : ℝ) ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using Real.real_sqrt_le_nat_sqrt_succ (a := n)
  have hsum := gaussianKernel_sum_le_one_add_sqrt (n := n) hn
  have htail :
      (∑ k ∈ Finset.range n, gaussianKernel n k) /
          (((Nat.sqrt n + 1 : ℕ) : ℝ)) ≤
        (1 + Real.sqrt (Real.pi * (n : ℝ) / 2)) /
          (((Nat.sqrt n + 1 : ℕ) : ℝ)) :=
    div_le_div_of_nonneg_right hsum hden_pos.le
  have hone : (1 : ℝ) / (((Nat.sqrt n + 1 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_one₀ hden_pos]
    exact_mod_cast Nat.succ_pos (Nat.sqrt n)
  have hgauss :
      Real.sqrt (Real.pi * (n : ℝ) / 2) /
          (((Nat.sqrt n + 1 : ℕ) : ℝ)) ≤ 2 := by
    have hnum := sqrt_pi_mul_nat_div_two_le_two_sqrt n
    calc
      Real.sqrt (Real.pi * (n : ℝ) / 2) /
          (((Nat.sqrt n + 1 : ℕ) : ℝ)) ≤
        (2 * Real.sqrt (n : ℝ)) / (((Nat.sqrt n + 1 : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_right hnum hden_pos.le
      _ ≤ (2 * (((Nat.sqrt n + 1 : ℕ) : ℝ))) /
          (((Nat.sqrt n + 1 : ℕ) : ℝ)) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsqrt_le_den (by norm_num : (0 : ℝ) ≤ 2))
              hden_pos.le
      _ = 2 := by
        field_simp [hden_pos.ne']
  calc
    (∑ k ∈ Finset.range n, gaussianKernel n k) /
        (((Nat.sqrt n + 1 : ℕ) : ℝ)) ≤
      (1 + Real.sqrt (Real.pi * (n : ℝ) / 2)) /
        (((Nat.sqrt n + 1 : ℕ) : ℝ)) := htail
    _ = 1 / (((Nat.sqrt n + 1 : ℕ) : ℝ)) +
        Real.sqrt (Real.pi * (n : ℝ) / 2) /
          (((Nat.sqrt n + 1 : ℕ) : ℝ)) := by ring
    _ ≤ 1 + 2 := add_le_add hone hgauss
    _ = 3 := by norm_num

private lemma weightedRamanujanComponents_tail_le_three {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ (Finset.range n).filter fun i => Nat.sqrt n ≤ i,
        ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤ 3 := by
  classical
  let K : ℕ := Nat.sqrt n
  have htail_to_gauss :
      (∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤
        ∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
          gaussianKernel n i / (((K + 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_range : i ∈ Finset.range n := (Finset.mem_filter.mp hi).1
    have hKi : K ≤ i := (Finset.mem_filter.mp hi).2
    have hterm_nonneg : 0 ≤ ramanujanQTerm n i :=
      ramanujanQTerm_nonneg (n := n) (k := i) (Nat.le_of_lt (Finset.mem_range.mp hi_range))
    have hterm_gauss : ramanujanQTerm n i ≤ gaussianKernel n i :=
      ramanujanQTerm_le_gaussianKernel hn (Nat.le_of_lt (Finset.mem_range.mp hi_range))
    have hden_i_pos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have hden_K_pos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
    have hden_le : ((K + 1 : ℕ) : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hKi
    calc
      ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ)) ≤
          gaussianKernel n i / (((i + 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hterm_gauss hden_i_pos.le
      _ ≤ gaussianKernel n i / (((K + 1 : ℕ) : ℝ)) := by
        have hg_nonneg : 0 ≤ gaussianKernel n i := (Real.exp_pos _).le
        exact div_le_div_of_nonneg_left hg_nonneg hden_K_pos hden_le
  have hfilter_to_full :
      (∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
          gaussianKernel n i / (((K + 1 : ℕ) : ℝ))) ≤
        ∑ i ∈ Finset.range n, gaussianKernel n i / (((K + 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (by intro i hi; exact (Finset.mem_filter.mp hi).1) ?_
    intro i hi_range hi_not
    exact div_nonneg (Real.exp_pos _).le (by positivity)
  have hfull :
      (∑ i ∈ Finset.range n, gaussianKernel n i / (((K + 1 : ℕ) : ℝ))) =
        (∑ i ∈ Finset.range n, gaussianKernel n i) / (((K + 1 : ℕ) : ℝ)) := by
    rw [Finset.sum_div]
  calc
    (∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
        ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤
      ∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
        gaussianKernel n i / (((K + 1 : ℕ) : ℝ)) := htail_to_gauss
    _ ≤ ∑ i ∈ Finset.range n, gaussianKernel n i / (((K + 1 : ℕ) : ℝ)) := hfilter_to_full
    _ = (∑ i ∈ Finset.range n, gaussianKernel n i) / (((K + 1 : ℕ) : ℝ)) := hfull
    _ ≤ 3 := by
      simpa [K] using gaussianKernel_sum_div_nat_sqrt_succ_le_three (n := n) hn

private lemma weightedRamanujanComponents_le_harmonic_sqrt_add_three {n : ℕ} (hn : 0 < n) :
    weightedRamanujanComponents n ≤ (harmonic (Nat.sqrt n) : ℝ) + 3 := by
  classical
  let K : ℕ := Nat.sqrt n
  have hsplit :
      weightedRamanujanComponents n =
        (∑ i ∈ (Finset.range n).filter fun i => i < K,
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) +
        (∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) := by
    unfold weightedRamanujanComponents
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range n)
      (p := fun i => i < K)
      (f := fun i => ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ)))]
    refine congrArg₂ HAdd.hAdd ?_ ?_
    · rfl
    · refine Finset.sum_congr ?_ ?_
      · ext i
        simp [not_lt]
      · intro i hi
        rfl
  have hhead :
      (∑ i ∈ (Finset.range n).filter fun i => i < K,
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤
        (harmonic K : ℝ) := by
    calc
      (∑ i ∈ (Finset.range n).filter fun i => i < K,
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤
        ∑ i ∈ (Finset.range n).filter fun i => i < K,
          (((i + 1 : ℕ) : ℝ)⁻¹) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hi_range : i ∈ Finset.range n := (Finset.mem_filter.mp hi).1
          have hle := ramanujanQTerm_le_one (n := n) (k := i)
            (Nat.le_of_lt (Finset.mem_range.mp hi_range))
          have hden : 0 ≤ (((i + 1 : ℕ) : ℝ)) := by positivity
          simpa [one_div] using div_le_div_of_nonneg_right hle hden
      _ ≤ ∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ)⁻¹) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro i hi
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
          · intro i hi _hi_not
            positivity
      _ = (harmonic K : ℝ) := (harmonic_real_eq_sum_inv K).symm
  have htail :
      (∑ i ∈ (Finset.range n).filter fun i => K ≤ i,
          ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ))) ≤ 3 := by
    simpa [K] using weightedRamanujanComponents_tail_le_three (n := n) hn
  rw [hsplit]
  exact add_le_add hhead htail

private lemma harmonic_nat_sqrt_le_log_half_add_one {n : ℕ} (hn : 0 < n) :
    (harmonic (Nat.sqrt n) : ℝ) ≤ Real.log (n : ℝ) / 2 + 1 := by
  have hspos : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
  have hH := harmonic_le_one_add_log (Nat.sqrt n)
  have hlog_le :
      Real.log (Nat.sqrt n : ℝ) ≤ Real.log (Real.sqrt (n : ℝ)) := by
    exact Real.log_le_log (by exact_mod_cast hspos) Real.nat_sqrt_le_real_sqrt
  have hlogsqrt :
      Real.log (Real.sqrt (n : ℝ)) = Real.log (n : ℝ) / 2 := by
    rw [Real.log_sqrt (by positivity : 0 ≤ (n : ℝ))]
  calc
    (harmonic (Nat.sqrt n) : ℝ) ≤ 1 + Real.log (Nat.sqrt n : ℝ) := hH
    _ ≤ 1 + Real.log (Real.sqrt (n : ℝ)) := by linarith
    _ = Real.log (n : ℝ) / 2 + 1 := by rw [hlogsqrt]; ring

private lemma weightedRamanujanComponents_le_log_half_add_four {n : ℕ} (hn : 0 < n) :
    weightedRamanujanComponents n ≤ Real.log (n : ℝ) / 2 + 4 := by
  have h := weightedRamanujanComponents_le_harmonic_sqrt_add_three (n := n) hn
  have hH := harmonic_nat_sqrt_le_log_half_add_one (n := n) hn
  linarith

private lemma exists_nat_one_sub_inv_two_sq_gt {a : ℝ} (ha : a < 1) :
    ∃ L : ℕ, 0 < L ∧ a < 1 - 1 / (2 * (L : ℝ) ^ 2) := by
  let δ : ℝ := 1 - a
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨L, hL⟩ := exists_nat_gt (max (1 : ℝ) (1 / (2 * δ)))
  have hL_one : (1 : ℝ) < (L : ℝ) := (max_lt_iff.mp hL).1
  have hL_bound : 1 / (2 * δ) < (L : ℝ) := (max_lt_iff.mp hL).2
  have hLpos : 0 < L := by
    exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hL_one)
  have hL_le_sq : (L : ℝ) ≤ (L : ℝ) ^ 2 := by
    nlinarith [le_of_lt hL_one]
  have hbound_sq : 1 / (2 * δ) < (L : ℝ) ^ 2 :=
    hL_bound.trans_le hL_le_sq
  have hmain : (1 : ℝ) < 2 * δ * (L : ℝ) ^ 2 := by
    have htmp := mul_lt_mul_of_pos_left hbound_sq
      (by positivity : (0 : ℝ) < 2 * δ)
    have hleft : (2 * δ) * (1 / (2 * δ)) = (1 : ℝ) := by
      field_simp [hδ.ne']
    rw [hleft] at htmp
    nlinarith
  have hinv : 1 / (2 * (L : ℝ) ^ 2) < δ := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ 2)]
    nlinarith
  refine ⟨L, hLpos, ?_⟩
  dsimp [δ] at hinv
  linarith

private lemma nat_sqrt_div_add_one_ge_real_sqrt_div {L n : ℕ} (hL : 0 < L) (hn : 0 < n) :
    Real.sqrt (n : ℝ) / (2 * (L : ℝ)) ≤
      ((Nat.sqrt n / L + 1 : ℕ) : ℝ) := by
  let s : ℕ := Nat.sqrt n
  have hspos : 0 < s := by
    dsimp [s]
    exact Nat.sqrt_pos.mpr hn
  have hs_one : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hspos
  have hsqrt_le_two_s :
      Real.sqrt (n : ℝ) ≤ 2 * (s : ℝ) := by
    have hsqrtle : Real.sqrt (n : ℝ) ≤ (s : ℝ) + 1 := by
      simpa [s, Nat.cast_add, Nat.cast_one] using
        Real.real_sqrt_le_nat_sqrt_succ (a := n)
    have htwo : (s : ℝ) + 1 ≤ 2 * (s : ℝ) := by nlinarith
    exact hsqrtle.trans htwo
  have hLpos_real : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hdivlt_nat : s < (s / L + 1) * L := by
    have hlt : s / L < s / L + 1 := Nat.lt_succ_self _
    exact (Nat.div_lt_iff_lt_mul hL).mp hlt
  have hs_div_le : (s : ℝ) / (L : ℝ) ≤ ((s / L + 1 : ℕ) : ℝ) := by
    have hcast : (s : ℝ) < ((s / L + 1 : ℕ) : ℝ) * (L : ℝ) := by
      exact_mod_cast hdivlt_nat
    rw [div_le_iff₀ hLpos_real]
    exact le_of_lt (by simpa [mul_comm] using hcast)
  calc
    Real.sqrt (n : ℝ) / (2 * (L : ℝ)) ≤
        (2 * (s : ℝ)) / (2 * (L : ℝ)) := by
      exact div_le_div_of_nonneg_right hsqrt_le_two_s (by positivity)
    _ = (s : ℝ) / (L : ℝ) := by field_simp [hLpos_real.ne']
    _ ≤ ((s / L + 1 : ℕ) : ℝ) := hs_div_le

private lemma log_half_sub_log_two_mul_le_log_nat_sqrt_div_add_one
    {L n : ℕ} (hL : 0 < L) (hn : 0 < n) :
    Real.log (n : ℝ) / 2 - Real.log (2 * (L : ℝ)) ≤
      Real.log (((Nat.sqrt n / L + 1 : ℕ) : ℝ)) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hleft_pos : 0 < Real.sqrt (n : ℝ) / (2 * (L : ℝ)) := by
    positivity
  have hle := nat_sqrt_div_add_one_ge_real_sqrt_div (L := L) (n := n) hL hn
  have hlog :=
    Real.log_le_log hleft_pos hle
  have hlog_left :
      Real.log (Real.sqrt (n : ℝ) / (2 * (L : ℝ))) =
        Real.log (n : ℝ) / 2 - Real.log (2 * (L : ℝ)) := by
    rw [Real.log_div (by positivity : Real.sqrt (n : ℝ) ≠ 0)
      (by positivity : (2 * (L : ℝ)) ≠ 0)]
    rw [Real.log_sqrt (by positivity : 0 ≤ (n : ℝ))]
  simpa [hlog_left] using hlog

private lemma ramanujanQTerm_ge_one_sub_inv_two_sq_of_lt_sqrt_div
    {L n i : ℕ} (hL : 0 < L) (hn : 0 < n) (hi : i < Nat.sqrt n / L) :
    (1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2) ≤ ramanujanQTerm n i := by
  let K : ℕ := Nat.sqrt n / L
  have hiK_succ : i + 1 ≤ K := Nat.succ_le_of_lt hi
  have hLK_le_sqrt : L * (i + 1) ≤ Nat.sqrt n := by
    have hmul : L * (i + 1) ≤ L * K := Nat.mul_le_mul_left L hiK_succ
    have hLK : L * K ≤ Nat.sqrt n := by
      dsimp [K]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (Nat.sqrt n) L
    exact hmul.trans hLK
  have hLi_le_sqrt : L * i ≤ Nat.sqrt n := by
    exact (Nat.mul_le_mul_left L (Nat.le_succ i)).trans hLK_le_sqrt
  have hmul_nat : (L * i) * (L * (i + 1)) ≤ n := by
    calc
      (L * i) * (L * (i + 1)) ≤ Nat.sqrt n * Nat.sqrt n :=
        Nat.mul_le_mul hLi_le_sqrt hLK_le_sqrt
      _ ≤ n := Nat.sqrt_le n
  have hi_le_n : i ≤ n := by
    calc
      i ≤ Nat.sqrt n := by
        exact (le_of_lt hi).trans (Nat.div_le_self (Nat.sqrt n) L)
      _ ≤ n := Nat.sqrt_le_self n
  have hsum := one_sub_sum_le_ramanujanQTerm (n := n) (k := i) hi_le_n
  have hquad :
      ((i : ℝ) * ((i : ℝ) + 1) / 2) / (n : ℝ) ≤
        1 / (2 * (L : ℝ) ^ 2) := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hmul_real :
        ((L : ℝ) * (i : ℝ)) * ((L : ℝ) * ((i + 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
      exact_mod_cast hmul_nat
    rw [Nat.cast_add, Nat.cast_one] at hmul_real
    field_simp [hnpos.ne', hLpos.ne']
    nlinarith [hmul_real]
  have hsum_eval :
      (∑ j ∈ Finset.range i, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) =
        (((i : ℝ) * ((i : ℝ) + 1) / 2) / (n : ℝ)) := by
    simpa [Nat.cast_add] using sum_range_succ_cast_div i n
  calc
    (1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2) ≤
        1 - (∑ j ∈ Finset.range i, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      rw [hsum_eval]
      linarith
    _ ≤ ramanujanQTerm n i := hsum

private lemma weightedRamanujanComponents_lower_fixed
    {L n : ℕ} (hL : 0 < L) (hn : 0 < n) :
    ((1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2)) *
        (harmonic (Nat.sqrt n / L) : ℝ) ≤
      weightedRamanujanComponents n := by
  classical
  let K : ℕ := Nat.sqrt n / L
  have hK_le_n : K ≤ n := by
    dsimp [K]
    exact (Nat.div_le_self (Nat.sqrt n) L).trans (Nat.sqrt_le_self n)
  have hsubset : Finset.range K ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hK_le_n)
  have halpha_nonneg : 0 ≤ (1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2) := by
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hLsq_ge : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
      nlinarith [show (1 : ℝ) ≤ (L : ℝ) by exact_mod_cast hL]
    have hinv_le : 1 / (2 * (L : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one₀ (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ 2)]
      nlinarith
    linarith
  calc
    ((1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2)) *
        (harmonic K : ℝ) =
      ∑ i ∈ Finset.range K,
        ((1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2)) / (((i + 1 : ℕ) : ℝ)) := by
        rw [harmonic_real_eq_sum_inv, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [div_eq_mul_inv]
        ring
    _ ≤ ∑ i ∈ Finset.range K,
        ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hterm := ramanujanQTerm_ge_one_sub_inv_two_sq_of_lt_sqrt_div
          (L := L) (n := n) (i := i) hL hn (Finset.mem_range.mp hi)
        exact div_le_div_of_nonneg_right hterm (by positivity)
    _ ≤ ∑ i ∈ Finset.range n,
        ramanujanQTerm n i / (((i + 1 : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
        intro i hi _hi_not
        have hnonneg := ramanujanQTerm_nonneg (n := n) (k := i)
          (Nat.le_of_lt (Finset.mem_range.mp hi))
        exact div_nonneg hnonneg (by positivity)
    _ = weightedRamanujanComponents n := by
        simp [weightedRamanujanComponents]

private lemma weightedRamanujanComponents_lower_log_fixed
    {L n : ℕ} (hL : 0 < L) (hn : 0 < n) :
    ((1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2)) *
        (Real.log (n : ℝ) / 2 - Real.log (2 * (L : ℝ))) ≤
      weightedRamanujanComponents n := by
  let α : ℝ := (1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2)
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    have hLsq_ge : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by
      nlinarith [show (1 : ℝ) ≤ (L : ℝ) by exact_mod_cast hL]
    have hinv_le : 1 / (2 * (L : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one₀ (by positivity : (0 : ℝ) < 2 * (L : ℝ) ^ 2)]
      nlinarith
    linarith
  have hlog :
      Real.log (n : ℝ) / 2 - Real.log (2 * (L : ℝ)) ≤
        Real.log (((Nat.sqrt n / L + 1 : ℕ) : ℝ)) :=
    log_half_sub_log_two_mul_le_log_nat_sqrt_div_add_one (L := L) (n := n) hL hn
  have hH :
      Real.log (((Nat.sqrt n / L + 1 : ℕ) : ℝ)) ≤
        (harmonic (Nat.sqrt n / L) : ℝ) := by
    simpa using log_add_one_le_harmonic (Nat.sqrt n / L)
  have hfixed := weightedRamanujanComponents_lower_fixed (L := L) (n := n) hL hn
  calc
    α * (Real.log (n : ℝ) / 2 - Real.log (2 * (L : ℝ))) ≤
        α * (harmonic (Nat.sqrt n / L) : ℝ) :=
      mul_le_mul_of_nonneg_left (hlog.trans hH) hα_nonneg
    _ ≤ weightedRamanujanComponents n := by
      simpa [α] using hfixed

private lemma eventually_weighted_ratio_le_of_gt_one {a : ℝ} (ha : 1 < a) :
    ∀ᶠ n : ℕ in atTop,
      weightedRamanujanComponents n / (Real.log (n : ℝ) / 2) < a := by
  let g : ℕ → ℝ := fun n => Real.log (n : ℝ) / 2
  have hg : Tendsto g atTop atTop := componentLogScale_tendsto_atTop
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (4 : ℝ) / g n < a - 1 :=
    (Filter.Tendsto.const_div_atTop hg (4 : ℝ)).eventually
      (gt_mem_nhds (sub_pos.mpr ha))
  filter_upwards [hsmall, hg.eventually_gt_atTop (0 : ℝ),
    eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hsmall hgpos hn
  have hnpos : 0 < n := by omega
  have hupper := weightedRamanujanComponents_le_log_half_add_four (n := n) hnpos
  have hratio :
      weightedRamanujanComponents n / g n ≤ 1 + 4 / g n := by
    calc
      weightedRamanujanComponents n / g n ≤ (g n + 4) / g n :=
        div_le_div_of_nonneg_right (by simpa [g] using hupper) hgpos.le
      _ = 1 + 4 / g n := by
        field_simp [hgpos.ne']
  change weightedRamanujanComponents n / g n < a
  linarith

private lemma eventually_weighted_ratio_ge_of_lt_one {a : ℝ} (ha : a < 1) :
    ∀ᶠ n : ℕ in atTop,
      a < weightedRamanujanComponents n / (Real.log (n : ℝ) / 2) := by
  obtain ⟨L, hLpos, hLa⟩ := exists_nat_one_sub_inv_two_sq_gt ha
  let α : ℝ := (1 : ℝ) - 1 / (2 * (L : ℝ) ^ 2)
  let C : ℝ := Real.log (2 * (L : ℝ))
  have hαa : a < α := by simpa [α] using hLa
  have hgap : 0 < α - a := sub_pos.mpr hαa
  let g : ℕ → ℝ := fun n => Real.log (n : ℝ) / 2
  have hg : Tendsto g atTop atTop := componentLogScale_tendsto_atTop
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (α * C) / g n < α - a :=
    (Filter.Tendsto.const_div_atTop hg (α * C)).eventually (gt_mem_nhds hgap)
  filter_upwards [hsmall, hg.eventually_gt_atTop (0 : ℝ),
    eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hsmall hgpos hn
  have hnpos : 0 < n := by omega
  have hlower := weightedRamanujanComponents_lower_log_fixed
    (L := L) (n := n) hLpos hnpos
  have hratio_lower :
      α - (α * C) / g n ≤ weightedRamanujanComponents n / g n := by
    calc
      α - (α * C) / g n =
          (α * (g n - C)) / g n := by
            field_simp [hgpos.ne']
      _ ≤ weightedRamanujanComponents n / g n :=
        div_le_div_of_nonneg_right (by simpa [α, C, g] using hlower) hgpos.le
  change a < weightedRamanujanComponents n / g n
  linarith

theorem weightedRamanujanComponents_tendsto_ratio_one :
    Tendsto
      (fun n : ℕ => weightedRamanujanComponents n / (Real.log (n : ℝ) / 2))
      atTop (𝓝 1) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact eventually_weighted_ratio_ge_of_lt_one ha
  · intro a ha
    exact eventually_weighted_ratio_le_of_gt_one ha

theorem weightedRamanujanComponents_isEquivalent :
    (fun n : ℕ => weightedRamanujanComponents n) ~[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / 2) := by
  exact Asymptotics.isEquivalent_of_tendsto_one weightedRamanujanComponents_tendsto_ratio_one

theorem componentExpectationFormula_isEquivalent :
    (fun n : ℕ => componentExpectationFormula n) ~[atTop]
      (fun n : ℕ => Real.log (n : ℝ) / 2) := by
  refine weightedRamanujanComponents_isEquivalent.congr_left ?_
  exact eventually_atTop.2 ⟨1, fun n hn => by
    exact (componentExpectationFormula_eq_weightedRamanujan (n := n) (by omega)).symm⟩

theorem expected_components_isEquivalent :
    (fun n : ℕ => (∑ f : Fin n → Fin n, (componentCount f : ℝ)) / (n : ℝ)^n)
      ~[atTop] (fun n : ℕ => Real.log (n : ℝ) / 2) := by
  refine componentExpectationFormula_isEquivalent.congr_left ?_
  exact eventually_atTop.2 ⟨1, fun n hn => by
    exact (expected_components_eq (n := n) (by omega)).symm⟩

end Sharp

end

end AnalyticCombinatorics.Ch2.Mappings.MappingComponentsNS
