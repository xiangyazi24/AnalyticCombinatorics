import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.SigmaRecurrence

namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

open scoped BigOperators
open Finset

noncomputable section

private lemma Ioc_zero_eq_Icc_one (n : ℕ) :
    Finset.Ioc 0 n = Finset.Icc 1 n := by
  ext k
  simp [Nat.succ_le_iff]

private lemma sum_Icc_one_nat_cast (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := n) (f := fun k : ℕ => (k : ℝ))
        (by omega)]
      rw [ih]
      norm_num
      ring

private lemma sigma_summatory_eq_triangular (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, sigmaR m) =
      ∑ q ∈ Finset.Icc 1 N,
        ((N / q : ℕ) : ℝ) * (((N / q : ℕ) : ℝ) + 1) / 2 := by
  classical
  have hnat :
      (∑ m ∈ Finset.Icc 1 N, ArithmeticFunction.sigma 1 m) =
        ∑ q ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / q), d := by
    have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
      (ArithmeticFunction.zeta : ArithmeticFunction ℕ)
      (ArithmeticFunction.pow 1) N
    rw [ArithmeticFunction.zeta_mul_pow_eq_sigma] at h
    have h' :
        (∑ m ∈ Finset.Icc 1 N, ArithmeticFunction.sigma 1 m) =
          ∑ q ∈ Finset.Icc 1 N,
            if q = 0 then 0 else ∑ d ∈ Finset.Icc 1 (N / q), d := by
      simpa [Ioc_zero_eq_Icc_one, ArithmeticFunction.zeta_apply,
        ArithmeticFunction.pow_apply] using h
    refine h'.trans ?_
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hq0 : q ≠ 0 := by
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      omega
    simp [hq0]
  have hreal := congrArg (fun a : ℕ => (a : ℝ)) hnat
  calc
    (∑ m ∈ Finset.Icc 1 N, sigmaR m)
        = ∑ q ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / q), (d : ℝ) := by
          simpa [sigmaR, Nat.cast_sum] using hreal
    _ = ∑ q ∈ Finset.Icc 1 N,
        ((N / q : ℕ) : ℝ) * (((N / q : ℕ) : ℝ) + 1) / 2 := by
          refine Finset.sum_congr rfl ?_
          intro q _hq
          exact sum_Icc_one_nat_cast (N / q)

private lemma hasSum_one_div_nat_sq :
    HasSum (fun n : ℕ => (((n : ℝ) ^ 2)⁻¹)) (Real.pi ^ 2 / 6) := by
  simpa [one_div] using hasSum_zeta_two

private lemma sum_range_succ_inv_sq_eq_sum_Icc (N : ℕ) :
    (∑ q ∈ Finset.range (N + 1), (((q : ℝ) ^ 2)⁻¹)) =
      ∑ q ∈ Finset.Icc 1 N, (((q : ℝ) ^ 2)⁻¹) := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := Ioc_zero_eq_Icc_one N
  rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc,
    Finset.Icc_eq_cons_Ioc (Nat.zero_le N)]
  simp [hIoc]

private lemma basel_partial_bounds {N : ℕ} (hN : 1 ≤ N) :
    let P := ∑ q ∈ Finset.Icc 1 N, (((q : ℝ) ^ 2)⁻¹)
    P ≤ Real.pi ^ 2 / 6 ∧ Real.pi ^ 2 / 6 ≤ P + ((N : ℝ)⁻¹) := by
  classical
  let f : ℕ → ℝ := fun n => (((n : ℝ) ^ 2)⁻¹)
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    positivity
  have hf_hasSum : HasSum f (Real.pi ^ 2 / 6) := by
    simpa [f] using hasSum_one_div_nat_sq
  let P : ℝ := ∑ q ∈ Finset.Icc 1 N, f q
  have hP_range : (∑ q ∈ Finset.range (N + 1), f q) = P := by
    dsimp [P, f]
    exact sum_range_succ_inv_sq_eq_sum_Icc N
  have hlower : P ≤ Real.pi ^ 2 / 6 := by
    exact sum_le_hasSum (Finset.Icc 1 N) (fun q _hq => hf_nonneg q) hf_hasSum
  have hbound_range : ∀ r : ℕ, (∑ q ∈ Finset.range r, f q) ≤ P + ((N : ℝ)⁻¹) := by
    intro r
    by_cases hr : r ≤ N + 1
    · have hsubset : Finset.range r ⊆ Finset.range (N + 1) := by
        intro q hq
        exact Finset.mem_range.mpr ((Finset.mem_range.mp hq).trans_le hr)
      have hle : (∑ q ∈ Finset.range r, f q) ≤ ∑ q ∈ Finset.range (N + 1), f q := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun q _hq _hnot => hf_nonneg q)
      calc
        (∑ q ∈ Finset.range r, f q) ≤ P := by simpa [hP_range] using hle
        _ ≤ P + ((N : ℝ)⁻¹) := by
          have hnonneg : 0 ≤ ((N : ℝ)⁻¹) := by positivity
          linarith
    · have hrle : N + 1 ≤ r := Nat.le_of_not_ge hr
      have htail_subset : Finset.Ico (N + 1) r ⊆ Finset.Ioc N r := by
        intro q hq
        simp only [Finset.mem_Ico, Finset.mem_Ioc] at hq ⊢
        omega
      have htail_le_Ioc :
          (∑ q ∈ Finset.Ico (N + 1) r, f q) ≤
            ∑ q ∈ Finset.Ioc N r, f q := by
        exact Finset.sum_le_sum_of_subset_of_nonneg htail_subset
          (fun q _hq _hnot => hf_nonneg q)
      have htail_Ioc :
          (∑ q ∈ Finset.Ioc N r, f q) ≤ ((N : ℝ)⁻¹) - ((r : ℝ)⁻¹) := by
        simpa [f] using
          (sum_Ioc_inv_sq_le_sub (α := ℝ) (k := N) (n := r)
            (Nat.ne_of_gt hN) (by omega))
      have htail_le :
          (∑ q ∈ Finset.Ico (N + 1) r, f q) ≤ ((N : ℝ)⁻¹) := by
        have hr_nonneg : 0 ≤ ((r : ℝ)⁻¹) := by positivity
        exact htail_le_Ioc.trans (htail_Ioc.trans (by linarith))
      calc
        (∑ q ∈ Finset.range r, f q)
            = (∑ q ∈ Finset.range (N + 1), f q) +
                ∑ q ∈ Finset.Ico (N + 1) r, f q := by
              rw [Finset.sum_range_add_sum_Ico _ hrle]
        _ ≤ P + ((N : ℝ)⁻¹) := by
              nlinarith [hP_range, htail_le]
  have hupper :
      Real.pi ^ 2 / 6 ≤ P + ((N : ℝ)⁻¹) := by
    have htsum_le := Real.tsum_le_of_sum_range_le hf_nonneg hbound_range
    simpa [hf_hasSum.tsum_eq] using htsum_le
  exact ⟨hlower, hupper⟩

private lemma triangular_error_of_floor {y j : ℝ} (hy1 : 1 ≤ y) (hj0 : 0 ≤ j)
    (hj_le : j ≤ y) (hy_lt : y < j + 1) :
    |j * (j + 1) / 2 - y ^ 2 / 2| ≤ 2 * y := by
  have hy0 : 0 ≤ y := zero_le_one.trans hy1
  have hy_le_j1 : y ≤ j + 1 := hy_lt.le
  have hdiff_nonneg : 0 ≤ y - j := sub_nonneg.mpr hj_le
  have hdiff_le : y - j ≤ 1 := by linarith
  have hj1_nonneg : 0 ≤ j + 1 := by nlinarith
  have hj1_le : j + 1 ≤ 2 * y := by nlinarith
  have hprod_le : (y - j) * (j + 1) ≤ 1 * (2 * y) :=
    mul_le_mul hdiff_le hj1_le hj1_nonneg (by norm_num)
  have hsq_le_yj : y ^ 2 ≤ y * (j + 1) := by
    have := mul_nonneg hy0 (sub_nonneg.mpr hy_le_j1)
    nlinarith
  have hlow_aux : y ^ 2 - j * (j + 1) ≤ (y - j) * (j + 1) := by
    nlinarith
  have hlow : y ^ 2 / 2 - j * (j + 1) / 2 ≤ 2 * y := by
    nlinarith
  have hsq_j_le_y : j ^ 2 ≤ y ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hj_le) (add_nonneg hy0 hj0)
    nlinarith
  have hupper : j * (j + 1) / 2 - y ^ 2 / 2 ≤ 2 * y := by
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

private lemma triangular_term_error {N q : ℕ} (hq : 1 ≤ q) (hqN : q ≤ N) :
    |((N / q : ℕ) : ℝ) * (((N / q : ℕ) : ℝ) + 1) / 2 -
        ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)| ≤
      2 * (N : ℝ) * ((q : ℝ)⁻¹) := by
  let y : ℝ := (N : ℝ) / (q : ℝ)
  let j : ℝ := ((N / q : ℕ) : ℝ)
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq_ne : (q : ℝ) ≠ 0 := hq_pos.ne'
  have hj0 : 0 ≤ j := by dsimp [j]; positivity
  have hj_le : j ≤ y := by
    dsimp [j, y]
    exact Nat.cast_div_le
  have hy_lt : y < j + 1 := by
    have hfloor :
        Nat.floor ((N : ℝ) / (q : ℝ)) = N / q := by
      simpa using (Nat.floor_div_eq_div (K := ℝ) N q)
    dsimp [y, j]
    simpa [hfloor] using Nat.lt_floor_add_one ((N : ℝ) / (q : ℝ))
  have hy1 : 1 ≤ y := by
    have hqN_real : (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hqN
    have hmul : (1 : ℝ) * (q : ℝ) ≤ y * (q : ℝ) := by
      dsimp [y]
      field_simp [hq_ne]
      exact hqN_real
    exact (mul_le_mul_iff_right₀ hq_pos).mp (by simpa [mul_comm] using hmul)
  have h := triangular_error_of_floor hy1 hj0 hj_le hy_lt
  dsimp [y, j] at h
  have hquad :
      ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹) =
        ((N : ℝ) / (q : ℝ)) ^ 2 / 2 := by
    field_simp [hq_ne]
  have hrhs :
      2 * (N : ℝ) * ((q : ℝ)⁻¹) = 2 * ((N : ℝ) / (q : ℝ)) := by
    field_simp [hq_ne]
  simpa [hquad, hrhs] using h

private lemma harmonic_sum_Icc_inv (N : ℕ) :
    (∑ q ∈ Finset.Icc 1 N, ((q : ℝ)⁻¹)) = (harmonic N : ℝ) := by
  have h :
      ((harmonic N : ℚ) : ℝ) =
        ∑ q ∈ Finset.Icc 1 N, ((q : ℝ)⁻¹) := by
    simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact h.symm

private lemma log_two_mul_nat_ge_half {N : ℕ} (hN : 1 ≤ N) :
    (1 / 2 : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have harg : (2 : ℝ) ≤ 2 * (N : ℝ) := by
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  exact hlog2.trans (Real.log_le_log (by norm_num) harg)

private lemma log_two_mul_ge_half {x : ℝ} (hx : 1 ≤ x) :
    (1 / 2 : ℝ) ≤ Real.log (2 * x) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have harg : (2 : ℝ) ≤ 2 * x := by nlinarith
  exact hlog2.trans (Real.log_le_log (by norm_num) harg)

private lemma one_add_log_nat_le_three_log_two_mul {N : ℕ} (hN : 1 ≤ N) :
    1 + Real.log (N : ℝ) ≤ 3 * Real.log (2 * (N : ℝ)) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have harg : (N : ℝ) ≤ 2 * (N : ℝ) := by nlinarith [show (0 : ℝ) ≤ N by positivity]
  have hlog_le : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log hNpos harg
  have hhalf := log_two_mul_nat_ge_half hN
  nlinarith

private lemma triangular_summatory_error {N : ℕ} (hN : 1 ≤ N) :
    |(∑ q ∈ Finset.Icc 1 N,
        ((N / q : ℕ) : ℝ) * (((N / q : ℕ) : ℝ) + 1) / 2) -
      ∑ q ∈ Finset.Icc 1 N,
        ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)| ≤
      6 * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
  classical
  let T : ℕ → ℝ := fun q =>
    ((N / q : ℕ) : ℝ) * (((N / q : ℕ) : ℝ) + 1) / 2
  let Q : ℕ → ℝ := fun q =>
    ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)
  have hterm :
      |(∑ q ∈ Finset.Icc 1 N, T q) - ∑ q ∈ Finset.Icc 1 N, Q q| ≤
        ∑ q ∈ Finset.Icc 1 N, 2 * (N : ℝ) * ((q : ℝ)⁻¹) := by
    calc
      |(∑ q ∈ Finset.Icc 1 N, T q) - ∑ q ∈ Finset.Icc 1 N, Q q|
          = |∑ q ∈ Finset.Icc 1 N, (T q - Q q)| := by
              rw [Finset.sum_sub_distrib]
      _ ≤ ∑ q ∈ Finset.Icc 1 N, |T q - Q q| :=
              Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Finset.Icc 1 N, 2 * (N : ℝ) * ((q : ℝ)⁻¹) := by
              refine Finset.sum_le_sum ?_
              intro q hq
              have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
              have hqN : q ≤ N := (Finset.mem_Icc.mp hq).2
              simpa [T, Q] using triangular_term_error (N := N) (q := q) hq1 hqN
  have hfactor :
      (∑ q ∈ Finset.Icc 1 N, 2 * (N : ℝ) * ((q : ℝ)⁻¹)) =
        2 * (N : ℝ) * (harmonic N : ℝ) := by
    rw [← harmonic_sum_Icc_inv N]
    exact (Finset.mul_sum (s := Finset.Icc 1 N)
      (a := 2 * (N : ℝ)) (f := fun q => ((q : ℝ)⁻¹))).symm
  have hH : (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) :=
    harmonic_le_one_add_log N
  have hlog := one_add_log_nat_le_three_log_two_mul hN
  calc
    |(∑ q ∈ Finset.Icc 1 N, T q) - ∑ q ∈ Finset.Icc 1 N, Q q|
        ≤ ∑ q ∈ Finset.Icc 1 N, 2 * (N : ℝ) * ((q : ℝ)⁻¹) := hterm
    _ = 2 * (N : ℝ) * (harmonic N : ℝ) := hfactor
    _ ≤ 2 * (N : ℝ) * (1 + Real.log (N : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ 6 * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
          have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * (N : ℝ))
          nlinarith

private lemma basel_weighted_error {N : ℕ} (hN : 1 ≤ N) :
    |(∑ q ∈ Finset.Icc 1 N,
        ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)) -
      (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| ≤ (N : ℝ) / 2 := by
  classical
  let P : ℝ := ∑ q ∈ Finset.Icc 1 N, (((q : ℝ) ^ 2)⁻¹)
  let C : ℝ := (N : ℝ) ^ 2 / 2
  have hb := basel_partial_bounds (N := N) hN
  dsimp only at hb
  have hP_le : P ≤ Real.pi ^ 2 / 6 := by
    simpa [P] using hb.1
  have htail : Real.pi ^ 2 / 6 - P ≤ ((N : ℝ)⁻¹) := by
    have h := hb.2
    simpa [P] using (sub_le_iff_le_add'.mpr h)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hsum :
      (∑ q ∈ Finset.Icc 1 N,
        ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)) = C * P := by
    dsimp [C, P]
    exact (Finset.mul_sum (s := Finset.Icc 1 N)
      (a := (N : ℝ) ^ 2 / 2) (f := fun q => (((q : ℝ) ^ 2)⁻¹))).symm
  have htarget : (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 = C * (Real.pi ^ 2 / 6) := by
    dsimp [C]
    ring
  have hnonpos : C * P - C * (Real.pi ^ 2 / 6) ≤ 0 := by
    exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left hP_le hC_nonneg)
  calc
    |(∑ q ∈ Finset.Icc 1 N,
        ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)) -
      (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2|
        = |C * P - C * (Real.pi ^ 2 / 6)| := by rw [hsum, htarget]
    _ = C * (Real.pi ^ 2 / 6 - P) := by
          rw [abs_of_nonpos hnonpos]
          ring
    _ ≤ C * ((N : ℝ)⁻¹) := by
          exact mul_le_mul_of_nonneg_left htail hC_nonneg
    _ = (N : ℝ) / 2 := by
          have hNpos : (N : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hN)
          dsimp [C]
          field_simp [hNpos]

private lemma sigma_summatory_nat_bound {N : ℕ} (hN : 1 ≤ N) :
    |(∑ m ∈ Finset.Icc 1 N, sigmaR m) -
      (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| ≤
      7 * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
  classical
  let T : ℕ → ℝ := fun q =>
    ((N / q : ℕ) : ℝ) * (((N / q : ℕ) : ℝ) + 1) / 2
  let Q : ℕ → ℝ := fun q =>
    ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)
  have htri := triangular_summatory_error (N := N) hN
  have hbasel := basel_weighted_error (N := N) hN
  have hhalf :
      (N : ℝ) / 2 ≤ (N : ℝ) * Real.log (2 * (N : ℝ)) := by
    have hlog := log_two_mul_nat_ge_half hN
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (N : ℝ))
    nlinarith
  calc
    |(∑ m ∈ Finset.Icc 1 N, sigmaR m) -
      (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2|
        = |(∑ q ∈ Finset.Icc 1 N, T q) -
            (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| := by
              rw [sigma_summatory_eq_triangular]
    _ ≤ |(∑ q ∈ Finset.Icc 1 N, T q) - ∑ q ∈ Finset.Icc 1 N, Q q| +
          |(∑ q ∈ Finset.Icc 1 N, Q q) -
            (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| :=
          abs_sub_le _ _ _
    _ ≤ 7 * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
          have htri' : |(∑ q ∈ Finset.Icc 1 N, T q) - ∑ q ∈ Finset.Icc 1 N, Q q| ≤
              6 * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
            simpa [T, Q] using htri
          have hbasel' : |(∑ q ∈ Finset.Icc 1 N, Q q) -
              (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| ≤ (N : ℝ) / 2 := by
            simpa [Q] using hbasel
          nlinarith [htri', hbasel', hhalf]

private lemma floor_quadratic_error {x : ℝ} (hx : 1 ≤ x) :
    |(Real.pi ^ 2 / 12) * (⌊x⌋₊ : ℝ) ^ 2 -
      (Real.pi ^ 2 / 12) * x ^ 2| ≤
      Real.pi ^ 2 * x * Real.log (2 * x) := by
  let N : ℕ := ⌊x⌋₊
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hN_le : (N : ℝ) ≤ x := by
    dsimp [N]
    exact Nat.floor_le hx0
  have hx_lt : x < (N : ℝ) + 1 := by
    dsimp [N]
    exact Nat.lt_floor_add_one x
  have hdiff_nonneg : 0 ≤ x - (N : ℝ) := sub_nonneg.mpr hN_le
  have hdiff_le : x - (N : ℝ) ≤ 1 := by linarith
  have hsum_nonneg : 0 ≤ x + (N : ℝ) := by positivity
  have hsum_le : x + (N : ℝ) ≤ 2 * x := by nlinarith
  have hsquares : x ^ 2 - (N : ℝ) ^ 2 ≤ 2 * x := by
    have hmul : (x - (N : ℝ)) * (x + (N : ℝ)) ≤ 1 * (2 * x) :=
      mul_le_mul hdiff_le hsum_le hsum_nonneg (by norm_num)
    nlinarith
  have hsquares_nonneg : 0 ≤ x ^ 2 - (N : ℝ) ^ 2 := by
    have hmul_nonneg := mul_nonneg (sub_nonneg.mpr hN_le) (add_nonneg hx0 (by positivity))
    nlinarith
  have hconst_nonneg : 0 ≤ Real.pi ^ 2 / 12 := by positivity
  have hbasic :
      |(Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 -
        (Real.pi ^ 2 / 12) * x ^ 2| ≤
        2 * (Real.pi ^ 2 / 12) * x := by
    have hnonpos :
        (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 -
          (Real.pi ^ 2 / 12) * x ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg hconst_nonneg hsquares_nonneg]
    rw [abs_of_nonpos hnonpos]
    have hmul := mul_le_mul_of_nonneg_left hsquares hconst_nonneg
    nlinarith
  have hlog := log_two_mul_ge_half hx
  have hpi_x_nonneg : 0 ≤ Real.pi ^ 2 * x := by positivity
  have hlogmul := mul_le_mul_of_nonneg_left hlog hpi_x_nonneg
  exact hbasic.trans (by nlinarith)

theorem sigma_summatory_asymptotic :
    ∃ K, 0 < K ∧ ∀ x : ℝ, 1 ≤ x →
      |(∑ m ∈ Finset.Icc 1 ⌊x⌋₊, sigmaR m) -
        (Real.pi ^ 2 / 12) * x ^ 2| ≤ K * x * Real.log (2 * x) := by
  refine ⟨8 + Real.pi ^ 2, by positivity, ?_⟩
  intro x hx
  let N : ℕ := ⌊x⌋₊
  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.floor_pos.mpr hx
  have hN : 1 ≤ N := hNpos
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hN_le_x : (N : ℝ) ≤ x := by
    dsimp [N]
    exact Nat.floor_le hx0
  have hlogN_nonneg : 0 ≤ Real.log (2 * (N : ℝ)) := by
    have hhalf := log_two_mul_nat_ge_half hN
    linarith
  have hlog_mono :
      Real.log (2 * (N : ℝ)) ≤ Real.log (2 * x) := by
    have harg_pos : 0 < 2 * (N : ℝ) := by positivity
    have harg_le : 2 * (N : ℝ) ≤ 2 * x := by nlinarith
    exact Real.log_le_log harg_pos harg_le
  have hNxlog :
      (N : ℝ) * Real.log (2 * (N : ℝ)) ≤ x * Real.log (2 * x) := by
    exact mul_le_mul hN_le_x hlog_mono hlogN_nonneg hx0
  have hnat := sigma_summatory_nat_bound (N := N) hN
  have hnat_x :
      |(∑ m ∈ Finset.Icc 1 N, sigmaR m) -
        (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| ≤
        7 * x * Real.log (2 * x) := by
    have hmul := mul_le_mul_of_nonneg_left hNxlog (by norm_num : (0 : ℝ) ≤ 7)
    nlinarith [hnat, hmul]
  have hfloor := floor_quadratic_error (x := x) hx
  have hxlog_nonneg : 0 ≤ x * Real.log (2 * x) := by
    have hhalf := log_two_mul_ge_half hx
    exact mul_nonneg hx0 (by linarith)
  calc
    |(∑ m ∈ Finset.Icc 1 ⌊x⌋₊, sigmaR m) -
        (Real.pi ^ 2 / 12) * x ^ 2|
        = |(∑ m ∈ Finset.Icc 1 N, sigmaR m) -
            (Real.pi ^ 2 / 12) * x ^ 2| := by rfl
    _ ≤ |(∑ m ∈ Finset.Icc 1 N, sigmaR m) -
          (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| +
        |(Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 -
          (Real.pi ^ 2 / 12) * x ^ 2| :=
          abs_sub_le _ _ _
    _ ≤ (8 + Real.pi ^ 2) * x * Real.log (2 * x) := by
          have hfloor' :
              |(Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 -
                (Real.pi ^ 2 / 12) * x ^ 2| ≤
                Real.pi ^ 2 * x * Real.log (2 * x) := by
            simpa [N] using hfloor
          nlinarith [hnat_x, hfloor', hxlog_nonneg]

end

end AnalyticCombinatorics.Ch8.Partitions.Sigma
