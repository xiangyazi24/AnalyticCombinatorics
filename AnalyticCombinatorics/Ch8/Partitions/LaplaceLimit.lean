import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.UpperBound
import AnalyticCombinatorics.Ch8.Partitions.LaplaceAsymptotic
import AnalyticCombinatorics.Ch8.Partitions.EulerProduct

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology

-- The log bridge combines finite-product logarithms with several `tsum` reindexing steps.
set_option maxHeartbeats 800000

private noncomputable def logEulerTerm (t : ℝ) (k : ℕ+) : ℝ :=
  -Real.log (1 - Real.exp (-(t * (k : ℝ))))

private noncomputable def logBridgeTerm (t : ℝ) (k j : ℕ+) : ℝ :=
  Real.exp (-(t * (k : ℝ))) ^ (j : ℕ) / (j : ℝ)

private lemma PartLaplace_pos {t : ℝ} (ht : 0 < t) :
    0 < PartLaplace t := by
  have hsum := partLaplace_summable ht
  have hnonneg : ∀ n : ℕ, 0 ≤ part n * Real.exp (-(t * (n : ℝ))) := by
    intro n
    exact mul_nonneg (part_pos n).le (Real.exp_pos _).le
  have hzero :
      0 < (fun n : ℕ => part n * Real.exp (-(t * (n : ℝ)))) 0 := by
    exact mul_pos (part_pos 0) (Real.exp_pos _)
  simpa [PartLaplace] using hsum.tsum_pos hnonneg 0 hzero

private lemma exp_neg_mul_pnat_lt_one {t : ℝ} (ht : 0 < t) (k : ℕ+) :
    Real.exp (-(t * (k : ℝ))) < 1 := by
  have hk : 0 < (k : ℝ) := by exact_mod_cast k.2
  have htk : 0 < t * (k : ℝ) := mul_pos ht hk
  rw [Real.exp_lt_one_iff]
  linarith

private lemma neg_log_one_sub_nonneg {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ -Real.log (1 - y) := by
  exact neg_nonneg.mpr (Real.log_nonpos (sub_nonneg.mpr hy1.le) (by linarith))

private lemma neg_log_one_sub_le_div {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    -Real.log (1 - y) ≤ y / (1 - y) := by
  have hlog := neg_log_one_sub_le_tsum hy0 hy1
  let r : ℝ := y
  have hgeo_tail :
      HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    have hgeo := (hasSum_nat_add_iff' (G := ℝ)
      (f := fun n : ℕ => r ^ n) 1).mpr
      (hasSum_geometric_of_lt_one hy0 hy1)
    convert hgeo using 1
    simp only [Finset.sum_range_one, pow_zero]
    have hden : 1 - r ≠ 0 := by linarith [show r < 1 by simpa [r] using hy1]
    field_simp [hden]
    ring
  have hsumm_log :
      Summable (fun n : ℕ => y ^ (n + 1) / ((n : ℝ) + 1)) := by
    have habs : |y| < 1 := by simpa [abs_of_nonneg hy0] using hy1
    exact (Real.hasSum_pow_div_log_of_abs_lt_one habs).summable
  have hle :
      ∀ n : ℕ, y ^ (n + 1) / ((n : ℝ) + 1) ≤ y ^ (n + 1) := by
    intro n
    have hpow : 0 ≤ y ^ (n + 1) := pow_nonneg hy0 _
    have hden : 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    calc
      y ^ (n + 1) / ((n : ℝ) + 1)
          ≤ y ^ (n + 1) / 1 := by
            exact div_le_div_of_nonneg_left hpow zero_lt_one hden
      _ = y ^ (n + 1) := by ring
  rw [hlog]
  exact hasSum_le hle hsumm_log.hasSum hgeo_tail

private lemma summable_logEulerTerm {t : ℝ} (ht : 0 < t) :
    Summable (logEulerTerm t) := by
  let x : ℝ := Real.exp (-t)
  let C : ℝ := (1 - x)⁻¹
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    linarith
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact inv_nonneg.mpr (sub_nonneg.mpr hx1.le)
  have hgeo_nat : Summable (fun n : ℕ => C * x ^ (n + 1)) := by
    exact ((summable_geometric_of_lt_one hx0 hx1).comp_injective Nat.succ_injective).mul_left C
  have hgeo_pnat : Summable (fun k : ℕ+ => C * x ^ (k : ℕ)) := by
    exact (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => C * x ^ n)).mpr hgeo_nat
  refine Summable.of_nonneg_of_le ?_ ?_ hgeo_pnat
  · intro k
    dsimp [logEulerTerm]
    exact neg_log_one_sub_nonneg (Real.exp_pos _).le (exp_neg_mul_pnat_lt_one ht k)
  · intro k
    dsimp [logEulerTerm]
    have hk : 0 < (k : ℝ) := by exact_mod_cast k.2
    have hpow_eq : Real.exp (-(t * (k : ℝ))) = x ^ (k : ℕ) := by
      rw [exp_neg_mul_nat_eq_pow]
    have hy_le_x : Real.exp (-(t * (k : ℝ))) ≤ x := by
      rw [hpow_eq]
      simpa using (pow_le_pow_of_le_one hx0 hx1.le
        (by exact_mod_cast k.2) : x ^ (k : ℕ) ≤ x ^ 1)
    have hden_le :
        1 - x ≤ 1 - Real.exp (-(t * (k : ℝ))) := by
      exact sub_le_sub_left hy_le_x 1
    calc
      -Real.log (1 - Real.exp (-(t * (k : ℝ))))
          ≤ Real.exp (-(t * (k : ℝ))) / (1 - Real.exp (-(t * (k : ℝ)))) := by
            exact neg_log_one_sub_le_div (Real.exp_pos _).le (exp_neg_mul_pnat_lt_one ht k)
      _ ≤ Real.exp (-(t * (k : ℝ))) / (1 - x) := by
            exact div_le_div_of_nonneg_left (Real.exp_pos _).le (sub_pos.mpr hx1) hden_le
      _ = C * x ^ (k : ℕ) := by
            rw [hpow_eq]
            dsimp [C]
            ring

private lemma summable_logBridgeTerm_right {t : ℝ} (ht : 0 < t) (k : ℕ+) :
    Summable (fun j : ℕ+ => logBridgeTerm t k j) := by
  let y : ℝ := Real.exp (-(t * (k : ℝ)))
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hy1 : y < 1 := by
    dsimp [y]
    exact exp_neg_mul_pnat_lt_one ht k
  have habs : |y| < 1 := by simpa [abs_of_nonneg hy0] using hy1
  have hnat :
      Summable (fun n : ℕ => y ^ (n + 1) / ((n : ℝ) + 1)) :=
    (Real.hasSum_pow_div_log_of_abs_lt_one habs).summable
  have hpnat : Summable (fun j : ℕ+ => y ^ (j : ℕ) / (j : ℝ)) := by
    exact (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => y ^ n / (n : ℝ))).mpr (by
        simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hnat)
  exact hpnat.congr (fun j => by rfl)

private lemma tsum_logBridgeTerm_right {t : ℝ} (ht : 0 < t) (k : ℕ+) :
    (∑' j : ℕ+, logBridgeTerm t k j) = logEulerTerm t k := by
  let y : ℝ := Real.exp (-(t * (k : ℝ)))
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hy1 : y < 1 := by
    dsimp [y]
    exact exp_neg_mul_pnat_lt_one ht k
  have hlog := neg_log_one_sub_le_tsum hy0 hy1
  have hpnat :
      (∑' j : ℕ+, y ^ (j : ℕ) / (j : ℝ)) =
        ∑' n : ℕ, y ^ (n + 1) / ((n : ℝ) + 1) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => y ^ n / (n : ℝ))]
    congr
    funext n
    simp [Nat.cast_add, Nat.cast_one]
  calc
    (∑' j : ℕ+, logBridgeTerm t k j)
        = ∑' j : ℕ+, y ^ (j : ℕ) / (j : ℝ) := by rfl
    _ = ∑' n : ℕ, y ^ (n + 1) / ((n : ℝ) + 1) := hpnat
    _ = logEulerTerm t k := by
          dsimp [logEulerTerm, y]
          exact hlog.symm

private lemma tsum_pnat_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' k : ℕ+, r ^ (k : ℕ)) = r / (1 - r) := by
  have hgeo_tail :
      HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    have hgeo := (hasSum_nat_add_iff' (G := ℝ)
      (f := fun n : ℕ => r ^ n) 1).mpr
      (hasSum_geometric_of_lt_one hr0 hr1)
    convert hgeo using 1
    simp only [Finset.sum_range_one, pow_zero]
    have hden : 1 - r ≠ 0 := by linarith
    field_simp [hden]
    ring
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => r ^ n)]
  exact hgeo_tail.tsum_eq

private lemma pow_exp_swap {t : ℝ} (k j : ℕ+) :
    Real.exp (-(t * (k : ℝ))) ^ (j : ℕ) =
      Real.exp (-(t * (j : ℝ))) ^ (k : ℕ) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  ring

private lemma tsum_logBridgeTerm_left {t : ℝ} (ht : 0 < t) (j : ℕ+) :
    (∑' k : ℕ+, logBridgeTerm t k j) =
      1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)) := by
  let r : ℝ := Real.exp (-(t * (j : ℝ)))
  have hj : 0 < (j : ℝ) := by exact_mod_cast j.2
  have htj : 0 < t * (j : ℝ) := mul_pos ht hj
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  calc
    (∑' k : ℕ+, logBridgeTerm t k j)
        = ∑' k : ℕ+, r ^ (k : ℕ) / (j : ℝ) := by
            refine tsum_congr ?_
            intro k
            dsimp [logBridgeTerm, r]
            rw [pow_exp_swap]
    _ = (∑' k : ℕ+, r ^ (k : ℕ)) / (j : ℝ) := by
            simp_rw [div_eq_mul_inv]
            exact (tsum_mul_right
              (f := fun k : ℕ+ => r ^ (k : ℕ)) (a := (j : ℝ)⁻¹))
    _ = (r / (1 - r)) / (j : ℝ) := by
            rw [tsum_pnat_geometric hr0 hr1]
    _ = 1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)) := by
            dsimp [r]
            rw [Real.exp_neg]
            have hexp_ne : Real.exp (t * (j : ℝ)) ≠ 0 := Real.exp_ne_zero _
            have hsub_ne : Real.exp (t * (j : ℝ)) - 1 ≠ 0 := by
              exact sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr htj).ne'
            field_simp [hj.ne', hexp_ne, hsub_ne]

private lemma logBridgeTerm_nonneg {t : ℝ} (k j : ℕ+) :
    0 ≤ logBridgeTerm t k j := by
  dsimp [logBridgeTerm]
  exact div_nonneg (pow_nonneg (Real.exp_pos _).le _) (by positivity)

private lemma finite_euler_log_eq_sum {t : ℝ} (ht : 0 < t) (K : ℕ) :
    Real.log (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * (k : ℝ))))⁻¹)
      = ∑ k ∈ Finset.Icc 1 K, -Real.log (1 - Real.exp (-(t * (k : ℝ)))) := by
  have hne :
      ∀ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * (k : ℝ))))⁻¹ ≠ 0 := by
    intro k hk
    have hkpos_nat : 0 < k := (Finset.mem_Icc.mp hk).1
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkpos_nat
    have htk : 0 < t * (k : ℝ) := mul_pos ht hkpos
    have hexp_lt : Real.exp (-(t * (k : ℝ))) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    exact inv_ne_zero (sub_ne_zero.mpr hexp_lt.ne')
  rw [Real.log_prod hne]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Real.log_inv]

private lemma finite_euler_log_eq_range {t : ℝ} (ht : 0 < t) (K : ℕ) :
    Real.log (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * (k : ℝ))))⁻¹)
      = ∑ n ∈ Finset.range K, logEulerTerm t (Nat.succPNat n) := by
  calc
    Real.log (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * (k : ℝ))))⁻¹)
        = ∑ k ∈ Finset.Icc 1 K, -Real.log (1 - Real.exp (-(t * (k : ℝ)))) :=
            finite_euler_log_eq_sum ht K
    _ = ∑ n ∈ Finset.range K, logEulerTerm t (Nat.succPNat n) := by
          symm
          refine Finset.sum_bij (fun n _hn => n + 1) ?_ ?_ ?_ ?_
          · intro n hn
            rw [Finset.mem_Icc]
            exact ⟨Nat.succ_pos n, Finset.mem_range.mp hn⟩
          · intro a ha b hb hab
            exact Nat.succ.inj hab
          · intro b hb
            rw [Finset.mem_Icc] at hb
            refine ⟨b - 1, ?_, ?_⟩
            · rw [Finset.mem_range]
              omega
            · exact Nat.sub_add_cancel hb.1
          · intro n hn
            dsimp [logEulerTerm]

theorem log_partLaplace_eq {t : ℝ} (ht : 0 < t) :
    Real.log (PartLaplace t) =
      ∑' k : ℕ+, -Real.log (1 - Real.exp (-(t * k))) := by
  have hpos : 0 < PartLaplace t := PartLaplace_pos ht
  have hsumm : Summable (logEulerTerm t) := summable_logEulerTerm ht
  have hsucc_summ :
      Summable (fun n : ℕ => logEulerTerm t (Nat.succPNat n)) := by
    exact (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => -Real.log (1 - Real.exp (-(t * (n : ℝ)))))).mp
      (by simpa [logEulerTerm] using hsumm)
  have hpartial :
      Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, logEulerTerm t (Nat.succPNat n))
        atTop (𝓝 (∑' k : ℕ+, logEulerTerm t k)) := by
    have hnat :=
      (hsucc_summ.hasSum.tendsto_sum_nat :
        Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, logEulerTerm t (Nat.succPNat n))
          atTop (𝓝 (∑' n : ℕ, logEulerTerm t (Nat.succPNat n))))
    have htsum :
        (∑' n : ℕ, logEulerTerm t (Nat.succPNat n)) =
          ∑' k : ℕ+, logEulerTerm t k := by
      simpa [Equiv.pnatEquivNat] using
        (Equiv.pnatEquivNat.symm.tsum_eq (fun k : ℕ+ => logEulerTerm t k))
    simpa [htsum] using hnat
  have hlog_tendsto :
      Tendsto
        (fun K : ℕ =>
          Real.log (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * (k : ℝ))))⁻¹))
        atTop
        (𝓝 (Real.log (PartLaplace t))) := by
    exact (Real.continuousAt_log hpos.ne').tendsto.comp (partLaplace_eq_finprod_tendsto ht)
  have hlog_partial :
      Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, logEulerTerm t (Nat.succPNat n))
        atTop (𝓝 (Real.log (PartLaplace t))) := by
    exact hlog_tendsto.congr' (Eventually.of_forall fun K => finite_euler_log_eq_range ht K)
  have heq : Real.log (PartLaplace t) = ∑' k : ℕ+, logEulerTerm t k :=
    tendsto_nhds_unique hlog_partial hpartial
  simpa [logEulerTerm] using heq

theorem log_series_regroup {t : ℝ} (ht : 0 < t) :
    (∑' k : ℕ+, -Real.log (1 - Real.exp (-(t*k)))) =
      ∑' j : ℕ+, 1 / ((j:ℝ) * (Real.exp (t*j) - 1)) := by
  have hsumm_log : Summable (logEulerTerm t) := summable_logEulerTerm ht
  have hprod_summ :
      Summable (fun p : ℕ+ × ℕ+ => logBridgeTerm t p.1 p.2) := by
    have hrows :
        ∀ k : ℕ+, Summable (fun j : ℕ+ => logBridgeTerm t k j) :=
      summable_logBridgeTerm_right ht
    have hrow_sums :
        Summable (fun k : ℕ+ => ∑' j : ℕ+, logBridgeTerm t k j) := by
      exact hsumm_log.congr (fun k => (tsum_logBridgeTerm_right ht k).symm)
    exact (summable_prod_of_nonneg
      (f := fun p : ℕ+ × ℕ+ => logBridgeTerm t p.1 p.2)
      (fun p => logBridgeTerm_nonneg p.1 p.2)).mpr ⟨hrows, hrow_sums⟩
  calc
    (∑' k : ℕ+, -Real.log (1 - Real.exp (-(t*k))))
        = ∑' k : ℕ+, logEulerTerm t k := by
            simp [logEulerTerm]
    _ = ∑' k : ℕ+, ∑' j : ℕ+, logBridgeTerm t k j := by
            refine tsum_congr ?_
            intro k
            exact (tsum_logBridgeTerm_right ht k).symm
    _ = ∑' j : ℕ+, ∑' k : ℕ+, logBridgeTerm t k j := by
            exact (Summable.tsum_comm hprod_summ).symm
    _ = ∑' j : ℕ+, 1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)) := by
            refine tsum_congr ?_
            intro j
            exact tsum_logBridgeTerm_left ht j

theorem partition_laplace_log_asymptotic :
    Tendsto (fun t : ℝ => t * Real.log (PartLaplace t)) (𝓝[>] 0) (𝓝 A) := by
  refine partition_laplace_series_asymptotic.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [log_partLaplace_eq ht, log_series_regroup ht]

end AnalyticCombinatorics.Ch8.Partitions
