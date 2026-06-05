import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.UpperBound
import AnalyticCombinatorics.Ch8.Partitions.LaplaceAsymptotic
import AnalyticCombinatorics.Ch8.Partitions.EulerProduct
import AnalyticCombinatorics.Ch8.Partitions.LaplaceLimit
import AnalyticCombinatorics.Ch8.Partitions.Tauberian
import AnalyticCombinatorics.Ch8.Partitions.TauberianFull
import AnalyticCombinatorics.Ch8.Partitions.TauberianAssembly

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology Asymptotics

-- The final transfer combines real logarithm/square-root limits with field
-- simplification; this keeps those terminal proofs within the local file.
set_option maxHeartbeats 400000

noncomputable def PartCum (N : ℕ) : ℝ :=
  Tauberian.Cum part N

theorem part_zero : part 0 = 1 := by
  simp [part]

def addOnesPartition {m n : ℕ} (hmn : m ≤ n) (p : Nat.Partition m) :
    Nat.Partition n where
  parts := p.parts + Multiset.replicate (n - m) 1
  parts_pos := by
    intro i hi
    rw [Multiset.mem_add] at hi
    rcases hi with hi | hi
    · exact p.parts_pos hi
    · have h : i = 1 := Multiset.eq_of_mem_replicate hi
      omega
  parts_sum := by
    rw [Multiset.sum_add, Multiset.sum_replicate, p.parts_sum]
    simp
    omega

lemma addOnesPartition_injective {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (addOnesPartition (m := m) (n := n) hmn) := by
  intro p q hpq
  apply Nat.Partition.ext
  have hparts :
      p.parts + Multiset.replicate (n - m) 1 =
        q.parts + Multiset.replicate (n - m) 1 := by
    exact congrArg Nat.Partition.parts hpq
  exact (add_left_injective (Multiset.replicate (n - m) 1)) hparts

theorem part_mono : Monotone part := by
  intro m n hmn
  dsimp [part]
  exact_mod_cast
    Fintype.card_le_of_injective
      (addOnesPartition (m := m) (n := n) hmn)
      (addOnesPartition_injective (m := m) (n := n) hmn)

theorem part_le_PartCum (N : ℕ) :
    part N ≤ PartCum N := by
  simpa [PartCum] using
    (Tauberian.term_le_Cum (a := part) (fun n => (part_pos n).le) N)

theorem PartCum_le_mul_part (N : ℕ) :
    PartCum N ≤ (N + 1 : ℝ) * part N := by
  unfold PartCum Tauberian.Cum
  calc
    (∑ n ∈ Finset.range (N + 1), part n)
        ≤ ∑ n ∈ Finset.range (N + 1), part N := by
          exact Finset.sum_le_sum fun n hn =>
            part_mono (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
    _ = (N + 1 : ℝ) * part N := by
          simp [Finset.sum_const, nsmul_eq_mul]

theorem partition_cum_log_asymptotic :
    Tendsto
      (fun N : ℕ => Real.log (PartCum N) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 (2 * Real.sqrt A)) := by
  have h :=
    Tauberian.log_tauberian_cumulative_sqrt
      (a := part)
      (ha := fun n => (part_pos n).le)
      (ha0 := by rw [part_zero])
      (hK := A_pos)
      (hsum := fun t ht => partLaplace_summable ht)
      (hF := by simpa [PartLaplace] using partition_laplace_log_asymptotic)
  simpa [PartCum] using h

lemma log_nat_succ_div_sqrt_tendsto_zero :
    Tendsto
      (fun N : ℕ => Real.log ((N : ℝ) + 1) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 0) := by
  have hlog_real :
      Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hsucc_atTop : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hlog_succ :
      Tendsto
        (fun N : ℕ => Real.log ((N : ℝ) + 1) / Real.sqrt ((N : ℝ) + 1))
        atTop
        (𝓝 0) :=
    hlog_real.comp hsucc_atTop
  have hratio :
      Tendsto
        (fun N : ℕ => Real.sqrt (((N : ℝ) + 1) / (N : ℝ)))
        atTop
        (𝓝 1) := by
    have hdiv :
        Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (N : ℝ)) atTop (𝓝 1) := by
      simpa [mul_comm, add_comm] using
        (tendsto_add_mul_div_add_mul_atTop_nhds
          (𝕜 := ℝ) (a := 1) (b := 0) (c := 1) (d := 1) one_ne_zero)
    simpa [Real.sqrt_one] using hdiv.sqrt
  have hprod := hlog_succ.mul hratio
  simpa using
    (hprod.congr' <| by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
      have hsqrtN_ne : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
      have hsqrt_succ_ne : Real.sqrt ((N : ℝ) + 1) ≠ 0 := by positivity
      have hsqrt_div :
          Real.sqrt (((N : ℝ) + 1) / (N : ℝ)) =
            Real.sqrt ((N : ℝ) + 1) / Real.sqrt (N : ℝ) := by
        rw [Real.sqrt_div (by positivity : 0 ≤ (N : ℝ) + 1)]
      rw [hsqrt_div]
      field_simp [hsqrtN_ne, hsqrt_succ_ne])

lemma PartCum_log_part_log_gap_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        (Real.log (PartCum N) - Real.log (part N)) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    log_nat_succ_div_sqrt_tendsto_zero ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
    have hpart_pos : 0 < part N := part_pos N
    have hcum_pos : 0 < PartCum N := hpart_pos.trans_le (part_le_PartCum N)
    have hlog_le : Real.log (part N) ≤ Real.log (PartCum N) :=
      Real.log_le_log hpart_pos (part_le_PartCum N)
    rw [div_nonneg_iff]
    exact Or.inl ⟨sub_nonneg.mpr hlog_le, hsqrtN_pos.le⟩
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
    have hpart_pos : 0 < part N := part_pos N
    have hcum_pos : 0 < PartCum N := hpart_pos.trans_le (part_le_PartCum N)
    have hlog_upper :
        Real.log (PartCum N) ≤ Real.log ((N + 1 : ℝ) * part N) :=
      Real.log_le_log hcum_pos (PartCum_le_mul_part N)
    have hlog_mul :
        Real.log ((N + 1 : ℝ) * part N) =
          Real.log ((N : ℝ) + 1) + Real.log (part N) := by
      rw [Real.log_mul (by positivity : ((N : ℝ) + 1) ≠ 0) hpart_pos.ne']
    have hnum :
        Real.log (PartCum N) - Real.log (part N) ≤ Real.log ((N : ℝ) + 1) := by
      calc
        Real.log (PartCum N) - Real.log (part N)
            ≤ Real.log ((N + 1 : ℝ) * part N) - Real.log (part N) := by
              exact sub_le_sub_right hlog_upper _
        _ = Real.log ((N : ℝ) + 1) := by
              rw [hlog_mul]
              ring
    exact div_le_div_of_nonneg_right hnum hsqrtN_pos.le

lemma PartCum_part_log_div_gap_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        Real.log (PartCum N) / Real.sqrt (N : ℝ) -
          Real.log (part N) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 0) := by
  refine PartCum_log_part_log_gap_tendsto_zero.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hsqrtN_ne : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
  field_simp [hsqrtN_ne]

theorem two_sqrt_A_const_eq :
    2 * Real.sqrt A = Real.pi * Real.sqrt (2 / 3) := by
  simpa using two_sqrt_A_eq 1

theorem partition_log_asymptotic :
    Tendsto
      (fun n : ℕ => Real.log (part n) / Real.sqrt n)
      atTop
      (𝓝 (Real.pi * Real.sqrt (2 / 3))) := by
  have hpart_to_cum :=
    partition_cum_log_asymptotic.sub PartCum_part_log_div_gap_tendsto_zero
  have hpart :
      Tendsto
        (fun n : ℕ => Real.log (part n) / Real.sqrt (n : ℝ))
        atTop
        (𝓝 (2 * Real.sqrt A)) := by
    simpa using
      (hpart_to_cum.congr' <| by
        filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
        ring)
  simpa [two_sqrt_A_const_eq] using hpart

lemma partition_log_target_eq_const_mul_sqrt {n : ℕ} :
    Real.pi * Real.sqrt (2 * (n : ℝ) / 3) =
      (Real.pi * Real.sqrt (2 / 3)) * Real.sqrt (n : ℝ) := by
  have harg : 2 * (n : ℝ) / 3 = (2 / 3 : ℝ) * (n : ℝ) := by ring
  rw [harg, Real.sqrt_mul (by positivity : 0 ≤ (2 / 3 : ℝ))]
  ring

theorem partition_log_isEquivalent :
    (fun n : ℕ => Real.log (part n)) ~[atTop]
      (fun n : ℕ => Real.pi * Real.sqrt (2 * (n : ℝ) / 3)) := by
  have htarget_ne :
      ∀ᶠ n : ℕ in atTop, Real.pi * Real.sqrt (2 * (n : ℝ) / 3) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    positivity
  refine (Asymptotics.isEquivalent_iff_tendsto_one htarget_ne).mpr ?_
  have hconst_pos : 0 < Real.pi * Real.sqrt (2 / 3) := by positivity
  have hratio :
      Tendsto
        (fun n : ℕ =>
          (Real.log (part n) / Real.sqrt (n : ℝ)) /
            (Real.pi * Real.sqrt (2 / 3)))
        atTop
        (𝓝 1) := by
    have h :=
      partition_log_asymptotic.div_const (Real.pi * Real.sqrt (2 / 3))
    simpa [hconst_pos.ne'] using h
  refine hratio.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnpos).ne'
  have hconst_ne : Real.pi * Real.sqrt (2 / 3) ≠ 0 := hconst_pos.ne'
  simp only [Pi.div_apply]
  rw [partition_log_target_eq_const_mul_sqrt]
  field_simp [hsqrt_ne, hconst_ne]

end AnalyticCombinatorics.Ch8.Partitions
