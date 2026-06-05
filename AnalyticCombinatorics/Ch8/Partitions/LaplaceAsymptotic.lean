import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.UpperBound

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology

noncomputable def PartLaplace (t : ℝ) : ℝ :=
  ∑' n : ℕ, part n * Real.exp (-(t * n))

lemma two_sqrt_A_mul_le_linear {ε x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) :
    2 * Real.sqrt (A * x) ≤ ε * x + A / ε := by
  have hleft : 0 ≤ 2 * Real.sqrt (A * x) := by positivity
  have hright : 0 ≤ ε * x + A / ε :=
    add_nonneg (mul_nonneg hε.le hx) (div_nonneg A_nonneg hε.le)
  have hAx : 0 ≤ A * x := mul_nonneg A_nonneg hx
  have hεne : ε ≠ 0 := hε.ne'
  have hsquare : 0 ≤ (ε * x - A / ε) ^ 2 := sq_nonneg _
  refine (sq_le_sq₀ hleft hright).mp ?_
  rw [mul_pow, Real.sq_sqrt hAx]
  rw [← sub_nonneg]
  have hdiff :
      (ε * x + A / ε) ^ 2 - 2 ^ 2 * (A * x) = (ε * x - A / ε) ^ 2 := by
    field_simp [hεne]
    ring_nf
  rwa [hdiff]

theorem partLaplace_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n => part n * Real.exp (-(t * n))) := by
  have ht2 : 0 < t / 2 := by positivity
  have hgeom : Summable (fun n : ℕ => Real.exp (-(t / 2) * (n : ℝ))) := by
    have h := Real.summable_exp_nat_mul_iff.mpr (by linarith : -(t / 2) < 0)
    convert h using 1
    ext n
    ring_nf
  refine (hgeom.mul_left (Real.exp (2 * A / t))).of_norm_bounded ?_
  intro n
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hpart : part n ≤ Real.exp (2 * Real.sqrt (A * n)) := by
    have h := partition_upper_exp n
    convert h using 1
    exact congrArg Real.exp (two_sqrt_A_eq n)
  have hlin : 2 * Real.sqrt (A * (n : ℝ)) ≤ (t / 2) * n + A / (t / 2) :=
    two_sqrt_A_mul_le_linear ht2 hn
  calc
    ‖part n * Real.exp (-(t * n))‖
        = part n * Real.exp (-(t * n)) := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact mul_nonneg (part_pos n).le (Real.exp_pos _).le
    _ ≤ Real.exp (2 * Real.sqrt (A * n)) * Real.exp (-(t * n)) := by
          exact mul_le_mul_of_nonneg_right hpart (Real.exp_pos _).le
    _ = Real.exp (2 * Real.sqrt (A * n) - t * n) := by
          rw [← Real.exp_add]
          ring_nf
    _ ≤ Real.exp (2 * A / t - (t / 2) * n) := by
          refine Real.exp_monotone ?_
          have hAdiv : A / (t / 2) = 2 * A / t := by field_simp [ht.ne']
          linarith
    _ = Real.exp (2 * A / t) * Real.exp (-(t / 2) * n) := by
          rw [← Real.exp_add]
          ring_nf

lemma summable_one_div_pnat_sq :
    Summable (fun j : ℕ+ => (1 : ℝ) / (j : ℝ) ^ 2) := by
  exact
    (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)).mpr
      (by
        simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
          using hasSum_one_div_nat_succ_sq.summable)

lemma tsum_one_div_pnat_sq :
    (∑' j : ℕ+, (1 : ℝ) / (j : ℝ) ^ 2) = A := by
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)]
  simpa [A, pow_two, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
    using tsum_one_div_nat_succ_sq

lemma exp_sub_one_div_self_tendsto_one :
    Tendsto (fun u : ℝ => (Real.exp u - 1) / u) (𝓝[>] 0) (𝓝 1) := by
  have h := (Real.hasDerivAt_exp 0).sub_const 1
  have hslope := h.tendsto_slope_zero_right
  simpa [slope, Real.exp_zero, div_eq_mul_inv, mul_comm] using hslope

lemma exp_ratio_tendsto_one (j : ℕ+) :
    Tendsto
      (fun t : ℝ => (t * (j : ℝ)) / (Real.exp (t * (j : ℝ)) - 1))
      (𝓝[>] 0) (𝓝 1) := by
  have hj : 0 < (j : ℝ) := by exact_mod_cast j.2
  have hmul_nhds :
      Tendsto (fun t : ℝ => t * (j : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hc : Tendsto (fun _t : ℝ => (j : ℝ)) (𝓝[>] 0) (𝓝 (j : ℝ)) :=
      tendsto_const_nhds
    simpa using hid.mul hc
  have hmul_pos : ∀ᶠ t : ℝ in 𝓝[>] 0, t * (j : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos ht hj
  have hmul :
      Tendsto (fun t : ℝ => t * (j : ℝ)) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hmul_nhds, hmul_pos⟩
  have hbase := exp_sub_one_div_self_tendsto_one.comp hmul
  have hinv :
      Tendsto
        (fun t : ℝ => ((Real.exp (t * (j : ℝ)) - 1) / (t * (j : ℝ)))⁻¹)
        (𝓝[>] 0) (𝓝 1) := by
    simpa using hbase.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  refine hinv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have htj : 0 < t * (j : ℝ) := mul_pos ht hj
  have hne : Real.exp (t * (j : ℝ)) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr htj).ne'
  field_simp [hne, htpos.ne', hj.ne']

lemma exp_partition_term_bound {t : ℝ} (ht : 0 < t) (j : ℕ+) :
    0 ≤ t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))
    ∧
    t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))
      ≤ 1 / (j : ℝ) ^ 2 := by
  have hj : 0 < (j : ℝ) := by exact_mod_cast j.2
  have htj : 0 < t * (j : ℝ) := mul_pos ht hj
  have hexp_pos : 0 < Real.exp (t * (j : ℝ)) - 1 := by
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr htj)
  have hden_pos : 0 < (j : ℝ) * (Real.exp (t * (j : ℝ)) - 1) :=
    mul_pos hj hexp_pos
  constructor
  · positivity
  · have hlinear : t * (j : ℝ) ≤ Real.exp (t * (j : ℝ)) - 1 := by
      linarith [Real.add_one_le_exp (t * (j : ℝ))]
    have hden_le :
        (j : ℝ) * (t * (j : ℝ)) ≤ (j : ℝ) * (Real.exp (t * (j : ℝ)) - 1) :=
      mul_le_mul_of_nonneg_left hlinear hj.le
    have hsmall_pos : 0 < (j : ℝ) * (t * (j : ℝ)) := mul_pos hj htj
    calc
      t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))
          ≤ t / ((j : ℝ) * (t * (j : ℝ))) := by
            exact div_le_div_of_nonneg_left ht.le hsmall_pos hden_le
      _ = 1 / (j : ℝ) ^ 2 := by
            field_simp [ht.ne', hj.ne']

lemma exp_partition_term_tendsto (j : ℕ+) :
    Tendsto
      (fun t : ℝ =>
        t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)))
      (𝓝[>] 0)
      (𝓝 (1 / (j : ℝ) ^ 2)) := by
  have hj : 0 < (j : ℝ) := by exact_mod_cast j.2
  have hratio := exp_ratio_tendsto_one j
  have hscaled :
      Tendsto
        (fun t : ℝ =>
          ((j : ℝ) ^ 2)⁻¹ *
            ((t * (j : ℝ)) / (Real.exp (t * (j : ℝ)) - 1)))
        (𝓝[>] 0)
        (𝓝 (((j : ℝ) ^ 2)⁻¹)) := by
    simpa using hratio.const_mul (((j : ℝ) ^ 2)⁻¹)
  have heq :
      (fun t : ℝ =>
        ((j : ℝ) ^ 2)⁻¹ *
          ((t * (j : ℝ)) / (Real.exp (t * (j : ℝ)) - 1)))
        =ᶠ[𝓝[>] 0]
      (fun t : ℝ =>
        t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have htj : 0 < t * (j : ℝ) := mul_pos ht hj
    have hne : Real.exp (t * (j : ℝ)) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr htj).ne'
    field_simp [hne, htpos.ne', hj.ne']
  simpa [one_div] using hscaled.congr' heq

theorem partition_laplace_series_asymptotic :
    Tendsto
      (fun t : ℝ =>
        t * (∑' j : ℕ+, 1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))))
      (𝓝[>] 0)
      (𝓝 A) := by
  have hdom :
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        ∀ j : ℕ+,
          ‖t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))‖
            ≤ (1 : ℝ) / (j : ℝ) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht j
    have hb := exp_partition_term_bound ht j
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  have htend :=
    tendsto_tsum_of_dominated_convergence
      (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun (t : ℝ) (j : ℕ+) =>
        t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)))
      (g := fun j : ℕ+ => (1 : ℝ) / (j : ℝ) ^ 2)
      summable_one_div_pnat_sq
      exp_partition_term_tendsto
      hdom
  have hrewrite :
      (fun t : ℝ =>
        t * (∑' j : ℕ+, 1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))))
        = fun t : ℝ =>
          ∑' j : ℕ+, t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)) := by
    funext t
    calc
      t * (∑' j : ℕ+, 1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)))
          = ∑' j : ℕ+,
              t * (1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1))) := by
            exact (tsum_mul_left
              (a := t)
              (f := fun j : ℕ+ =>
                1 / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)))).symm
      _ = ∑' j : ℕ+, t / ((j : ℝ) * (Real.exp (t * (j : ℝ)) - 1)) := by
            congr
            funext j
            ring_nf
  rw [hrewrite]
  have hlimit : (∑' j : ℕ+, ((j : ℝ) ^ 2)⁻¹) = A := by
    simpa [one_div] using tsum_one_div_pnat_sq
  simpa [hlimit] using htend

end AnalyticCombinatorics.Ch8.Partitions
