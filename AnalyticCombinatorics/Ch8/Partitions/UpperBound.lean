import Mathlib

namespace AnalyticCombinatorics.Ch8.Partitions

open scoped BigOperators

noncomputable def part (n : ℕ) : ℝ :=
  (Fintype.card (Nat.Partition n) : ℝ)

noncomputable def A : ℝ :=
  Real.pi ^ 2 / 6

lemma part_pos (n : ℕ) : 0 < part n := by
  dsimp [part]
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨Nat.Partition.indiscrete n⟩

lemma A_pos : 0 < A := by
  dsimp [A]
  positivity

lemma A_nonneg : 0 ≤ A := A_pos.le

lemma log_one_div_le_self {u : ℝ} (hu : 0 < u) :
    Real.log (1 + 1 / u) ≤ 1 / u := by
  have hpos : 0 < 1 + 1 / u := by positivity
  have := Real.log_le_sub_one_of_pos hpos
  linarith

lemma neg_log_one_sub_le_tsum {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    -Real.log (1 - y) = ∑' j : ℕ, y ^ (j + 1) / ((j : ℝ) + 1) := by
  have habs : |y| < 1 := by simpa [abs_of_nonneg hy0] using hy1
  exact (Real.hasSum_pow_div_log_of_abs_lt_one habs).tsum_eq.symm

lemma hasSum_one_div_nat_succ_sq :
    HasSum (fun j : ℕ => (1 : ℝ) / (((j : ℝ) + 1) ^ 2)) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' (G := ℝ)
    (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hasSum_zeta_two
  simpa [pow_two, add_comm, add_left_comm, add_assoc] using h

lemma tsum_one_div_nat_succ_sq :
    (∑' j : ℕ, (1 : ℝ) / (((j : ℝ) + 1) ^ 2)) = A := by
  simpa [A] using hasSum_one_div_nat_succ_sq.tsum_eq

lemma geom_ratio_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {m : ℕ} (hm : 0 < m) :
    x ^ m / (1 - x ^ m) ≤ x / ((m : ℝ) * (1 - x)) := by
  have hx0' : 0 ≤ x := hx0.le
  have hx1' : x ≤ 1 := hx1.le
  have hpow_lt_one : x ^ m < 1 := pow_lt_one₀ hx0' hx1 hm.ne'
  have hden_pos : 0 < 1 - x ^ m := sub_pos.mpr hpow_lt_one
  have hsmall_pos : 0 < (m : ℝ) * x ^ (m - 1) * (1 - x) := by
    have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    have hxpow : 0 < x ^ (m - 1) := pow_pos hx0 _
    have hxden : 0 < 1 - x := sub_pos.mpr hx1
    positivity
  have hsum_lower :
      (m : ℝ) * x ^ (m - 1) ≤ ∑ i ∈ Finset.range m, x ^ i := by
    calc
      (m : ℝ) * x ^ (m - 1) = ∑ i ∈ Finset.range m, x ^ (m - 1) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range m, x ^ i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi_le : i ≤ m - 1 := Nat.le_pred_of_lt (Finset.mem_range.mp hi)
        exact pow_le_pow_of_le_one hx0' hx1' hi_le
  have hden_lower : (m : ℝ) * x ^ (m - 1) * (1 - x) ≤ 1 - x ^ m := by
    have hmul := mul_le_mul_of_nonneg_right hsum_lower (sub_nonneg.mpr hx1')
    simpa [geom_sum_mul_of_le_one hx1' m, mul_assoc] using hmul
  calc
    x ^ m / (1 - x ^ m) ≤ x ^ m / ((m : ℝ) * x ^ (m - 1) * (1 - x)) := by
      exact div_le_div_of_nonneg_left (pow_nonneg hx0' m) hsmall_pos hden_lower
    _ = x / ((m : ℝ) * (1 - x)) := by
      rw [show x ^ m = x ^ (m - 1) * x by
        rw [← pow_succ, Nat.sub_add_cancel hm]]
      field_simp [hx0.ne', (Nat.cast_pos.mpr hm).ne', sub_ne_zero.mpr hx1.ne]

lemma finite_partition_log_product_bound {n : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (∑ i ∈ Finset.range n, -Real.log (1 - x ^ (i + 1))) ≤ A * x / (1 - x) := by
  classical
  let f : ℕ → ℕ → ℝ := fun i j =>
    (x ^ (i + 1)) ^ (j + 1) / ((j : ℝ) + 1)
  have hx0' : 0 ≤ x := hx0.le
  have hx1' : x ≤ 1 := hx1.le
  have hf_sum : ∀ i ∈ Finset.range n, Summable (f i) := by
    intro i hi
    have hpow_nonneg : 0 ≤ x ^ (i + 1) := pow_nonneg hx0' _
    have hpow_lt : x ^ (i + 1) < 1 := pow_lt_one₀ hx0' hx1 (Nat.succ_ne_zero i)
    exact (Real.hasSum_pow_div_log_of_abs_lt_one
      (by simpa [abs_of_nonneg hpow_nonneg] using hpow_lt)).summable
  have hlog_eq :
      (∑ i ∈ Finset.range n, -Real.log (1 - x ^ (i + 1)))
        = ∑' j : ℕ, ∑ i ∈ Finset.range n, f i j := by
    rw [Summable.tsum_finsetSum hf_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hpow_nonneg : 0 ≤ x ^ (i + 1) := pow_nonneg hx0' _
    have hpow_lt : x ^ (i + 1) < 1 := pow_lt_one₀ hx0' hx1 (Nat.succ_ne_zero i)
    exact neg_log_one_sub_le_tsum hpow_nonneg hpow_lt
  have hmajor_hasSum :
      HasSum (fun j : ℕ => x / (((j : ℝ) + 1) ^ 2 * (1 - x)))
        (A * x / (1 - x)) := by
    have h := hasSum_one_div_nat_succ_sq.mul_left (x / (1 - x))
    convert h using 1
    · ext j
      field_simp [pow_two, sub_ne_zero.mpr hx1.ne]
    · simp [A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hlog_eq]
  have hbound :
      ∀ j : ℕ, (∑ i ∈ Finset.range n, f i j)
        ≤ x / (((j : ℝ) + 1) ^ 2 * (1 - x)) := by
    intro j
    have hm_pos : 0 < j + 1 := Nat.succ_pos j
    have hpowm_lt : x ^ (j + 1) < 1 := pow_lt_one₀ hx0' hx1 hm_pos.ne'
    have hgeom :
        HasSum (fun i : ℕ => (x ^ (j + 1)) ^ (i + 1) / ((j : ℝ) + 1))
          (x ^ (j + 1) / (1 - x ^ (j + 1)) / ((j : ℝ) + 1)) := by
      have hbase :
          HasSum (fun i : ℕ => (x ^ (j + 1)) ^ (i + 1))
            (x ^ (j + 1) / (1 - x ^ (j + 1))) := by
        let r := x ^ (j + 1)
        have hr_nonneg : 0 ≤ r := pow_nonneg hx0' _
        have hr_lt : r < 1 := by simpa [r] using hpowm_lt
        have hgeo := (hasSum_nat_add_iff' (G := ℝ)
          (f := fun i : ℕ => r ^ i) 1).mpr
          (hasSum_geometric_of_lt_one hr_nonneg hr_lt)
        have hgeo' : HasSum (fun i : ℕ => r ^ (i + 1)) (r / (1 - r)) := by
          convert hgeo using 1
          simp only [Finset.sum_range_one, pow_zero]
          have hden : 1 - r ≠ 0 := by linarith
          field_simp [hden]
          ring
        simpa [r] using hgeo'
      simpa [div_eq_mul_inv, mul_assoc] using hbase.mul_right (((j : ℝ) + 1)⁻¹)
    have hgeom_f :
        HasSum (fun i : ℕ => f i j)
          (x ^ (j + 1) / (1 - x ^ (j + 1)) / ((j : ℝ) + 1)) := by
      convert hgeom using 1
      funext i
      dsimp [f]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    calc
      (∑ i ∈ Finset.range n, f i j)
          ≤ x ^ (j + 1) / (1 - x ^ (j + 1)) / ((j : ℝ) + 1) := by
        refine sum_le_hasSum (Finset.range n) ?_ hgeom_f
        intro i hi
        dsimp [f]
        positivity
      _ ≤ x / (((j : ℝ) + 1) ^ 2 * (1 - x)) := by
        have hratio := geom_ratio_le hx0 hx1 hm_pos
        have hratio' :
            x ^ (j + 1) / (1 - x ^ (j + 1))
              ≤ x / (((j : ℝ) + 1) * (1 - x)) := by
          simpa using hratio
        have hden_nonneg : 0 ≤ ((j : ℝ) + 1)⁻¹ := by positivity
        calc
          x ^ (j + 1) / (1 - x ^ (j + 1)) / ((j : ℝ) + 1)
              = (x ^ (j + 1) / (1 - x ^ (j + 1))) * (((j : ℝ) + 1)⁻¹) := by
                ring
          _ ≤ (x / (((j : ℝ) + 1) * (1 - x))) * (((j : ℝ) + 1)⁻¹) := by
                exact mul_le_mul_of_nonneg_right hratio' hden_nonneg
          _ = x / (((j : ℝ) + 1) ^ 2 * (1 - x)) := by
                field_simp [pow_two]
  have hsumm_left : Summable (fun j : ℕ => ∑ i ∈ Finset.range n, f i j) :=
    Summable.of_nonneg_of_le
      (fun j => by
        refine Finset.sum_nonneg ?_
        intro i hi
        dsimp [f]
        positivity)
      hbound
      hmajor_hasSum.summable
  exact hasSum_le hbound hsumm_left.hasSum hmajor_hasSum

lemma partition_range_count_sum (n : ℕ) (p : Nat.Partition n) :
    (∑ i ∈ Finset.range n, p.parts.count (i + 1) * (i + 1)) = n := by
  have hIcc :
      (∑ m ∈ Finset.Icc 1 n, p.parts.count m * m) = n := by
    have hmem := Nat.Partition.toFinsuppAntidiag_mem_finsuppAntidiag (p := p)
    have hsum := (Finset.mem_finsuppAntidiag.mp hmem).1
    simpa [Nat.Partition.toFinsuppAntidiag, mul_comm] using hsum
  calc
    (∑ i ∈ Finset.range n, p.parts.count (i + 1) * (i + 1))
        = ∑ m ∈ Finset.Icc 1 n, p.parts.count m * m := by
      refine Finset.sum_bij (fun i hi => i + 1) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_Icc]
        constructor
        · exact Nat.succ_pos i
        · exact Finset.mem_range.mp hi
      · intro a ha b hb h
        exact Nat.succ.inj h
      · intro b hb
        rw [Finset.mem_Icc] at hb
        refine ⟨b - 1, ?_, ?_⟩
        · rw [Finset.mem_range]
          omega
        · exact Nat.sub_add_cancel hb.1
      · intro i hi
        rfl
    _ = n := hIcc

lemma partition_count_le_n {n i : ℕ} (p : Nat.Partition n) (hi : i ∈ Finset.range n) :
    p.parts.count (i + 1) ≤ n := by
  have hterm :
      p.parts.count (i + 1) * (i + 1) ≤ n := by
    have hsingle :
        p.parts.count (i + 1) * (i + 1)
          ≤ ∑ k ∈ Finset.range n, p.parts.count (k + 1) * (k + 1) := by
      exact Finset.single_le_sum
        (s := Finset.range n)
        (f := fun k => p.parts.count (k + 1) * (k + 1))
        (fun k hk => Nat.zero_le _) hi
    simpa [partition_range_count_sum n p] using hsingle
  have hcount_le :
      p.parts.count (i + 1) ≤ p.parts.count (i + 1) * (i + 1) := by
    nth_rewrite 1 [← Nat.mul_one (p.parts.count (i + 1))]
    exact Nat.mul_le_mul_left _ (Nat.succ_pos i)
  exact hcount_le.trans hterm

lemma partition_product_term_eq {n : ℕ} (z : ℝ) (p : Nat.Partition n) :
    (∏ a ∈ (Finset.range n).attach,
        z ^ ((a.1 + 1) * p.parts.count (a.1 + 1))) = z ^ n := by
  calc
    (∏ a ∈ (Finset.range n).attach,
        z ^ ((a.1 + 1) * p.parts.count (a.1 + 1)))
        = ∏ i ∈ Finset.range n, z ^ ((i + 1) * p.parts.count (i + 1)) := by
      simpa using
        (Finset.prod_attach (Finset.range n)
          (fun i => z ^ ((i + 1) * p.parts.count (i + 1))))
    _ = z ^ (∑ i ∈ Finset.range n, (i + 1) * p.parts.count (i + 1)) := by
      exact Finset.prod_pow_eq_pow_sum (Finset.range n)
        (fun i => (i + 1) * p.parts.count (i + 1)) z
    _ = z ^ n := by
      congr 1
      simpa [Nat.mul_comm] using partition_range_count_sum n p

lemma partition_multiplicity_injective (n : ℕ) :
    Function.Injective
      (fun p : Nat.Partition n =>
        fun i : ℕ => fun _hi : i ∈ Finset.range n => p.parts.count (i + 1)) := by
  intro p q h
  apply Nat.Partition.ext
  apply Multiset.ext.mpr
  intro m
  by_cases hm0 : m = 0
  · subst hm0
    have hp0 : 0 ∉ p.parts := by
      intro hp
      exact (Nat.not_lt_zero _) (p.parts_pos hp)
    have hq0 : 0 ∉ q.parts := by
      intro hq
      exact (Nat.not_lt_zero _) (q.parts_pos hq)
    simp [Multiset.count_eq_zero_of_notMem hp0, Multiset.count_eq_zero_of_notMem hq0]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    by_cases hmn : m ≤ n
    · have hi : m - 1 ∈ Finset.range n := by
        rw [Finset.mem_range]
        omega
      have hval := congr_fun (congr_fun h (m - 1)) hi
      simpa [Nat.sub_add_cancel hmpos] using hval
    · have hpmn : m ∉ p.parts := by
        intro hp
        exact hmn (Nat.Partition.le_of_mem_parts hp)
      have hqmn : m ∉ q.parts := by
        intro hq
        exact hmn (Nat.Partition.le_of_mem_parts hq)
      simp [Multiset.count_eq_zero_of_notMem hpmn, Multiset.count_eq_zero_of_notMem hqmn]

lemma partition_le_truncated_product {n : ℕ} {z : ℝ} (hz0 : 0 ≤ z) :
    part n * z ^ n
      ≤ ∏ i ∈ Finset.range n, ∑ j ∈ Finset.range (n + 1), z ^ ((i + 1) * j) := by
  classical
  let enc : Nat.Partition n → (i : ℕ) → i ∈ Finset.range n → ℕ :=
    fun p i _hi => p.parts.count (i + 1)
  let term : ((i : ℕ) → i ∈ Finset.range n → ℕ) → ℝ :=
    fun q => ∏ a ∈ (Finset.range n).attach, z ^ ((a.1 + 1) * q a.1 a.2)
  have henc_mem :
      ∀ p : Nat.Partition n, enc p ∈ (Finset.range n).pi (fun _ => Finset.range (n + 1)) := by
    intro p
    rw [Finset.mem_pi]
    intro i hi
    rw [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (partition_count_le_n p hi)
  have henc_inj : Set.InjOn enc (Finset.univ : Finset (Nat.Partition n)) := by
    intro p _ q _ hpq
    exact partition_multiplicity_injective n hpq
  have hterm_enc : ∀ p : Nat.Partition n, term (enc p) = z ^ n := by
    intro p
    dsimp [term, enc]
    exact partition_product_term_eq z p
  have hleft :
      part n * z ^ n = ∑ p : Nat.Partition n, term (enc p) := by
    simp [part, hterm_enc, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have himage_subset :
      Finset.image enc (Finset.univ : Finset (Nat.Partition n))
        ⊆ (Finset.range n).pi (fun _ => Finset.range (n + 1)) := by
    intro q hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨p, _hp, rfl⟩
    exact henc_mem p
  calc
    part n * z ^ n = ∑ p : Nat.Partition n, term (enc p) := hleft
    _ = ∑ q ∈ Finset.image enc (Finset.univ : Finset (Nat.Partition n)), term q := by
      exact (Finset.sum_image henc_inj).symm
    _ ≤ ∑ q ∈ (Finset.range n).pi (fun _ => Finset.range (n + 1)), term q := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
        (fun q _hq _hnot => by
          dsimp [term]
          exact Finset.prod_nonneg (fun a _ha => pow_nonneg hz0 _))
    _ = ∏ i ∈ Finset.range n, ∑ j ∈ Finset.range (n + 1), z ^ ((i + 1) * j) := by
      rw [Finset.prod_sum]

lemma partition_log_bound_x (n : ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Real.log (part n) ≤ -((n : ℝ) * Real.log z) + A * z / (1 - z) := by
  classical
  have hz0' : 0 ≤ z := hz0.le
  have hcomb := partition_le_truncated_product (n := n) (z := z) hz0'
  let trunc : ℝ := ∏ i ∈ Finset.range n,
    ∑ j ∈ Finset.range (n + 1), z ^ ((i + 1) * j)
  let euler : ℝ := ∏ i ∈ Finset.range n, (1 - z ^ (i + 1))⁻¹
  have hleft_pos : 0 < part n * z ^ n := mul_pos (part_pos n) (pow_pos hz0 n)
  have htrunc_pos : 0 < trunc := by
    dsimp [trunc]
    refine Finset.prod_pos ?_
    intro i hi
    refine Finset.sum_pos' ?_ ?_
    · intro j hj
      exact pow_nonneg hz0' _
    · refine ⟨0, by simp, ?_⟩
      simp
  have htrunc_le_euler : trunc ≤ euler := by
    dsimp [trunc, euler]
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      refine Finset.sum_nonneg ?_
      intro j hj
      exact pow_nonneg hz0' _
    · intro i hi
      have hbase_lt : z ^ (i + 1) < 1 :=
        pow_lt_one₀ hz0' hz1 (Nat.succ_ne_zero i)
      have hgeom := hasSum_geometric_of_lt_one (pow_nonneg hz0' _) hbase_lt
      have hsumle :
          (∑ j ∈ Finset.range (n + 1), (z ^ (i + 1)) ^ j)
            ≤ (1 - z ^ (i + 1))⁻¹ := by
        exact sum_le_hasSum (Finset.range (n + 1))
          (fun j hj => pow_nonneg (pow_nonneg hz0' _) _) hgeom
      simpa [pow_mul] using hsumle
  have hlog_comb :
      Real.log (part n * z ^ n) ≤ Real.log trunc :=
    Real.log_le_log hleft_pos (by simpa [trunc] using hcomb)
  have hlog_trunc_euler : Real.log trunc ≤ Real.log euler :=
    Real.log_le_log htrunc_pos htrunc_le_euler
  have hlog_euler :
      Real.log euler = ∑ i ∈ Finset.range n, -Real.log (1 - z ^ (i + 1)) := by
    dsimp [euler]
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Real.log_inv]
    · intro i hi
      have hbase_lt : z ^ (i + 1) < 1 :=
        pow_lt_one₀ hz0' hz1 (Nat.succ_ne_zero i)
      exact inv_ne_zero (by linarith)
  have hlog_left :
      Real.log (part n * z ^ n) = Real.log (part n) + (n : ℝ) * Real.log z := by
    rw [Real.log_mul (part_pos n).ne' (pow_pos hz0 n).ne']
    rw [Real.log_pow]
  have hmain :
      Real.log (part n) + (n : ℝ) * Real.log z ≤ A * z / (1 - z) := by
    calc
      Real.log (part n) + (n : ℝ) * Real.log z
          = Real.log (part n * z ^ n) := hlog_left.symm
      _ ≤ Real.log trunc := hlog_comb
      _ ≤ Real.log euler := hlog_trunc_euler
      _ = ∑ i ∈ Finset.range n, -Real.log (1 - z ^ (i + 1)) := hlog_euler
      _ ≤ A * z / (1 - z) := finite_partition_log_product_bound hz0 hz1
  linarith

theorem partition_log_upper (n : ℕ) (hn : 0 < n) :
    Real.log (part n) ≤ 2 * Real.sqrt (A * n) := by
  let s : ℝ := Real.sqrt (A * (n : ℝ))
  let y : ℝ := (n : ℝ) / s
  let z : ℝ := y / (1 + y)
  have hnR_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnR_nonneg : 0 ≤ (n : ℝ) := hnR_pos.le
  have hs_arg_nonneg : 0 ≤ A * (n : ℝ) := mul_nonneg A_nonneg hnR_nonneg
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos_of_pos (mul_pos A_pos hnR_pos)
  have hs_sq : s ^ 2 = A * (n : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt hs_arg_nonneg
  have hy_pos : 0 < y := by
    dsimp [y]
    exact div_pos hnR_pos hs_pos
  have hz_pos : 0 < z := by
    dsimp [z]
    positivity
  have hz_lt_one : z < 1 := by
    dsimp [z]
    rw [div_lt_one (by positivity : 0 < 1 + y)]
    linarith
  have hz_ratio : z / (1 - z) = y := by
    dsimp [z]
    field_simp [show 1 + y ≠ 0 by positivity]
    ring
  have hzinv : z⁻¹ = 1 + 1 / y := by
    dsimp [z]
    field_simp [hy_pos.ne', show 1 + y ≠ 0 by positivity]
    ring
  have hneglog : -Real.log z = Real.log (1 + 1 / y) := by
    rw [← Real.log_inv, hzinv]
  have hneglog_le : -Real.log z ≤ 1 / y := by
    rw [hneglog]
    exact log_one_div_le_self hy_pos
  have hny : (n : ℝ) / y = s := by
    dsimp [y]
    field_simp [hnR_pos.ne', hs_pos.ne']
  have hAy : A * y = s := by
    dsimp [y]
    field_simp [hs_pos.ne']
    rw [← hs_sq]
  have hopt :
      -((n : ℝ) * Real.log z) + A * z / (1 - z) ≤ 2 * s := by
    calc
      -((n : ℝ) * Real.log z) + A * z / (1 - z)
          = (n : ℝ) * (-Real.log z) + A * (z / (1 - z)) := by ring
      _ ≤ (n : ℝ) * (1 / y) + A * y := by
        rw [hz_ratio]
        exact add_le_add (mul_le_mul_of_nonneg_left hneglog_le hnR_nonneg) le_rfl
      _ = (n : ℝ) / y + A * y := by ring
      _ = 2 * s := by
        rw [hny, hAy]
        ring
  exact (partition_log_bound_x n hz_pos hz_lt_one).trans (by simpa [s] using hopt)

theorem two_sqrt_A_eq (n : ℕ) :
    2 * Real.sqrt (A * n) = Real.pi * Real.sqrt (2 * n / 3) := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hleft_nonneg : 0 ≤ 2 * Real.sqrt (A * n) := by positivity
  have hright_nonneg : 0 ≤ Real.pi * Real.sqrt (2 * n / 3) := by positivity
  have harg_right : 0 ≤ (2 : ℝ) * n / 3 := by positivity
  have hsq :
      (2 * Real.sqrt (A * n)) ^ 2
        = (Real.pi * Real.sqrt (2 * n / 3)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg A_nonneg hn_nonneg)]
    rw [mul_pow, Real.sq_sqrt harg_right]
    simp [A]
    ring
  have habs := (sq_eq_sq_iff_abs_eq_abs
    (2 * Real.sqrt (A * n)) (Real.pi * Real.sqrt (2 * n / 3))).mp hsq
  rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] at habs
  exact habs

theorem partition_upper_exp (n : ℕ) :
    part n ≤ Real.exp (Real.pi * Real.sqrt (2 * n / 3)) := by
  by_cases hn : 0 < n
  · have hlog := partition_log_upper n hn
    have hexp : part n ≤ Real.exp (2 * Real.sqrt (A * n)) :=
      (Real.log_le_iff_le_exp (part_pos n)).mp hlog
    rw [two_sqrt_A_eq n] at hexp
    exact hexp
  · have hn0 : n = 0 := by omega
    subst hn0
    simp [part]

end AnalyticCombinatorics.Ch8.Partitions
