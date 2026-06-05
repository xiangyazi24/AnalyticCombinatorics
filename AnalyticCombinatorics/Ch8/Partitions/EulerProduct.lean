import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.UpperBound
import AnalyticCombinatorics.Ch8.Partitions.LaplaceAsymptotic

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology

/-- The number of partitions of `n` all of whose parts are at most `K`. -/
noncomputable def partsLE (K n : ℕ) : ℕ :=
  Fintype.card {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K}

/-- The weighted size of a multiplicity vector for parts `1, ..., K`. -/
def multiplicityWeight (K : ℕ) (q : Fin K → ℕ) : ℕ :=
  ∑ i : Fin K, (i.1 + 1) * q i

def countsMultiset {K : ℕ} (q : Fin K → ℕ) : Multiset ℕ :=
  ∑ i : Fin K, Multiset.replicate (q i) (i.1 + 1)

lemma countsMultiset_sum {K : ℕ} (q : Fin K → ℕ) :
    (countsMultiset q).sum = multiplicityWeight K q := by
  simp [countsMultiset, multiplicityWeight, Multiset.sum_sum, Multiset.sum_replicate,
    mul_comm]

lemma countsMultiset_pos {K : ℕ} (q : Fin K → ℕ) {m : ℕ} :
    m ∈ countsMultiset q → 0 < m := by
  intro hm
  rw [countsMultiset, Multiset.mem_sum] at hm
  rcases hm with ⟨i, _hi, hmrep⟩
  rw [Multiset.mem_replicate] at hmrep
  rcases hmrep with ⟨_, rfl⟩
  exact Nat.succ_pos _

lemma countsMultiset_le {K : ℕ} (q : Fin K → ℕ) {m : ℕ} :
    m ∈ countsMultiset q → m ≤ K := by
  intro hm
  rw [countsMultiset, Multiset.mem_sum] at hm
  rcases hm with ⟨i, _hi, hmrep⟩
  rw [Multiset.mem_replicate] at hmrep
  rcases hmrep with ⟨_, rfl⟩
  exact i.2

lemma countsMultiset_count {K : ℕ} (q : Fin K → ℕ) (i : Fin K) :
    (countsMultiset q).count (i.1 + 1) = q i := by
  classical
  rw [countsMultiset, Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    have hval : (j : ℕ) ≠ (i : ℕ) := by
      intro h
      exact hji (Fin.ext h)
    simp [hval]
  · intro hi
    simp at hi

lemma countsMultiset_count_eq_zero_of_lt {K : ℕ} (q : Fin K → ℕ) {m : ℕ}
    (hmK : K < m) :
    (countsMultiset q).count m = 0 := by
  classical
  rw [countsMultiset, Multiset.count_sum']
  refine Finset.sum_eq_zero ?_
  intro i _hi
  have hne : i.1 + 1 ≠ m := by omega
  simp [Multiset.count_replicate, hne]

lemma countsMultiset_count_zero {K : ℕ} (q : Fin K → ℕ) :
    (countsMultiset q).count 0 = 0 := by
  classical
  rw [countsMultiset, Multiset.count_sum']
  refine Finset.sum_eq_zero ?_
  intro i _hi
  simp [Multiset.count_replicate]

noncomputable def partitionOfCountsAt {K n : ℕ}
    (q : {q : Fin K → ℕ // multiplicityWeight K q = n}) : Nat.Partition n where
  parts := countsMultiset q.1
  parts_pos := by
    intro _i hi
    exact countsMultiset_pos q.1 hi
  parts_sum := by
    rw [countsMultiset_sum, q.2]

lemma sum_fin_succ_eq_Icc {M : Type*} [AddCommMonoid M] (K : ℕ) (f : ℕ → M) :
    (∑ i : Fin K, f (i.1 + 1)) = ∑ k ∈ Finset.Icc 1 K, f k := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_bij (fun i _hi => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Icc]
    exact ⟨Nat.succ_pos i, Finset.mem_range.mp hi⟩
  · intro _a _ha _b _hb h
    exact Nat.succ.inj h
  · intro b hb
    rw [Finset.mem_Icc] at hb
    refine ⟨b - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · exact Nat.sub_add_cancel hb.1
  · intro i hi
    have hlt : i < K := Finset.mem_range.mp hi
    simp [hlt]

lemma prod_fin_succ_eq_Icc {M : Type*} [CommMonoid M] (K : ℕ) (f : ℕ → M) :
    (∏ i : Fin K, f (i.1 + 1)) = ∏ k ∈ Finset.Icc 1 K, f k := by
  classical
  rw [Finset.prod_fin_eq_prod_range]
  refine Finset.prod_bij (fun i _hi => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Icc]
    exact ⟨Nat.succ_pos i, Finset.mem_range.mp hi⟩
  · intro _a _ha _b _hb h
    exact Nat.succ.inj h
  · intro b hb
    rw [Finset.mem_Icc] at hb
    refine ⟨b - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · exact Nat.sub_add_cancel hb.1
  · intro i hi
    have hlt : i < K := Finset.mem_range.mp hi
    simp [hlt]

lemma bounded_partition_count_sum {K n : ℕ} (p : Nat.Partition n)
    (hp : ∀ m ∈ p.parts, m ≤ K) :
    multiplicityWeight K (fun i : Fin K => p.parts.count (i.1 + 1)) = n := by
  classical
  have hIcc :
      (∑ m ∈ Finset.Icc 1 K, p.parts.count m * m) = n := by
    have hsupport : p.parts.toFinset ⊆ Finset.Icc 1 K := by
      intro m hm
      rw [Finset.mem_Icc]
      exact ⟨p.parts_pos (by simpa using hm), hp m (by simpa using hm)⟩
    convert ← p.parts_sum
    rw [Finset.sum_multiset_count]
    apply Finset.sum_subset hsupport
    intro x _hx hxnot
    simp [Multiset.count_eq_zero_of_notMem (by simpa using hxnot)]
  dsimp [multiplicityWeight]
  rw [sum_fin_succ_eq_Icc K (fun m => m * p.parts.count m)]
  simpa [Nat.mul_comm] using hIcc

noncomputable def boundedPartitionEquivCounts (K n : ℕ) :
    {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K} ≃
      {q : Fin K → ℕ // multiplicityWeight K q = n} where
  toFun p := ⟨fun i => p.1.parts.count (i.1 + 1), bounded_partition_count_sum p.1 p.2⟩
  invFun q := ⟨partitionOfCountsAt q, by
    intro _m hm
    exact countsMultiset_le q.1 hm⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Nat.Partition.ext
    apply Multiset.ext.mpr
    intro m
    change Multiset.count m (countsMultiset (fun i : Fin K => p.1.parts.count (i.1 + 1))) =
      Multiset.count m p.1.parts
    by_cases hm0 : m = 0
    · subst hm0
      rw [countsMultiset_count_zero]
      have hp0 : 0 ∉ p.1.parts := by
        intro h
        exact (Nat.not_lt_zero _) (p.1.parts_pos h)
      simp [Multiset.count_eq_zero_of_notMem hp0]
    · have hmpos : 1 ≤ m := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hm0)
      by_cases hmK : m ≤ K
      · let i : Fin K := ⟨m - 1, by omega⟩
        have hi : i.1 + 1 = m := by dsimp [i]; omega
        calc
          Multiset.count m (countsMultiset (fun i : Fin K => p.1.parts.count (i.1 + 1)))
              = Multiset.count (i.1 + 1)
                  (countsMultiset (fun i : Fin K => p.1.parts.count (i.1 + 1))) := by rw [hi]
          _ = p.1.parts.count (i.1 + 1) := countsMultiset_count _ i
          _ = p.1.parts.count m := by rw [hi]
      · have hKlt : K < m := Nat.lt_of_not_ge hmK
        rw [countsMultiset_count_eq_zero_of_lt _ hKlt]
        have hnot : m ∉ p.1.parts := by
          intro hpmem
          exact (not_le_of_gt hKlt) (p.2 m hpmem)
        simp [Multiset.count_eq_zero_of_notMem hnot]
  right_inv := by
    intro q
    apply Subtype.ext
    funext i
    exact countsMultiset_count q.1 i

@[reducible]
noncomputable def weightFiberFintype (K n : ℕ) :
    Fintype {q : Fin K → ℕ // multiplicityWeight K q = n} :=
  Fintype.ofEquiv {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K}
    (boundedPartitionEquivCounts K n)

noncomputable def weightFiberCard (K n : ℕ) : ℕ :=
  @Fintype.card {q : Fin K → ℕ // multiplicityWeight K q = n}
    (weightFiberFintype K n)

lemma partsLE_eq_weightFiberCard (K n : ℕ) :
    partsLE K n = weightFiberCard K n := by
  change Fintype.card {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K} =
    @Fintype.card {q : Fin K → ℕ // multiplicityWeight K q = n}
      (weightFiberFintype K n)
  exact @Fintype.card_congr
    {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K}
    {q : Fin K → ℕ // multiplicityWeight K q = n}
    inferInstance
    (weightFiberFintype K n)
    (boundedPartitionEquivCounts K n)

lemma multiplicityWeight_snoc (K : ℕ) (q : Fin K → ℕ) (j : ℕ) :
    multiplicityWeight (K + 1) (Fin.snoc q j) =
      multiplicityWeight K q + (K + 1) * j := by
  dsimp [multiplicityWeight]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last]

def finSuccFunctionEquiv (K : ℕ) : ((Fin K → ℕ) × ℕ) ≃ (Fin (K + 1) → ℕ) where
  toFun z := Fin.snoc z.1 z.2
  invFun q := (Fin.init q, q (Fin.last K))
  left_inv := by
    intro z
    ext i <;> simp [Fin.init_snoc, Fin.snoc_last]
  right_inv := by
    intro q
    exact Fin.snoc_init_self q

def weightPreimageEquiv (K n : ℕ) :
    ↑((multiplicityWeight K) ⁻¹' ({n} : Set ℕ)) ≃
      {q : Fin K → ℕ // multiplicityWeight K q = n} where
  toFun b := ⟨b.1, b.2⟩
  invFun b := ⟨b.1, b.2⟩
  left_inv := by intro b; rfl
  right_inv := by intro b; rfl

lemma ennreal_finite_geom_product_eq_tsum_weight (K : ℕ) (r : ENNReal) :
    (∏ i : Fin K, (1 - r ^ (i.1 + 1))⁻¹) =
      ∑' q : Fin K → ℕ, r ^ multiplicityWeight K q := by
  induction K with
  | zero =>
      simp [multiplicityWeight]
  | succ K ih =>
      calc
        (∏ i : Fin (K + 1), (1 - r ^ (i.1 + 1))⁻¹)
            = (∏ i : Fin K, (1 - r ^ (i.1 + 1))⁻¹) * (1 - r ^ (K + 1))⁻¹ := by
                rw [Fin.prod_univ_castSucc]
                simp [Fin.val_last]
        _ = (∑' q : Fin K → ℕ, r ^ multiplicityWeight K q) *
              (∑' j : ℕ, r ^ ((K + 1) * j)) := by
                rw [ih]
                rw [← ENNReal.tsum_geometric (r ^ (K + 1))]
                congr
                ext j
                rw [pow_mul]
        _ = ∑' q : Fin K → ℕ, ∑' j : ℕ,
              r ^ multiplicityWeight K q * r ^ ((K + 1) * j) := by
                rw [← ENNReal.tsum_mul_right]
                congr
                ext q
                rw [← ENNReal.tsum_mul_left]
        _ = ∑' z : (Fin K → ℕ) × ℕ,
              r ^ multiplicityWeight K z.1 * r ^ ((K + 1) * z.2) := by
                rw [(ENNReal.tsum_prod).symm]
        _ = ∑' q : Fin (K + 1) → ℕ, r ^ multiplicityWeight (K + 1) q := by
                rw [← (finSuccFunctionEquiv K).tsum_eq
                  (fun q : Fin (K + 1) → ℕ => r ^ multiplicityWeight (K + 1) q)]
                congr
                ext z
                change r ^ multiplicityWeight K z.1 * r ^ ((K + 1) * z.2) =
                  r ^ multiplicityWeight (K + 1) (Fin.snoc z.1 z.2)
                rw [multiplicityWeight_snoc, pow_add]

lemma ennreal_tsum_weight_group_card (K : ℕ) (r : ENNReal)
    (hfin : ∀ n : ℕ, Fintype {q : Fin K → ℕ // multiplicityWeight K q = n}) :
    (∑' q : Fin K → ℕ, r ^ multiplicityWeight K q) =
      ∑' n : ℕ,
        (@Fintype.card {q : Fin K → ℕ // multiplicityWeight K q = n} (hfin n) : ENNReal)
          * r ^ n := by
  rw [← ENNReal.tsum_fiberwise (fun q : Fin K → ℕ => r ^ multiplicityWeight K q)
    (multiplicityWeight K)]
  congr
  ext n
  letI : Fintype {q : Fin K → ℕ // multiplicityWeight K q = n} := hfin n
  letI : Fintype ↑((multiplicityWeight K) ⁻¹' ({n} : Set ℕ)) :=
    Fintype.ofEquiv _ (weightPreimageEquiv K n).symm
  calc
    (∑' b : ↑((multiplicityWeight K) ⁻¹' ({n} : Set ℕ)), r ^ multiplicityWeight K b.1)
        = ∑' b : ↑((multiplicityWeight K) ⁻¹' ({n} : Set ℕ)), r ^ n := by
            congr
            ext b
            have hb : multiplicityWeight K b.1 = n := b.2
            simp [hb]
    _ = (Fintype.card ↑((multiplicityWeight K) ⁻¹' ({n} : Set ℕ)) : ENNReal) * r ^ n := by
            rw [tsum_fintype]
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = (@Fintype.card {q : Fin K → ℕ // multiplicityWeight K q = n} (hfin n) : ENNReal) *
          r ^ n := by
            rw [Fintype.card_congr (weightPreimageEquiv K n)]

lemma ennreal_finite_euler_prod_eq (K : ℕ) (r : ENNReal) :
    (∏ k ∈ Finset.Icc 1 K, (1 - r ^ k)⁻¹) =
      ∑' n : ℕ, (partsLE K n : ENNReal) * r ^ n := by
  rw [← prod_fin_succ_eq_Icc K (fun k : ℕ => (1 - r ^ k)⁻¹)]
  rw [ennreal_finite_geom_product_eq_tsum_weight]
  rw [ennreal_tsum_weight_group_card K r (fun n => weightFiberFintype K n)]
  congr
  ext n
  change (weightFiberCard K n : ENNReal) * r ^ n = (partsLE K n : ENNReal) * r ^ n
  rw [partsLE_eq_weightFiberCard]

lemma partsLE_le_part (K n : ℕ) : (partsLE K n : ℝ) ≤ part n := by
  dsimp [partsLE, part]
  exact_mod_cast (Fintype.card_subtype_le (fun p : Nat.Partition n => ∀ m ∈ p.parts, m ≤ K))

lemma finite_partsLE_summable (K : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun n : ℕ => (partsLE K n : ℝ) * x ^ n) := by
  let t : ℝ := -Real.log x
  have ht : 0 < t := by
    dsimp [t]
    exact neg_pos.mpr ((Real.log_neg_iff hx0).mpr hx1)
  have hs := partLaplace_summable (t := t) ht
  refine Summable.of_nonneg_of_le ?_ ?_ hs
  · intro n
    exact mul_nonneg (by positivity) (pow_nonneg hx0.le n)
  · intro n
    have hxpow : Real.exp (-(t * (n : ℝ))) = x ^ n := by
      have harg : -(t * (n : ℝ)) = (n : ℝ) * Real.log x := by
        dsimp [t]
        ring
      rw [harg, Real.exp_nat_mul, Real.exp_log hx0]
    rw [hxpow]
    exact mul_le_mul_of_nonneg_right (partsLE_le_part K n) (pow_nonneg hx0.le n)

theorem finite_euler_prod_eq (K : ℕ) {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    ∏ k ∈ Finset.Icc 1 K, (1 - x^k)⁻¹ = ∑' n : ℕ, (partsLE K n : ℝ) * x^n := by
  have hx0 : 0 ≤ x := h0.le
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ (partsLE K n : ℝ) * x ^ n := by
    intro n
    exact mul_nonneg (by positivity) (pow_nonneg hx0 n)
  have hsum_nonneg : 0 ≤ ∑' n : ℕ, (partsLE K n : ℝ) * x ^ n :=
    tsum_nonneg hterm_nonneg
  have hfactor_nonneg : ∀ k ∈ Finset.Icc 1 K, 0 ≤ (1 - x ^ k)⁻¹ := by
    intro k _hk
    rw [inv_nonneg]
    exact sub_nonneg.mpr (pow_le_one₀ (n := k) hx0 h1.le)
  have hprod_nonneg : 0 ≤ ∏ k ∈ Finset.Icc 1 K, (1 - x ^ k)⁻¹ :=
    Finset.prod_nonneg hfactor_nonneg
  apply (ENNReal.ofReal_eq_ofReal_iff hprod_nonneg hsum_nonneg).mp
  have hL :
      ENNReal.ofReal (∏ k ∈ Finset.Icc 1 K, (1 - x ^ k)⁻¹)
        = ∏ k ∈ Finset.Icc 1 K, (1 - ENNReal.ofReal x ^ k)⁻¹ := by
    rw [ENNReal.ofReal_prod_of_nonneg hfactor_nonneg]
    refine Finset.prod_congr rfl ?_
    intro k hk
    have hxk_nonneg : 0 ≤ x ^ k := pow_nonneg hx0 k
    have hxk_lt : x ^ k < 1 := by
      have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
      exact pow_lt_one₀ hx0 h1 hkpos.ne'
    rw [ENNReal.ofReal_inv_of_pos (sub_pos.mpr hxk_lt)]
    rw [ENNReal.ofReal_sub 1 hxk_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_pow hx0]
  have hsumm := finite_partsLE_summable K h0 h1
  have hR :
      ENNReal.ofReal (∑' n : ℕ, (partsLE K n : ℝ) * x ^ n)
        = ∑' n : ℕ, (partsLE K n : ENNReal) * ENNReal.ofReal x ^ n := by
    rw [ENNReal.ofReal_tsum_of_nonneg hterm_nonneg hsumm]
    congr
    ext n
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (partsLE K n : ℝ))]
    rw [ENNReal.ofReal_natCast, ENNReal.ofReal_pow hx0]
  rw [hL, hR]
  exact ennreal_finite_euler_prod_eq K (ENNReal.ofReal x)

noncomputable def boundedPartitionTopEquiv (K n : ℕ) (h : n ≤ K) :
    {p : Nat.Partition n // ∀ m ∈ p.parts, m ≤ K} ≃ Nat.Partition n where
  toFun p := p.1
  invFun p := ⟨p, by
    intro _m hm
    exact (Nat.Partition.le_of_mem_parts hm).trans h⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

lemma partsLE_eq_part_of_le {K n : ℕ} (h : n ≤ K) :
    (partsLE K n : ℝ) = part n := by
  dsimp [partsLE, part]
  exact_mod_cast Fintype.card_congr (boundedPartitionTopEquiv K n h)

lemma exp_neg_mul_nat_eq_pow (t : ℝ) (n : ℕ) :
    Real.exp (-(t * (n : ℝ))) = Real.exp (-t) ^ n := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem partLaplace_eq_finprod_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun K : ℕ => ∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * k)))⁻¹)
      atTop
      (𝓝 (PartLaplace t)) := by
  let x : ℝ := Real.exp (-t)
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    linarith
  have hsum_tendsto :
      Tendsto (fun K : ℕ => ∑' n : ℕ, (partsLE K n : ℝ) * x ^ n)
        atTop (𝓝 (∑' n : ℕ, part n * Real.exp (-(t * (n : ℝ))))) := by
    have hbound_summable : Summable (fun n : ℕ => part n * Real.exp (-(t * (n : ℝ)))) :=
      partLaplace_summable ht
    have hpoint :
        ∀ n : ℕ,
          Tendsto (fun K : ℕ => (partsLE K n : ℝ) * x ^ n)
            atTop (𝓝 (part n * Real.exp (-(t * (n : ℝ))))) := by
      intro n
      refine tendsto_const_nhds.congr' ?_
      refine Filter.eventually_atTop.mpr ⟨n, ?_⟩
      intro K hK
      change part n * Real.exp (-(t * (n : ℝ))) = (partsLE K n : ℝ) * x ^ n
      rw [partsLE_eq_part_of_le hK, exp_neg_mul_nat_eq_pow]
    have hbound :
        ∀ᶠ K : ℕ in atTop,
          ∀ n : ℕ,
            ‖(partsLE K n : ℝ) * x ^ n‖ ≤ part n * Real.exp (-(t * (n : ℝ))) := by
      refine Eventually.of_forall ?_
      intro K n
      rw [exp_neg_mul_nat_eq_pow]
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact mul_le_mul_of_nonneg_right (partsLE_le_part K n) (pow_nonneg hx0.le n)
      · exact mul_nonneg (by positivity) (pow_nonneg hx0.le n)
    exact tendsto_tsum_of_dominated_convergence hbound_summable hpoint hbound
  refine hsum_tendsto.congr' ?_
  refine Eventually.of_forall ?_
  intro K
  change (∑' n : ℕ, (partsLE K n : ℝ) * x ^ n) =
    ∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * k)))⁻¹
  rw [← finite_euler_prod_eq K hx0 hx1]
  refine Finset.prod_congr rfl ?_
  intro k hk
  have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
  have hpow : Real.exp (-(t * (k : ℝ))) = x ^ k := exp_neg_mul_nat_eq_pow t k
  rw [hpow]

end AnalyticCombinatorics.Ch8.Partitions
