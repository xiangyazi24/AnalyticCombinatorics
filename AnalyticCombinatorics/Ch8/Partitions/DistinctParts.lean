import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.UpperBound
import AnalyticCombinatorics.Ch8.Partitions.LaplaceAsymptotic
import AnalyticCombinatorics.Ch8.Partitions.EulerProduct
import AnalyticCombinatorics.Ch8.Partitions.LaplaceLimit
import AnalyticCombinatorics.Ch8.Partitions.Tauberian
import AnalyticCombinatorics.Ch8.Partitions.TauberianFull
import AnalyticCombinatorics.Ch8.Partitions.TauberianAssembly
import AnalyticCombinatorics.Ch8.Partitions.LogAsymptotic

namespace AnalyticCombinatorics.Ch8.Partitions.Distinct

open Filter
open scoped BigOperators Topology Asymptotics

-- This file mirrors the partition pipeline and has several long terminal
-- algebra/finite-type proofs; the higher heartbeat bound is local to it.
set_option maxHeartbeats 800000

/-- The number of partitions of `n` into distinct parts, as a real number. -/
noncomputable def qpart (n : ℕ) : ℝ :=
  (Fintype.card {p : Nat.Partition n // p.parts.Nodup} : ℝ)

/-- Laplace transform of the distinct-parts partition numbers. -/
noncomputable def QLaplace (t : ℝ) : ℝ :=
  ∑' n : ℕ, qpart n * Real.exp (-(t * n))

noncomputable def QPartCum (N : ℕ) : ℝ :=
  Tauberian.Cum qpart N

noncomputable def Kdistinct : ℝ :=
  A / 2

lemma Kdistinct_pos : 0 < Kdistinct := by
  dsimp [Kdistinct]
  nlinarith [A_pos]

lemma Kdistinct_nonneg : 0 ≤ Kdistinct :=
  Kdistinct_pos.le

lemma qpart_eq_card_distincts (n : ℕ) :
    qpart n = ((Nat.Partition.distincts n).card : ℝ) := by
  classical
  norm_num [qpart, Nat.Partition.distincts, Fintype.card_subtype]

lemma qpart_zero : qpart 0 = 1 := by
  classical
  simp [qpart]

lemma qpart_nonneg (n : ℕ) : 0 ≤ qpart n := by
  dsimp [qpart]
  positivity

lemma qpart_le_part (n : ℕ) : qpart n ≤ part n := by
  dsimp [qpart, part]
  exact_mod_cast
    (Fintype.card_subtype_le (fun p : Nat.Partition n => p.parts.Nodup))

lemma qpartLaplace_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => qpart n * Real.exp (-(t * n))) := by
  refine Summable.of_nonneg_of_le ?_ ?_ (partLaplace_summable ht)
  · intro n
    exact mul_nonneg (qpart_nonneg n) (Real.exp_pos _).le
  · intro n
    exact mul_le_mul_of_nonneg_right (qpart_le_part n) (Real.exp_pos _).le

lemma QLaplace_pos {t : ℝ} (ht : 0 < t) :
    0 < QLaplace t := by
  have hsum := qpartLaplace_summable ht
  have hnonneg : ∀ n : ℕ, 0 ≤ qpart n * Real.exp (-(t * n)) := by
    intro n
    exact mul_nonneg (qpart_nonneg n) (Real.exp_pos _).le
  have hzero :
      0 < (fun n : ℕ => qpart n * Real.exp (-(t * n))) 0 := by
    simp [qpart_zero]
  simpa [QLaplace] using hsum.tsum_pos hnonneg 0 hzero

lemma PartLaplace_pos' {t : ℝ} (ht : 0 < t) :
    0 < PartLaplace t := by
  have hsum := partLaplace_summable ht
  have hnonneg : ∀ n : ℕ, 0 ≤ part n * Real.exp (-(t * n)) := by
    intro n
    exact mul_nonneg (part_pos n).le (Real.exp_pos _).le
  have hzero :
      0 < (fun n : ℕ => part n * Real.exp (-(t * n))) 0 := by
    simpa using mul_pos (part_pos 0) (Real.exp_pos (-(t * (0 : ℕ))))
  simpa [PartLaplace] using hsum.tsum_pos hnonneg 0 hzero

/-! ### Finite distinct-products -/

/-- The weight of a Boolean choice of parts `1, ..., K`. -/
def distinctWeight (K : ℕ) (q : Fin K → Bool) : ℕ :=
  ∑ i : Fin K, if q i then i.1 + 1 else 0

def distinctChoiceMultiset {K : ℕ} (q : Fin K → Bool) : Multiset ℕ :=
  ∑ i : Fin K, if q i then ({i.1 + 1} : Multiset ℕ) else 0

lemma distinctChoiceMultiset_sum {K : ℕ} (q : Fin K → Bool) :
    (distinctChoiceMultiset q).sum = distinctWeight K q := by
  rw [distinctChoiceMultiset, Multiset.sum_sum]
  dsimp [distinctWeight]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases hq : q i <;> simp [hq]

lemma distinctChoiceMultiset_pos {K : ℕ} (q : Fin K → Bool) {m : ℕ} :
    m ∈ distinctChoiceMultiset q → 0 < m := by
  classical
  intro hm
  rw [distinctChoiceMultiset, Multiset.mem_sum] at hm
  rcases hm with ⟨i, _hi, hmif⟩
  by_cases hq : q i
  · rw [if_pos hq] at hmif
    rw [Multiset.mem_singleton] at hmif
    rw [hmif]
    exact Nat.succ_pos _
  · rw [if_neg hq] at hmif
    simp at hmif

lemma distinctChoiceMultiset_le {K : ℕ} (q : Fin K → Bool) {m : ℕ} :
    m ∈ distinctChoiceMultiset q → m ≤ K := by
  classical
  intro hm
  rw [distinctChoiceMultiset, Multiset.mem_sum] at hm
  rcases hm with ⟨i, _hi, hmif⟩
  by_cases hq : q i
  · rw [if_pos hq] at hmif
    rw [Multiset.mem_singleton] at hmif
    rw [hmif]
    exact i.2
  · rw [if_neg hq] at hmif
    simp at hmif

lemma distinctChoiceMultiset_count {K : ℕ} (q : Fin K → Bool) (i : Fin K) :
    (distinctChoiceMultiset q).count (i.1 + 1) = if q i then 1 else 0 := by
  classical
  rw [distinctChoiceMultiset, Multiset.count_sum']
  rw [Finset.sum_eq_single i]
  · by_cases hq : q i <;> simp [hq]
  · intro j _hj hji
    have hval : (j : ℕ) ≠ (i : ℕ) := by
      intro h
      exact hji (Fin.ext h)
    by_cases hq : q j <;> simp [hq, hval.symm]
  · intro hi
    simp at hi

lemma distinctChoiceMultiset_count_eq_zero_of_lt {K : ℕ} (q : Fin K → Bool) {m : ℕ}
    (hmK : K < m) :
    (distinctChoiceMultiset q).count m = 0 := by
  classical
  rw [distinctChoiceMultiset, Multiset.count_sum']
  refine Finset.sum_eq_zero ?_
  intro i _hi
  have hne : i.1 + 1 ≠ m := by omega
  by_cases hq : q i <;> simp [hq, hne.symm]

lemma distinctChoiceMultiset_count_zero {K : ℕ} (q : Fin K → Bool) :
    (distinctChoiceMultiset q).count 0 = 0 := by
  classical
  rw [distinctChoiceMultiset, Multiset.count_sum']
  refine Finset.sum_eq_zero ?_
  intro i _hi
  by_cases hq : q i <;> simp [hq]

lemma distinctChoiceMultiset_nodup {K : ℕ} (q : Fin K → Bool) :
    (distinctChoiceMultiset q).Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro m
  by_cases hm0 : m = 0
  · subst hm0
    simp [distinctChoiceMultiset_count_zero]
  · have hmpos : 1 ≤ m := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hm0)
    by_cases hmK : m ≤ K
    · let i : Fin K := ⟨m - 1, by omega⟩
      have hi : i.1 + 1 = m := by dsimp [i]; omega
      calc
        (distinctChoiceMultiset q).count m
            = (distinctChoiceMultiset q).count (i.1 + 1) := by rw [hi]
        _ = (if q i then 1 else 0) := distinctChoiceMultiset_count q i
        _ ≤ 1 := by by_cases hq : q i <;> simp [hq]
    · have hKlt : K < m := Nat.lt_of_not_ge hmK
      simp [distinctChoiceMultiset_count_eq_zero_of_lt q hKlt]

lemma mem_distinctChoiceMultiset_iff {K : ℕ} (q : Fin K → Bool) (i : Fin K) :
    i.1 + 1 ∈ distinctChoiceMultiset q ↔ q i = true := by
  classical
  rw [← Multiset.count_pos, distinctChoiceMultiset_count]
  cases q i <;> simp

noncomputable def distinctPartitionOfChoice {K n : ℕ}
    (q : {q : Fin K → Bool // distinctWeight K q = n}) : Nat.Partition n where
  parts := distinctChoiceMultiset q.1
  parts_pos := by
    intro _m hm
    exact distinctChoiceMultiset_pos q.1 hm
  parts_sum := by
    rw [distinctChoiceMultiset_sum, q.2]

lemma distinctPartitionOfChoice_nodup {K n : ℕ}
    (q : {q : Fin K → Bool // distinctWeight K q = n}) :
    (distinctPartitionOfChoice q).parts.Nodup :=
  distinctChoiceMultiset_nodup q.1

lemma distinctPartitionOfChoice_injective {K n : ℕ} :
    Function.Injective
      (fun q : {q : Fin K → Bool // distinctWeight K q = n} =>
        distinctPartitionOfChoice q) := by
  classical
  intro q r hqr
  apply Subtype.ext
  funext i
  have hparts :
      (distinctPartitionOfChoice q).parts = (distinctPartitionOfChoice r).parts :=
    congrArg Nat.Partition.parts hqr
  have hcount := congrArg (fun s : Multiset ℕ => s.count (i.1 + 1)) hparts
  dsimp [distinctPartitionOfChoice] at hcount
  rw [distinctChoiceMultiset_count q.1 i, distinctChoiceMultiset_count r.1 i] at hcount
  cases hq : q.1 i <;> cases hr : r.1 i <;> simp [hq, hr] at hcount ⊢

@[reducible]
noncomputable def distinctWeightFiberFintype (K n : ℕ) :
    Fintype {q : Fin K → Bool // distinctWeight K q = n} :=
  inferInstance

noncomputable def distinctWeightCard (K n : ℕ) : ℕ :=
  @Fintype.card {q : Fin K → Bool // distinctWeight K q = n}
    (distinctWeightFiberFintype K n)

lemma distinctWeightCard_le_qpart (K n : ℕ) :
    (distinctWeightCard K n : ℝ) ≤ qpart n := by
  dsimp [distinctWeightCard, qpart]
  exact_mod_cast
    Fintype.card_le_of_injective
      (fun q : {q : Fin K → Bool // distinctWeight K q = n} =>
        (⟨distinctPartitionOfChoice q, distinctPartitionOfChoice_nodup q⟩ :
          {p : Nat.Partition n // p.parts.Nodup}))
      (by
        intro q r hqr
        exact distinctPartitionOfChoice_injective (Subtype.ext_iff.mp hqr))

lemma distinctWeightCard_le_part (K n : ℕ) :
    (distinctWeightCard K n : ℝ) ≤ part n :=
  (distinctWeightCard_le_qpart K n).trans (qpart_le_part n)

lemma distinct_partition_weight_of_mem {K n : ℕ} (h : n ≤ K)
    (p : Nat.Partition n) (hp : p.parts.Nodup) :
    distinctWeight K (fun i : Fin K => decide (i.1 + 1 ∈ p.parts)) = n := by
  classical
  have hpK : ∀ m ∈ p.parts, m ≤ K := by
    intro m hm
    exact (Nat.Partition.le_of_mem_parts hm).trans h
  have hbounded := bounded_partition_count_sum (K := K) (n := n) p hpK
  calc
    distinctWeight K (fun i : Fin K => decide (i.1 + 1 ∈ p.parts))
        = multiplicityWeight K (fun i : Fin K => p.parts.count (i.1 + 1)) := by
          dsimp [distinctWeight, multiplicityWeight]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          by_cases hmem : i.1 + 1 ∈ p.parts
          · have hcount : p.parts.count (i.1 + 1) = 1 :=
              Multiset.count_eq_one_of_mem hp hmem
            simpa [hmem] using hcount
          · simp [hmem]
    _ = n := hbounded

noncomputable def distinctTopEquiv (K n : ℕ) (h : n ≤ K) :
    {q : Fin K → Bool // distinctWeight K q = n} ≃
      {p : Nat.Partition n // p.parts.Nodup} where
  toFun q := ⟨distinctPartitionOfChoice q, distinctPartitionOfChoice_nodup q⟩
  invFun p := ⟨fun i : Fin K => decide (i.1 + 1 ∈ p.1.parts),
    distinct_partition_weight_of_mem h p.1 p.2⟩
  left_inv := by
    classical
    intro q
    apply Subtype.ext
    funext i
    dsimp [distinctPartitionOfChoice]
    cases hqi : q.1 i
    · have hnot : i.1 + 1 ∉ distinctChoiceMultiset q.1 := by
        intro hm
        have htrue := (mem_distinctChoiceMultiset_iff q.1 i).1 hm
        simp [hqi] at htrue
      simp [hnot]
    · have hmem : i.1 + 1 ∈ distinctChoiceMultiset q.1 :=
        (mem_distinctChoiceMultiset_iff q.1 i).2 (by simp [hqi])
      simp [hmem]
  right_inv := by
    classical
    intro p
    apply Subtype.ext
    apply Nat.Partition.ext
    apply Multiset.ext.mpr
    intro m
    change
      (distinctChoiceMultiset
          (fun i : Fin K => decide (i.1 + 1 ∈ p.1.parts))).count m =
        p.1.parts.count m
    by_cases hm0 : m = 0
    · subst hm0
      rw [distinctChoiceMultiset_count_zero]
      have hp0 : 0 ∉ p.1.parts := by
        intro hp
        exact (Nat.not_lt_zero _) (p.1.parts_pos hp)
      simp [Multiset.count_eq_zero_of_notMem hp0]
    · have hmpos : 1 ≤ m := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hm0)
      by_cases hmK : m ≤ K
      · let i : Fin K := ⟨m - 1, by omega⟩
        have hi : i.1 + 1 = m := by dsimp [i]; omega
        calc
          (distinctChoiceMultiset
              (fun i : Fin K => decide (i.1 + 1 ∈ p.1.parts))).count m
              =
            (distinctChoiceMultiset
              (fun i : Fin K => decide (i.1 + 1 ∈ p.1.parts))).count (i.1 + 1) := by
              rw [hi]
          _ = (if decide (i.1 + 1 ∈ p.1.parts) then 1 else 0) :=
              distinctChoiceMultiset_count _ i
          _ = p.1.parts.count m := by
              by_cases hmem : m ∈ p.1.parts
              · have hcount : p.1.parts.count m = 1 :=
                  Multiset.count_eq_one_of_mem p.2 hmem
                simpa [hi, hmem] using hcount.symm
              · simp [hi, hmem]
      · have hKlt : K < m := Nat.lt_of_not_ge hmK
        rw [distinctChoiceMultiset_count_eq_zero_of_lt _ hKlt]
        have hnot : m ∉ p.1.parts := by
          intro hpmem
          exact (not_le_of_gt hKlt) ((Nat.Partition.le_of_mem_parts hpmem).trans h)
        simp [Multiset.count_eq_zero_of_notMem hnot]

lemma distinctWeightCard_eq_qpart_of_le {K n : ℕ} (h : n ≤ K) :
    (distinctWeightCard K n : ℝ) = qpart n := by
  dsimp [distinctWeightCard, qpart]
  exact_mod_cast Fintype.card_congr (distinctTopEquiv K n h)

def distinctWeightPreimageEquiv (K n : ℕ) :
    ↑((distinctWeight K) ⁻¹' ({n} : Set ℕ)) ≃
      {q : Fin K → Bool // distinctWeight K q = n} where
  toFun b := ⟨b.1, b.2⟩
  invFun b := ⟨b.1, b.2⟩
  left_inv := by intro b; rfl
  right_inv := by intro b; rfl

lemma ennreal_finite_distinct_prod_eq_tsum_weight (K : ℕ) (r : ENNReal) :
    (∏ i : Fin K, (1 + r ^ (i.1 + 1))) =
      ∑' q : Fin K → Bool, r ^ distinctWeight K q := by
  classical
  calc
    (∏ i : Fin K, (1 + r ^ (i.1 + 1)))
        = ∏ i : Fin K, ∑ b : Bool, if b then r ^ (i.1 + 1) else 1 := by
            congr
            ext i
            simp [add_comm]
    _ = ∑ q : Fin K → Bool, ∏ i : Fin K, if q i then r ^ (i.1 + 1) else 1 := by
            rw [Finset.prod_univ_sum]
            rw [Fintype.piFinset_univ]
    _ = ∑ q : Fin K → Bool, r ^ distinctWeight K q := by
            refine Finset.sum_congr rfl ?_
            intro q _hq
            calc
              (∏ i : Fin K, if q i then r ^ (i.1 + 1) else 1)
                  = ∏ i : Fin K, r ^ (if q i then i.1 + 1 else 0) := by
                      congr
                      ext i
                      by_cases hq : q i <;> simp [hq]
              _ = r ^ distinctWeight K q := by
                      simpa [distinctWeight] using
                        (Finset.prod_pow_eq_pow_sum
                          (Finset.univ : Finset (Fin K))
                          (fun i => if q i then i.1 + 1 else 0) r)
    _ = ∑' q : Fin K → Bool, r ^ distinctWeight K q := by
            rw [tsum_fintype]

lemma ennreal_tsum_distinct_weight_group_card (K : ℕ) (r : ENNReal) :
    (∑' q : Fin K → Bool, r ^ distinctWeight K q) =
      ∑' n : ℕ,
        (@Fintype.card {q : Fin K → Bool // distinctWeight K q = n}
            (distinctWeightFiberFintype K n) : ENNReal) * r ^ n := by
  rw [← ENNReal.tsum_fiberwise (fun q : Fin K → Bool => r ^ distinctWeight K q)
    (distinctWeight K)]
  congr
  ext n
  letI : Fintype ↑((distinctWeight K) ⁻¹' ({n} : Set ℕ)) := inferInstance
  calc
    (∑' b : ↑((distinctWeight K) ⁻¹' ({n} : Set ℕ)), r ^ distinctWeight K b.1)
        = ∑' b : ↑((distinctWeight K) ⁻¹' ({n} : Set ℕ)), r ^ n := by
            congr
            ext b
            have hb : distinctWeight K b.1 = n := b.2
            simp [hb]
    _ = (Fintype.card ↑((distinctWeight K) ⁻¹' ({n} : Set ℕ)) : ENNReal) * r ^ n := by
            rw [tsum_fintype]
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = (@Fintype.card {q : Fin K → Bool // distinctWeight K q = n}
          (distinctWeightFiberFintype K n) : ENNReal) * r ^ n := by
            have hcard :
                Fintype.card ↑((distinctWeight K) ⁻¹' ({n} : Set ℕ)) =
                  @Fintype.card {q : Fin K → Bool // distinctWeight K q = n}
                    (distinctWeightFiberFintype K n) :=
              Fintype.card_congr (distinctWeightPreimageEquiv K n)
            rw [hcard]

lemma ennreal_finite_distinct_prod_eq (K : ℕ) (r : ENNReal) :
    (∏ k ∈ Finset.Icc 1 K, (1 + r ^ k)) =
      ∑' n : ℕ, (distinctWeightCard K n : ENNReal) * r ^ n := by
  rw [← prod_fin_succ_eq_Icc K (fun k : ℕ => 1 + r ^ k)]
  rw [ennreal_finite_distinct_prod_eq_tsum_weight]
  rw [ennreal_tsum_distinct_weight_group_card]
  simp [distinctWeightCard]

lemma finite_distinct_summable (K : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun n : ℕ => (distinctWeightCard K n : ℝ) * x ^ n) := by
  let t : ℝ := -Real.log x
  have ht : 0 < t := by
    dsimp [t]
    exact neg_pos.mpr ((Real.log_neg_iff hx0).mpr hx1)
  have hs := qpartLaplace_summable (t := t) ht
  refine Summable.of_nonneg_of_le ?_ ?_ hs
  · intro n
    exact mul_nonneg (by positivity) (pow_nonneg hx0.le n)
  · intro n
    have hxpow : Real.exp (-(t * (n : ℝ))) = x ^ n := by
      have harg : -(t * (n : ℝ)) = (n : ℝ) * Real.log x := by
        dsimp [t]
        ring_nf
      rw [harg, Real.exp_nat_mul, Real.exp_log hx0]
    rw [hxpow]
    exact mul_le_mul_of_nonneg_right (distinctWeightCard_le_qpart K n) (pow_nonneg hx0.le n)

theorem finite_distinct_prod_eq (K : ℕ) {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    ∏ k ∈ Finset.Icc 1 K, (1 + x ^ k) =
      ∑' n : ℕ, (distinctWeightCard K n : ℝ) * x ^ n := by
  have hx0 : 0 ≤ x := h0.le
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ (distinctWeightCard K n : ℝ) * x ^ n := by
    intro n
    exact mul_nonneg (by positivity) (pow_nonneg hx0 n)
  have hsum_nonneg : 0 ≤ ∑' n : ℕ, (distinctWeightCard K n : ℝ) * x ^ n :=
    tsum_nonneg hterm_nonneg
  have hfactor_nonneg : ∀ k ∈ Finset.Icc 1 K, 0 ≤ 1 + x ^ k := by
    intro k _hk
    positivity
  have hprod_nonneg : 0 ≤ ∏ k ∈ Finset.Icc 1 K, (1 + x ^ k) :=
    Finset.prod_nonneg hfactor_nonneg
  apply (ENNReal.ofReal_eq_ofReal_iff hprod_nonneg hsum_nonneg).mp
  have hL :
      ENNReal.ofReal (∏ k ∈ Finset.Icc 1 K, (1 + x ^ k))
        = ∏ k ∈ Finset.Icc 1 K, (1 + ENNReal.ofReal x ^ k) := by
    rw [ENNReal.ofReal_prod_of_nonneg hfactor_nonneg]
    refine Finset.prod_congr rfl ?_
    intro k hk
    have hxk_nonneg : 0 ≤ x ^ k := pow_nonneg hx0 k
    rw [ENNReal.ofReal_add zero_le_one hxk_nonneg,
      ENNReal.ofReal_one, ENNReal.ofReal_pow hx0]
  have hsumm := finite_distinct_summable K h0 h1
  have hR :
      ENNReal.ofReal (∑' n : ℕ, (distinctWeightCard K n : ℝ) * x ^ n)
        = ∑' n : ℕ, (distinctWeightCard K n : ENNReal) * ENNReal.ofReal x ^ n := by
    rw [ENNReal.ofReal_tsum_of_nonneg hterm_nonneg hsumm]
    congr
    ext n
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (distinctWeightCard K n : ℝ))]
    rw [ENNReal.ofReal_natCast, ENNReal.ofReal_pow hx0]
  rw [hL, hR]
  exact ennreal_finite_distinct_prod_eq K (ENNReal.ofReal x)

theorem qpartLaplace_eq_finprod_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun K : ℕ => ∏ k ∈ Finset.Icc 1 K, (1 + Real.exp (-(t * k))))
      atTop
      (𝓝 (QLaplace t)) := by
  let x : ℝ := Real.exp (-t)
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    linarith
  have hsum_tendsto :
      Tendsto (fun K : ℕ => ∑' n : ℕ, (distinctWeightCard K n : ℝ) * x ^ n)
        atTop (𝓝 (∑' n : ℕ, qpart n * Real.exp (-(t * (n : ℝ))))) := by
    have hbound_summable : Summable (fun n : ℕ => qpart n * Real.exp (-(t * (n : ℝ)))) :=
      qpartLaplace_summable ht
    have hpoint :
        ∀ n : ℕ,
          Tendsto (fun K : ℕ => (distinctWeightCard K n : ℝ) * x ^ n)
            atTop (𝓝 (qpart n * Real.exp (-(t * (n : ℝ))))) := by
      intro n
      refine tendsto_const_nhds.congr' ?_
      refine Filter.eventually_atTop.mpr ⟨n, ?_⟩
      intro K hK
      change qpart n * Real.exp (-(t * (n : ℝ))) =
        (distinctWeightCard K n : ℝ) * x ^ n
      rw [distinctWeightCard_eq_qpart_of_le hK, exp_neg_mul_nat_eq_pow]
    have hbound :
        ∀ᶠ K : ℕ in atTop,
          ∀ n : ℕ,
            ‖(distinctWeightCard K n : ℝ) * x ^ n‖
              ≤ qpart n * Real.exp (-(t * (n : ℝ))) := by
      refine Eventually.of_forall ?_
      intro K n
      rw [exp_neg_mul_nat_eq_pow]
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact mul_le_mul_of_nonneg_right (distinctWeightCard_le_qpart K n)
          (pow_nonneg hx0.le n)
      · exact mul_nonneg (by positivity) (pow_nonneg hx0.le n)
    exact tendsto_tsum_of_dominated_convergence hbound_summable hpoint hbound
  refine hsum_tendsto.congr' ?_
  refine Eventually.of_forall ?_
  intro K
  change (∑' n : ℕ, (distinctWeightCard K n : ℝ) * x ^ n) =
    ∏ k ∈ Finset.Icc 1 K, (1 + Real.exp (-(t * k)))
  rw [← finite_distinct_prod_eq K hx0 hx1]
  refine Finset.prod_congr rfl ?_
  intro k hk
  have hpow : Real.exp (-(t * (k : ℝ))) = x ^ k := exp_neg_mul_nat_eq_pow t k
  rw [hpow]

lemma finite_distinct_product_ratio {t : ℝ} (ht : 0 < t) (K : ℕ) :
    (∏ k ∈ Finset.Icc 1 K, (1 + Real.exp (-(t * k)))) =
      (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * k)))⁻¹) /
        (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-((2 * t) * k)))⁻¹) := by
  have hfactor :
      ∀ k ∈ Finset.Icc 1 K,
        1 + Real.exp (-(t * (k : ℝ))) =
          (1 - Real.exp (-((2 * t) * (k : ℝ)))) *
            (1 - Real.exp (-(t * (k : ℝ))))⁻¹ := by
    intro k hk
    have hkpos_nat : 0 < k := (Finset.mem_Icc.mp hk).1
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkpos_nat
    have htk : 0 < t * (k : ℝ) := mul_pos ht hkpos
    have hne : 1 - Real.exp (-(t * (k : ℝ))) ≠ 0 := by
      have hlt : Real.exp (-(t * (k : ℝ))) < 1 := by
        rw [Real.exp_lt_one_iff]
        linarith
      exact sub_ne_zero.mpr hlt.ne'
    have hexp2 :
        Real.exp (-((2 * t) * (k : ℝ))) =
          Real.exp (-(t * (k : ℝ))) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring_nf
    rw [hexp2]
    field_simp [hne]
    ring_nf
  calc
    (∏ k ∈ Finset.Icc 1 K, (1 + Real.exp (-(t * k))))
        = ∏ k ∈ Finset.Icc 1 K,
            (1 - Real.exp (-((2 * t) * (k : ℝ)))) *
              (1 - Real.exp (-(t * (k : ℝ))))⁻¹ := by
            exact Finset.prod_congr rfl hfactor
    _ = (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-((2 * t) * (k : ℝ))))) *
          (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * (k : ℝ))))⁻¹) := by
            rw [Finset.prod_mul_distrib]
    _ = (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * k)))⁻¹) /
          (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-((2 * t) * k)))⁻¹) := by
            rw [div_eq_mul_inv]
            rw [show
              (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-((2 * t) * (k : ℝ))))⁻¹)⁻¹ =
                ∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-((2 * t) * (k : ℝ)))) by
              rw [Finset.prod_inv_distrib, inv_inv]]
            rw [mul_comm]

theorem QLaplace_eq_partLaplace_div {t : ℝ} (ht : 0 < t) :
    QLaplace t = PartLaplace t / PartLaplace (2 * t) := by
  have hq := qpartLaplace_eq_finprod_tendsto ht
  have hp := partLaplace_eq_finprod_tendsto ht
  have h2t : 0 < 2 * t := by positivity
  have hp2 := partLaplace_eq_finprod_tendsto h2t
  have hratio :
      Tendsto
        (fun K : ℕ =>
          (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * k)))⁻¹) /
            (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-((2 * t) * k)))⁻¹))
        atTop
        (𝓝 (PartLaplace t / PartLaplace (2 * t))) := by
    exact hp.div hp2 (PartLaplace_pos' h2t).ne'
  have hq' :
      Tendsto
        (fun K : ℕ =>
          (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * k)))⁻¹) /
            (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-((2 * t) * k)))⁻¹))
        atTop
        (𝓝 (QLaplace t)) := by
    exact hq.congr' (Eventually.of_forall fun K => finite_distinct_product_ratio ht K)
  exact tendsto_nhds_unique hq' hratio

/-! ### Log-Laplace asymptotic -/

lemma tendsto_two_mul_nhdsWithin_zero :
    Tendsto (fun t : ℝ => 2 * t) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa using (tendsto_const_nhds.mul
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id :
        Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0)))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos two_pos (by simpa using ht)

lemma partition_laplace_log_asymptotic_two_scaled :
    Tendsto (fun t : ℝ => t * Real.log (PartLaplace (2 * t)))
      (𝓝[>] 0) (𝓝 (A / 2)) := by
  have h :=
    partition_laplace_log_asymptotic.comp tendsto_two_mul_nhdsWithin_zero
  have hhalf := h.const_mul ((1 : ℝ) / 2)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (hhalf.congr' <| by
      filter_upwards with t
      dsimp
      ring_nf)

theorem distinct_laplace_log_asymptotic :
    Tendsto (fun t : ℝ => t * Real.log (QLaplace t))
      (𝓝[>] 0) (𝓝 Kdistinct) := by
  have hmain :
      Tendsto
        (fun t : ℝ =>
          t * Real.log (PartLaplace t) -
            t * Real.log (PartLaplace (2 * t)))
        (𝓝[>] 0) (𝓝 (A - A / 2)) :=
    partition_laplace_log_asymptotic.sub partition_laplace_log_asymptotic_two_scaled
  have hconv :
      Tendsto (fun t : ℝ => t * Real.log (QLaplace t))
        (𝓝[>] 0) (𝓝 (A - A / 2)) :=
    hmain.congr' <| by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : 0 < t := by simpa using ht
      have h2t : 0 < 2 * t := by positivity
      have hqeq := QLaplace_eq_partLaplace_div htpos
      have hp : PartLaplace t ≠ 0 := (PartLaplace_pos' htpos).ne'
      have hp2 : PartLaplace (2 * t) ≠ 0 := (PartLaplace_pos' h2t).ne'
      change t * Real.log (PartLaplace t) - t * Real.log (PartLaplace (2 * t)) =
        t * Real.log (QLaplace t)
      rw [hqeq, Real.log_div hp hp2]
      ring_nf
  have hconst : A - A / 2 = Kdistinct := by
    dsimp [Kdistinct]
    ring_nf
  simpa [hconst] using hconv

theorem distinct_cum_log_asymptotic :
    Tendsto
      (fun N : ℕ => Real.log (QPartCum N) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 (2 * Real.sqrt Kdistinct)) := by
  have h :=
    Tauberian.log_tauberian_cumulative_sqrt
      (a := qpart)
      (ha := qpart_nonneg)
      (ha0 := by rw [qpart_zero])
      (hK := Kdistinct_pos)
      (hsum := fun t ht => qpartLaplace_summable ht)
      (hF := by simpa [QLaplace, Kdistinct] using distinct_laplace_log_asymptotic)
  simpa [QPartCum] using h

/-! ### Monotone transfer from cumulative sums to coefficients -/

noncomputable def oddpart (n : ℕ) : ℝ :=
  (Fintype.card {p : Nat.Partition n // ∀ m ∈ p.parts, ¬ Even m} : ℝ)

lemma oddpart_eq_card_odds (n : ℕ) :
    oddpart n = ((Nat.Partition.odds n).card : ℝ) := by
  classical
  norm_num [oddpart, Nat.Partition.odds, Nat.Partition.restricted, Fintype.card_subtype]

lemma qpart_eq_oddpart (n : ℕ) :
    qpart n = oddpart n := by
  rw [qpart_eq_card_distincts, oddpart_eq_card_odds]
  exact_mod_cast (Nat.Partition.card_odds_eq_card_distincts n).symm

def addOnesOddPartition {m n : ℕ} (hmn : m ≤ n)
    (p : {p : Nat.Partition m // ∀ a ∈ p.parts, ¬ Even a}) :
    {p : Nat.Partition n // ∀ a ∈ p.parts, ¬ Even a} where
  val := addOnesPartition hmn p.1
  property := by
    intro a ha
    dsimp [addOnesPartition] at ha
    rw [Multiset.mem_add] at ha
    rcases ha with ha | ha
    · exact p.2 a ha
    · have h : a = 1 := Multiset.eq_of_mem_replicate ha
      rw [h]
      simp

lemma addOnesOddPartition_injective {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (addOnesOddPartition (m := m) (n := n) hmn) := by
  intro p q hpq
  apply Subtype.ext
  exact addOnesPartition_injective hmn (Subtype.ext_iff.mp hpq)

theorem oddpart_mono : Monotone oddpart := by
  intro m n hmn
  dsimp [oddpart]
  exact_mod_cast
    Fintype.card_le_of_injective
      (addOnesOddPartition hmn)
      (addOnesOddPartition_injective hmn)

theorem qpart_mono : Monotone qpart := by
  intro m n hmn
  rw [qpart_eq_oddpart m, qpart_eq_oddpart n]
  exact oddpart_mono hmn

theorem qpart_le_QPartCum (N : ℕ) :
    qpart N ≤ QPartCum N := by
  simpa [QPartCum] using
    (Tauberian.term_le_Cum (a := qpart) qpart_nonneg N)

theorem QPartCum_le_mul_qpart (N : ℕ) :
    QPartCum N ≤ (N + 1 : ℝ) * qpart N := by
  unfold QPartCum Tauberian.Cum
  calc
    (∑ n ∈ Finset.range (N + 1), qpart n)
        ≤ ∑ n ∈ Finset.range (N + 1), qpart N := by
          exact Finset.sum_le_sum fun n hn =>
            qpart_mono (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
    _ = (N + 1 : ℝ) * qpart N := by
          simp [Finset.sum_const, nsmul_eq_mul]

lemma QPartCum_log_qpart_log_gap_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        (Real.log (QPartCum N) - Real.log (qpart N)) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    log_nat_succ_div_sqrt_tendsto_zero ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
    have hqpart_pos : 0 < qpart N := by
      have h0 : 0 < qpart 0 := by
        rw [qpart_zero]
        norm_num
      exact h0.trans_le (qpart_mono (Nat.zero_le N))
    have hcum_pos : 0 < QPartCum N := hqpart_pos.trans_le (qpart_le_QPartCum N)
    have hlog_le : Real.log (qpart N) ≤ Real.log (QPartCum N) :=
      Real.log_le_log hqpart_pos (qpart_le_QPartCum N)
    rw [div_nonneg_iff]
    exact Or.inl ⟨sub_nonneg.mpr hlog_le, hsqrtN_pos.le⟩
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
    have hqpart_pos : 0 < qpart N := by
      have h0 : 0 < qpart 0 := by
        rw [qpart_zero]
        norm_num
      exact h0.trans_le (qpart_mono (Nat.zero_le N))
    have hcum_pos : 0 < QPartCum N := hqpart_pos.trans_le (qpart_le_QPartCum N)
    have hlog_upper :
        Real.log (QPartCum N) ≤ Real.log ((N + 1 : ℝ) * qpart N) :=
      Real.log_le_log hcum_pos (QPartCum_le_mul_qpart N)
    have hlog_mul :
        Real.log ((N + 1 : ℝ) * qpart N) =
          Real.log ((N : ℝ) + 1) + Real.log (qpart N) := by
      rw [Real.log_mul (by positivity : ((N : ℝ) + 1) ≠ 0) hqpart_pos.ne']
    have hnum :
        Real.log (QPartCum N) - Real.log (qpart N) ≤ Real.log ((N : ℝ) + 1) := by
      calc
        Real.log (QPartCum N) - Real.log (qpart N)
            ≤ Real.log ((N + 1 : ℝ) * qpart N) - Real.log (qpart N) := by
              exact sub_le_sub_right hlog_upper _
        _ = Real.log ((N : ℝ) + 1) := by
              rw [hlog_mul]
              ring_nf
    exact div_le_div_of_nonneg_right hnum hsqrtN_pos.le

lemma QPartCum_qpart_log_div_gap_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        Real.log (QPartCum N) / Real.sqrt (N : ℝ) -
          Real.log (qpart N) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 0) := by
  refine QPartCum_log_qpart_log_gap_tendsto_zero.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hsqrtN_ne : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
  field_simp [hsqrtN_ne]

theorem two_sqrt_Kdistinct_const_eq :
    2 * Real.sqrt Kdistinct = Real.pi * Real.sqrt (1 / 3) := by
  have hleft_nonneg : 0 ≤ 2 * Real.sqrt Kdistinct := by positivity
  have hright_nonneg : 0 ≤ Real.pi * Real.sqrt (1 / 3) := by positivity
  have hsq :
      (2 * Real.sqrt Kdistinct) ^ 2 =
        (Real.pi * Real.sqrt (1 / 3)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt Kdistinct_nonneg]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (1 / 3 : ℝ))]
    simp [Kdistinct, A]
    ring_nf
  have habs := (sq_eq_sq_iff_abs_eq_abs
    (2 * Real.sqrt Kdistinct) (Real.pi * Real.sqrt (1 / 3))).mp hsq
  rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] at habs
  exact habs

theorem distinct_log_asymptotic :
    Tendsto (fun n : ℕ => Real.log (qpart n) / Real.sqrt n)
      atTop (𝓝 (Real.pi * Real.sqrt (1 / 3))) := by
  have hq_to_cum :=
    distinct_cum_log_asymptotic.sub QPartCum_qpart_log_div_gap_tendsto_zero
  have hq :
      Tendsto
        (fun n : ℕ => Real.log (qpart n) / Real.sqrt (n : ℝ))
        atTop
        (𝓝 (2 * Real.sqrt Kdistinct)) := by
    simpa using
      (hq_to_cum.congr' <| by
        filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
        ring_nf)
  simpa [two_sqrt_Kdistinct_const_eq] using hq

lemma distinct_log_target_eq_const_mul_sqrt {n : ℕ} :
    Real.pi * Real.sqrt ((n : ℝ) / 3) =
      (Real.pi * Real.sqrt (1 / 3)) * Real.sqrt (n : ℝ) := by
  have harg : (n : ℝ) / 3 = (1 / 3 : ℝ) * (n : ℝ) := by ring_nf
  rw [harg, Real.sqrt_mul (by positivity : 0 ≤ (1 / 3 : ℝ))]
  ring_nf

theorem distinct_log_isEquivalent :
    (fun n : ℕ => Real.log (qpart n)) ~[atTop]
      (fun n : ℕ => Real.pi * Real.sqrt ((n : ℝ) / 3)) := by
  have htarget_ne :
      ∀ᶠ n : ℕ in atTop, Real.pi * Real.sqrt ((n : ℝ) / 3) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    positivity
  refine (Asymptotics.isEquivalent_iff_tendsto_one htarget_ne).mpr ?_
  have hconst_pos : 0 < Real.pi * Real.sqrt (1 / 3) := by positivity
  have hratio :
      Tendsto
        (fun n : ℕ =>
          (Real.log (qpart n) / Real.sqrt (n : ℝ)) /
            (Real.pi * Real.sqrt (1 / 3)))
        atTop
        (𝓝 1) := by
    have h :=
      distinct_log_asymptotic.div_const (Real.pi * Real.sqrt (1 / 3))
    simpa [hconst_pos.ne'] using h
  refine hratio.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnpos).ne'
  have hconst_ne : Real.pi * Real.sqrt (1 / 3) ≠ 0 := hconst_pos.ne'
  simp only [Pi.div_apply]
  rw [distinct_log_target_eq_const_mul_sqrt]
  field_simp [hsqrt_ne, hconst_ne]

end AnalyticCombinatorics.Ch8.Partitions.Distinct
