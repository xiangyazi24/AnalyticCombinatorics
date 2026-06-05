import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.UpperBound
import AnalyticCombinatorics.Ch8.Partitions.LaplaceAsymptotic
import AnalyticCombinatorics.Ch8.Partitions.EulerProduct
import AnalyticCombinatorics.Ch8.Partitions.LaplaceLimit
import AnalyticCombinatorics.Ch8.Partitions.Tauberian
import AnalyticCombinatorics.Ch8.Partitions.TauberianFull
import AnalyticCombinatorics.Ch8.Partitions.TauberianAssembly
import AnalyticCombinatorics.Ch8.Partitions.LogAsymptotic
import AnalyticCombinatorics.Ch8.Partitions.DistinctParts
import AnalyticCombinatorics.Ch8.Partitions.OddParts

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Glaisher

open Filter
open scoped BigOperators Topology Asymptotics

-- This file reuses the partition Tauberian pipeline with a finite `Fin m`
-- multiplicity model; the terminal finite-product and constant algebra proofs
-- need the same local heartbeat headroom as the distinct-parts file.
set_option maxHeartbeats 800000

/-- The genuine number of partitions of `n` whose parts are not divisible by `m`,
as a real number. -/
noncomputable def rpart (m n : ℕ) : ℝ :=
  ((Nat.Partition.restricted n (fun k => ¬ m ∣ k)).card : ℝ)

/-- The equinumerous count of partitions where each part is used fewer than `m` times. -/
noncomputable def cpart (m n : ℕ) : ℝ :=
  (Fintype.card {p : Nat.Partition n // ∀ k ∈ p.parts, p.parts.count k < m} : ℝ)

/-- Laplace transform of the restricted partition numbers. -/
noncomputable def RLaplace (m : ℕ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, rpart m n * Real.exp (-(t * n))

/-- Laplace transform of the count-restricted model. -/
noncomputable def CLaplace (m : ℕ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, cpart m n * Real.exp (-(t * n))

noncomputable def RPartCum (m N : ℕ) : ℝ :=
  Tauberian.Cum (rpart m) N

noncomputable def Kglaisher (m : ℕ) : ℝ :=
  (1 - 1 / (m : ℝ)) * A

lemma cpart_eq_card_countRestricted (m n : ℕ) :
    cpart m n = ((Nat.Partition.countRestricted n m).card : ℝ) := by
  classical
  norm_num [cpart, Nat.Partition.countRestricted, Fintype.card_subtype]

lemma rpart_eq_cpart {m : ℕ} (hm : 0 < m) (n : ℕ) :
    rpart m n = cpart m n := by
  rw [cpart_eq_card_countRestricted]
  dsimp [rpart]
  exact_mod_cast Nat.Partition.card_restricted_eq_card_countRestricted n hm

lemma rpart_zero (m : ℕ) : rpart m 0 = 1 := by
  classical
  simp [rpart, Nat.Partition.restricted]

lemma rpart_nonneg (m n : ℕ) : 0 ≤ rpart m n := by
  dsimp [rpart]
  positivity

lemma cpart_nonneg (m n : ℕ) : 0 ≤ cpart m n := by
  dsimp [cpart]
  positivity

lemma rpart_le_part (m n : ℕ) : rpart m n ≤ part n := by
  dsimp [rpart, part, Nat.Partition.restricted]
  exact_mod_cast Finset.card_filter_le _ _

lemma cpart_le_part (m n : ℕ) : cpart m n ≤ part n := by
  dsimp [cpart, part]
  exact_mod_cast
    (Fintype.card_subtype_le
      (fun p : Nat.Partition n => ∀ k ∈ p.parts, p.parts.count k < m))

lemma rpartLaplace_summable (m : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => rpart m n * Real.exp (-(t * n))) := by
  refine Summable.of_nonneg_of_le ?_ ?_ (partLaplace_summable ht)
  · intro n
    exact mul_nonneg (rpart_nonneg m n) (Real.exp_pos _).le
  · intro n
    exact mul_le_mul_of_nonneg_right (rpart_le_part m n) (Real.exp_pos _).le

lemma cpartLaplace_summable (m : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => cpart m n * Real.exp (-(t * n))) := by
  refine Summable.of_nonneg_of_le ?_ ?_ (partLaplace_summable ht)
  · intro n
    exact mul_nonneg (cpart_nonneg m n) (Real.exp_pos _).le
  · intro n
    exact mul_le_mul_of_nonneg_right (cpart_le_part m n) (Real.exp_pos _).le

lemma RLaplace_eq_CLaplace {m : ℕ} (hm : 0 < m) (t : ℝ) :
    RLaplace m t = CLaplace m t := by
  simp [RLaplace, CLaplace, rpart_eq_cpart hm]

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

/-! ### Finite count-restricted products -/

/-- Partitions of `n` with each multiplicity `< m` and all parts at most `K`. -/
noncomputable def cpartsLE (K m n : ℕ) : ℝ :=
  (Fintype.card
    {p : Nat.Partition n //
      (∀ k ∈ p.parts, p.parts.count k < m) ∧ (∀ k ∈ p.parts, k ≤ K)} : ℝ)

/-- Weighted size of a multiplicity vector with entries `0, ..., m - 1`. -/
def restrictedWeight (K m : ℕ) (q : Fin K → Fin m) : ℕ :=
  ∑ i : Fin K, (i.1 + 1) * (q i : ℕ)

def restrictedCountsMultiset {K m : ℕ} (q : Fin K → Fin m) : Multiset ℕ :=
  ∑ i : Fin K, Multiset.replicate (q i : ℕ) (i.1 + 1)

lemma restrictedCountsMultiset_sum {K m : ℕ} (q : Fin K → Fin m) :
    (restrictedCountsMultiset q).sum = restrictedWeight K m q := by
  simp [restrictedCountsMultiset, restrictedWeight, Multiset.sum_sum,
    Multiset.sum_replicate, mul_comm]

lemma restrictedCountsMultiset_pos {K m : ℕ} (q : Fin K → Fin m) {a : ℕ} :
    a ∈ restrictedCountsMultiset q → 0 < a := by
  intro ha
  rw [restrictedCountsMultiset, Multiset.mem_sum] at ha
  rcases ha with ⟨i, _hi, harep⟩
  rw [Multiset.mem_replicate] at harep
  rcases harep with ⟨_, rfl⟩
  exact Nat.succ_pos _

lemma restrictedCountsMultiset_le {K m : ℕ} (q : Fin K → Fin m) {a : ℕ} :
    a ∈ restrictedCountsMultiset q → a ≤ K := by
  intro ha
  rw [restrictedCountsMultiset, Multiset.mem_sum] at ha
  rcases ha with ⟨i, _hi, harep⟩
  rw [Multiset.mem_replicate] at harep
  rcases harep with ⟨_, rfl⟩
  exact i.2

lemma restrictedCountsMultiset_count {K m : ℕ} (q : Fin K → Fin m) (i : Fin K) :
    (restrictedCountsMultiset q).count (i.1 + 1) = (q i : ℕ) := by
  classical
  rw [restrictedCountsMultiset, Multiset.count_sum']
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

lemma restrictedCountsMultiset_count_eq_zero_of_lt {K m : ℕ} (q : Fin K → Fin m) {a : ℕ}
    (hKa : K < a) :
    (restrictedCountsMultiset q).count a = 0 := by
  classical
  rw [restrictedCountsMultiset, Multiset.count_sum']
  refine Finset.sum_eq_zero ?_
  intro i _hi
  have hne : i.1 + 1 ≠ a := by omega
  simp [Multiset.count_replicate, hne]

lemma restrictedCountsMultiset_count_zero {K m : ℕ} (q : Fin K → Fin m) :
    (restrictedCountsMultiset q).count 0 = 0 := by
  classical
  rw [restrictedCountsMultiset, Multiset.count_sum']
  refine Finset.sum_eq_zero ?_
  intro i _hi
  simp [Multiset.count_replicate]

noncomputable def restrictedPartitionOfCounts {K m n : ℕ}
    (q : {q : Fin K → Fin m // restrictedWeight K m q = n}) : Nat.Partition n where
  parts := restrictedCountsMultiset q.1
  parts_pos := by
    intro _a ha
    exact restrictedCountsMultiset_pos q.1 ha
  parts_sum := by
    rw [restrictedCountsMultiset_sum, q.2]

lemma restrictedPartitionOfCounts_count_lt {K m n : ℕ}
    (q : {q : Fin K → Fin m // restrictedWeight K m q = n}) :
    ∀ a ∈ (restrictedPartitionOfCounts q).parts,
      (restrictedPartitionOfCounts q).parts.count a < m := by
  intro a ha
  have haK : a ≤ K := restrictedCountsMultiset_le q.1 ha
  have hapos : 1 ≤ a := Nat.succ_le_iff.mpr (restrictedCountsMultiset_pos q.1 ha)
  let i : Fin K := ⟨a - 1, by omega⟩
  have hi : i.1 + 1 = a := by dsimp [i]; omega
  calc
    (restrictedPartitionOfCounts q).parts.count a
        = (restrictedCountsMultiset q.1).count (i.1 + 1) := by
            dsimp [restrictedPartitionOfCounts]
            rw [hi]
    _ = (q.1 i : ℕ) := restrictedCountsMultiset_count q.1 i
    _ < m := (q.1 i).2

lemma restrictedPartitionOfCounts_le {K m n : ℕ}
    (q : {q : Fin K → Fin m // restrictedWeight K m q = n}) :
    ∀ a ∈ (restrictedPartitionOfCounts q).parts, a ≤ K := by
  intro _a ha
  exact restrictedCountsMultiset_le q.1 ha

noncomputable def boundedCountRestrictedEquivCounts (K m n : ℕ) (hm : 0 < m) :
    {p : Nat.Partition n //
      (∀ k ∈ p.parts, p.parts.count k < m) ∧ (∀ k ∈ p.parts, k ≤ K)} ≃
      {q : Fin K → Fin m // restrictedWeight K m q = n} where
  toFun p :=
    ⟨fun i => ⟨p.1.parts.count (i.1 + 1), by
      by_cases hi : i.1 + 1 ∈ p.1.parts
      · exact p.2.1 (i.1 + 1) hi
      · rw [Multiset.count_eq_zero_of_notMem hi]
        exact hm⟩,
      by
        classical
        have hpK : ∀ a ∈ p.1.parts, a ≤ K := p.2.2
        exact bounded_partition_count_sum p.1 hpK⟩
  invFun q :=
    ⟨restrictedPartitionOfCounts q,
      ⟨restrictedPartitionOfCounts_count_lt q, restrictedPartitionOfCounts_le q⟩⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Nat.Partition.ext
    apply Multiset.ext.mpr
    intro a
    change
      (restrictedCountsMultiset
          (fun i : Fin K => ⟨p.1.parts.count (i.1 + 1), _⟩)).count a =
        p.1.parts.count a
    by_cases ha0 : a = 0
    · subst ha0
      rw [restrictedCountsMultiset_count_zero]
      have hp0 : 0 ∉ p.1.parts := by
        intro hp
        exact (Nat.not_lt_zero _) (p.1.parts_pos hp)
      simp [Multiset.count_eq_zero_of_notMem hp0]
    · have hapos : 1 ≤ a := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero ha0)
      by_cases haK : a ≤ K
      · let i : Fin K := ⟨a - 1, by omega⟩
        have hi : i.1 + 1 = a := by dsimp [i]; omega
        calc
          (restrictedCountsMultiset
              (fun i : Fin K => ⟨p.1.parts.count (i.1 + 1), _⟩)).count a
              =
            (restrictedCountsMultiset
              (fun i : Fin K => ⟨p.1.parts.count (i.1 + 1), _⟩)).count (i.1 + 1) := by
              rw [hi]
          _ = p.1.parts.count (i.1 + 1) :=
              restrictedCountsMultiset_count _ i
          _ = p.1.parts.count a := by rw [hi]
      · have hKlt : K < a := Nat.lt_of_not_ge haK
        rw [restrictedCountsMultiset_count_eq_zero_of_lt _ hKlt]
        have hnot : a ∉ p.1.parts := by
          intro hpmem
          exact (not_le_of_gt hKlt) (p.2.2 a hpmem)
        simp [Multiset.count_eq_zero_of_notMem hnot]
  right_inv := by
    intro q
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact restrictedCountsMultiset_count q.1 i

noncomputable def restrictedWeightCard (K m n : ℕ) : ℕ :=
  Fintype.card {q : Fin K → Fin m // restrictedWeight K m q = n}

lemma cpartsLE_eq_restrictedWeightCard {K m n : ℕ} (hm : 0 < m) :
    cpartsLE K m n = (restrictedWeightCard K m n : ℝ) := by
  dsimp [cpartsLE, restrictedWeightCard]
  exact_mod_cast Fintype.card_congr (boundedCountRestrictedEquivCounts K m n hm)

lemma cpartsLE_le_part (K m n : ℕ) :
    cpartsLE K m n ≤ part n := by
  dsimp [cpartsLE, part]
  exact_mod_cast
    Fintype.card_le_of_injective
      (fun p :
        {p : Nat.Partition n //
          (∀ k ∈ p.parts, p.parts.count k < m) ∧ (∀ k ∈ p.parts, k ≤ K)} => p.1)
      (by intro p q hpq; exact Subtype.ext hpq)

lemma cpartsLE_le_cpart (K m n : ℕ) :
    cpartsLE K m n ≤ cpart m n := by
  dsimp [cpartsLE, cpart]
  exact_mod_cast
    Fintype.card_le_of_injective
      (fun p :
        {p : Nat.Partition n //
          (∀ k ∈ p.parts, p.parts.count k < m) ∧ (∀ k ∈ p.parts, k ≤ K)} =>
        (⟨p.1, p.2.1⟩ :
          {p : Nat.Partition n // ∀ k ∈ p.parts, p.parts.count k < m}))
      (by
        intro p q hpq
        have hval : p.1 = q.1 :=
          congrArg
            (fun x : {p : Nat.Partition n // ∀ k ∈ p.parts, p.parts.count k < m} => x.1)
            hpq
        exact Subtype.ext hval)

noncomputable def boundedCountRestrictedTopEquiv (K m n : ℕ) (h : n ≤ K) :
    {p : Nat.Partition n //
      (∀ k ∈ p.parts, p.parts.count k < m) ∧ (∀ k ∈ p.parts, k ≤ K)} ≃
      {p : Nat.Partition n // ∀ k ∈ p.parts, p.parts.count k < m} where
  toFun p := ⟨p.1, p.2.1⟩
  invFun p := ⟨p.1, ⟨p.2, by
    intro a ha
    exact (Nat.Partition.le_of_mem_parts ha).trans h⟩⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

lemma cpartsLE_eq_cpart_of_le {K m n : ℕ} (h : n ≤ K) :
    cpartsLE K m n = cpart m n := by
  dsimp [cpartsLE, cpart]
  exact_mod_cast Fintype.card_congr (boundedCountRestrictedTopEquiv K m n h)

def restrictedWeightPreimageEquiv (K m n : ℕ) :
    ↑((restrictedWeight K m) ⁻¹' ({n} : Set ℕ)) ≃
      {q : Fin K → Fin m // restrictedWeight K m q = n} where
  toFun q := ⟨q.1, q.2⟩
  invFun q := ⟨q.1, q.2⟩
  left_inv := by intro q; rfl
  right_inv := by intro q; rfl

lemma ennreal_finite_restricted_prod_eq_tsum_weight (K m : ℕ) (r : ENNReal) :
    (∏ i : Fin K, ∑ j : Fin m, r ^ ((i.1 + 1) * (j : ℕ))) =
      ∑' q : Fin K → Fin m, r ^ restrictedWeight K m q := by
  classical
  calc
    (∏ i : Fin K, ∑ j : Fin m, r ^ ((i.1 + 1) * (j : ℕ)))
        = ∑ q : Fin K → Fin m,
            ∏ i : Fin K, r ^ ((i.1 + 1) * (q i : ℕ)) := by
            rw [Finset.prod_univ_sum]
            rw [Fintype.piFinset_univ]
    _ = ∑ q : Fin K → Fin m, r ^ restrictedWeight K m q := by
            refine Finset.sum_congr rfl ?_
            intro q _hq
            simpa [restrictedWeight] using
              (Finset.prod_pow_eq_pow_sum
                (Finset.univ : Finset (Fin K))
                (fun i => (i.1 + 1) * (q i : ℕ)) r)
    _ = ∑' q : Fin K → Fin m, r ^ restrictedWeight K m q := by
            rw [tsum_fintype]

lemma ennreal_tsum_restricted_weight_group_card (K m : ℕ) (r : ENNReal) :
    (∑' q : Fin K → Fin m, r ^ restrictedWeight K m q) =
      ∑' n : ℕ, (restrictedWeightCard K m n : ENNReal) * r ^ n := by
  rw [← ENNReal.tsum_fiberwise (fun q : Fin K → Fin m => r ^ restrictedWeight K m q)
    (restrictedWeight K m)]
  congr
  ext n
  letI : Fintype ↑((restrictedWeight K m) ⁻¹' ({n} : Set ℕ)) := inferInstance
  calc
    (∑' q : ↑((restrictedWeight K m) ⁻¹' ({n} : Set ℕ)), r ^ restrictedWeight K m q.1)
        = ∑' q : ↑((restrictedWeight K m) ⁻¹' ({n} : Set ℕ)), r ^ n := by
            congr
            ext q
            have hq : restrictedWeight K m q.1 = n := q.2
            simp [hq]
    _ = (Fintype.card ↑((restrictedWeight K m) ⁻¹' ({n} : Set ℕ)) : ENNReal) * r ^ n := by
            rw [tsum_fintype]
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = (restrictedWeightCard K m n : ENNReal) * r ^ n := by
            have hcard :
                Fintype.card ↑((restrictedWeight K m) ⁻¹' ({n} : Set ℕ)) =
                  restrictedWeightCard K m n :=
              Fintype.card_congr (restrictedWeightPreimageEquiv K m n)
            rw [hcard]

lemma ennreal_finite_restricted_prod_eq {K m : ℕ} (hm : 0 < m) (r : ENNReal) :
    (∏ k ∈ Finset.Icc 1 K, ∑ j : Fin m, r ^ (k * (j : ℕ))) =
      ∑' n : ℕ, ENNReal.ofReal (cpartsLE K m n) * r ^ n := by
  rw [← prod_fin_succ_eq_Icc K (fun k : ℕ => ∑ j : Fin m, r ^ (k * (j : ℕ)))]
  rw [ennreal_finite_restricted_prod_eq_tsum_weight]
  rw [ennreal_tsum_restricted_weight_group_card]
  congr
  ext n
  have hcard := cpartsLE_eq_restrictedWeightCard (K := K) (m := m) (n := n) hm
  rw [hcard, ENNReal.ofReal_natCast]

lemma finite_cpartsLE_summable (K m : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun n : ℕ => cpartsLE K m n * x ^ n) := by
  let t : ℝ := -Real.log x
  have ht : 0 < t := by
    dsimp [t]
    exact neg_pos.mpr ((Real.log_neg_iff hx0).mpr hx1)
  have hs := partLaplace_summable (t := t) ht
  refine Summable.of_nonneg_of_le ?_ ?_ hs
  · intro n
    exact mul_nonneg (by dsimp [cpartsLE]; positivity) (pow_nonneg hx0.le n)
  · intro n
    have hxpow : Real.exp (-(t * (n : ℝ))) = x ^ n := by
      have harg : -(t * (n : ℝ)) = (n : ℝ) * Real.log x := by
        dsimp [t]
        ring
      rw [harg, Real.exp_nat_mul, Real.exp_log hx0]
    rw [hxpow]
    exact mul_le_mul_of_nonneg_right (cpartsLE_le_part K m n) (pow_nonneg hx0.le n)

theorem finite_countRestricted_prod_eq {K m : ℕ} (hm : 0 < m)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (∏ k ∈ Finset.Icc 1 K, ∑ j : Fin m, x ^ (k * (j : ℕ))) =
      ∑' n : ℕ, cpartsLE K m n * x ^ n := by
  have hx0le : 0 ≤ x := hx0.le
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ cpartsLE K m n * x ^ n := by
    intro n
    exact mul_nonneg (by dsimp [cpartsLE]; positivity) (pow_nonneg hx0le n)
  have hsum_nonneg : 0 ≤ ∑' n : ℕ, cpartsLE K m n * x ^ n :=
    tsum_nonneg hterm_nonneg
  have hfactor_nonneg :
      ∀ k ∈ Finset.Icc 1 K, 0 ≤ ∑ j : Fin m, x ^ (k * (j : ℕ)) := by
    intro k _hk
    exact Finset.sum_nonneg fun j _ => pow_nonneg hx0le _
  have hprod_nonneg : 0 ≤ ∏ k ∈ Finset.Icc 1 K, ∑ j : Fin m, x ^ (k * (j : ℕ)) :=
    Finset.prod_nonneg hfactor_nonneg
  apply (ENNReal.ofReal_eq_ofReal_iff hprod_nonneg hsum_nonneg).mp
  have hL :
      ENNReal.ofReal (∏ k ∈ Finset.Icc 1 K, ∑ j : Fin m, x ^ (k * (j : ℕ)))
        = ∏ k ∈ Finset.Icc 1 K, ∑ j : Fin m, ENNReal.ofReal x ^ (k * (j : ℕ)) := by
    rw [ENNReal.ofReal_prod_of_nonneg hfactor_nonneg]
    refine Finset.prod_congr rfl ?_
    intro k hk
    rw [ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [ENNReal.ofReal_pow hx0le]
    · intro j _hj
      exact pow_nonneg hx0le _
  have hsumm := finite_cpartsLE_summable K m hx0 hx1
  have hR :
      ENNReal.ofReal (∑' n : ℕ, cpartsLE K m n * x ^ n)
        = ∑' n : ℕ, ENNReal.ofReal (cpartsLE K m n) * ENNReal.ofReal x ^ n := by
    rw [ENNReal.ofReal_tsum_of_nonneg hterm_nonneg hsumm]
    congr
    ext n
    rw [ENNReal.ofReal_mul (by dsimp [cpartsLE]; positivity : 0 ≤ cpartsLE K m n)]
    rw [ENNReal.ofReal_pow hx0le]
  rw [hL, hR]
  exact ennreal_finite_restricted_prod_eq (K := K) (m := m) hm (ENNReal.ofReal x)

theorem cpartLaplace_eq_finprod_tendsto {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun K : ℕ =>
        ∏ k ∈ Finset.Icc 1 K,
          ∑ j : Fin m, (Real.exp (-t)) ^ (k * (j : ℕ)))
      atTop
      (𝓝 (CLaplace m t)) := by
  let x : ℝ := Real.exp (-t)
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    linarith
  have hsum_tendsto :
      Tendsto (fun K : ℕ => ∑' n : ℕ, cpartsLE K m n * x ^ n)
        atTop (𝓝 (∑' n : ℕ, cpart m n * Real.exp (-(t * (n : ℝ))))) := by
    have hbound_summable : Summable (fun n : ℕ => cpart m n * Real.exp (-(t * (n : ℝ)))) :=
      cpartLaplace_summable m ht
    have hpoint :
        ∀ n : ℕ,
          Tendsto (fun K : ℕ => cpartsLE K m n * x ^ n)
            atTop (𝓝 (cpart m n * Real.exp (-(t * (n : ℝ))))) := by
      intro n
      refine tendsto_const_nhds.congr' ?_
      refine Filter.eventually_atTop.mpr ⟨n, ?_⟩
      intro K hK
      change cpart m n * Real.exp (-(t * (n : ℝ))) = cpartsLE K m n * x ^ n
      rw [cpartsLE_eq_cpart_of_le hK, exp_neg_mul_nat_eq_pow]
    have hbound :
        ∀ᶠ K : ℕ in atTop,
          ∀ n : ℕ,
            ‖cpartsLE K m n * x ^ n‖
              ≤ cpart m n * Real.exp (-(t * (n : ℝ))) := by
      refine Eventually.of_forall ?_
      intro K n
      rw [exp_neg_mul_nat_eq_pow]
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact mul_le_mul_of_nonneg_right
          (cpartsLE_le_cpart K m n)
          (pow_nonneg hx0.le n)
      · exact mul_nonneg (by dsimp [cpartsLE]; positivity) (pow_nonneg hx0.le n)
    exact tendsto_tsum_of_dominated_convergence hbound_summable hpoint hbound
  refine hsum_tendsto.congr' ?_
  refine Eventually.of_forall ?_
  intro K
  change (∑' n : ℕ, cpartsLE K m n * x ^ n) =
    ∏ k ∈ Finset.Icc 1 K, ∑ j : Fin m, x ^ (k * (j : ℕ))
  exact (finite_countRestricted_prod_eq (K := K) (m := m) hm hx0 hx1).symm

lemma finite_geometric_factor_eq {x : ℝ} {m k : ℕ} (hx0 : 0 < x) (hx1 : x < 1)
    (hk : 0 < k) :
    (∑ j : Fin m, x ^ (k * (j : ℕ))) =
      (1 - x ^ (m * k)) * (1 - x ^ k)⁻¹ := by
  have hxk_lt : x ^ k < 1 := pow_lt_one₀ hx0.le hx1 hk.ne'
  have hxk_ne : 1 - x ^ k ≠ 0 := sub_ne_zero.mpr hxk_lt.ne'
  calc
    (∑ j : Fin m, x ^ (k * (j : ℕ)))
        = ∑ j : Fin m, (x ^ k) ^ (j : ℕ) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [pow_mul]
    _ = ∑ j ∈ Finset.range m, (x ^ k) ^ j := by
            rw [Fin.sum_univ_eq_sum_range]
    _ = (1 - (x ^ k) ^ m) * (1 - x ^ k)⁻¹ := by
            have hgeom := geom_sum_mul_neg (x ^ k) m
            rw [← hgeom]
            field_simp [hxk_ne]
    _ = (1 - x ^ (m * k)) * (1 - x ^ k)⁻¹ := by
            rw [pow_mul]
            ring_nf

lemma finite_countRestricted_product_ratio {m : ℕ} (_hm : 0 < m)
    {t : ℝ} (ht : 0 < t) (K : ℕ) :
    (∏ k ∈ Finset.Icc 1 K, ∑ j : Fin m, (Real.exp (-t)) ^ (k * (j : ℕ))) =
      (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * k)))⁻¹) /
        (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(((m : ℝ) * t) * k)))⁻¹) := by
  let x : ℝ := Real.exp (-t)
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    linarith
  have hfactor :
      ∀ k ∈ Finset.Icc 1 K,
        (∑ j : Fin m, x ^ (k * (j : ℕ))) =
          (1 - Real.exp (-(((m : ℝ) * t) * (k : ℝ)))) *
            (1 - Real.exp (-(t * (k : ℝ))))⁻¹ := by
    intro k hk
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hxk : x ^ k = Real.exp (-(t * (k : ℝ))) := by
      dsimp [x]
      exact (exp_neg_mul_nat_eq_pow t k).symm
    have hxmk : x ^ (m * k) = Real.exp (-(((m : ℝ) * t) * (k : ℝ))) := by
      dsimp [x]
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [finite_geometric_factor_eq hx0 hx1 hkpos, hxmk, hxk]
  calc
    (∏ k ∈ Finset.Icc 1 K, ∑ j : Fin m, (Real.exp (-t)) ^ (k * (j : ℕ)))
        = ∏ k ∈ Finset.Icc 1 K,
            (1 - Real.exp (-(((m : ℝ) * t) * (k : ℝ)))) *
              (1 - Real.exp (-(t * (k : ℝ))))⁻¹ := by
            exact Finset.prod_congr rfl hfactor
    _ = (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(((m : ℝ) * t) * (k : ℝ))))) *
          (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * (k : ℝ))))⁻¹) := by
            rw [Finset.prod_mul_distrib]
    _ = (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * k)))⁻¹) /
          (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(((m : ℝ) * t) * k)))⁻¹) := by
            rw [div_eq_mul_inv]
            rw [show
              (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(((m : ℝ) * t) * (k : ℝ))))⁻¹)⁻¹ =
                ∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(((m : ℝ) * t) * (k : ℝ)))) by
              rw [Finset.prod_inv_distrib, inv_inv]]
            rw [mul_comm]

theorem CLaplace_eq_partLaplace_div {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    CLaplace m t = PartLaplace t / PartLaplace ((m : ℝ) * t) := by
  have hc := cpartLaplace_eq_finprod_tendsto (m := m) hm ht
  have hp := partLaplace_eq_finprod_tendsto ht
  have hmt : 0 < (m : ℝ) * t := by
    exact mul_pos (Nat.cast_pos.mpr hm) ht
  have hpm := partLaplace_eq_finprod_tendsto hmt
  have hratio :
      Tendsto
        (fun K : ℕ =>
          (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * k)))⁻¹) /
            (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(((m : ℝ) * t) * k)))⁻¹))
        atTop
        (𝓝 (PartLaplace t / PartLaplace ((m : ℝ) * t))) := by
    exact hp.div hpm (PartLaplace_pos' hmt).ne'
  have hc' :
      Tendsto
        (fun K : ℕ =>
          (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(t * k)))⁻¹) /
            (∏ k ∈ Finset.Icc 1 K, (1 - Real.exp (-(((m : ℝ) * t) * k)))⁻¹))
        atTop
        (𝓝 (CLaplace m t)) := by
    exact hc.congr' (Eventually.of_forall fun K =>
      finite_countRestricted_product_ratio (m := m) hm ht K)
  exact tendsto_nhds_unique hc' hratio

theorem RLaplace_eq_partLaplace_div {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    RLaplace m t = PartLaplace t / PartLaplace ((m : ℝ) * t) := by
  rw [RLaplace_eq_CLaplace hm, CLaplace_eq_partLaplace_div hm ht]

/-! ### Log-Laplace asymptotic -/

lemma tendsto_nat_mul_nhdsWithin_zero {m : ℕ} (hm : 0 < m) :
    Tendsto (fun t : ℝ => (m : ℝ) * t) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa using (tendsto_const_nhds.mul
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id :
        Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0)))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos (Nat.cast_pos.mpr hm) (by simpa using ht)

lemma partition_laplace_log_asymptotic_scaled {m : ℕ} (hm : 0 < m) :
    Tendsto (fun t : ℝ => t * Real.log (PartLaplace ((m : ℝ) * t)))
      (𝓝[>] 0) (𝓝 (A / (m : ℝ))) := by
  have h :=
    partition_laplace_log_asymptotic.comp (tendsto_nat_mul_nhdsWithin_zero hm)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hscaled := h.const_mul ((1 : ℝ) / (m : ℝ))
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hmR] using
    (hscaled.congr' <| by
      filter_upwards with t
      dsimp
      field_simp [hmR]
      )

lemma Kglaisher_pos {m : ℕ} (hm : 2 ≤ m) : 0 < Kglaisher m := by
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm)
  have hdiv : 1 / (m : ℝ) < 1 := by
    rw [div_lt_iff₀ hmpos]
    simpa using hmone
  dsimp [Kglaisher]
  exact mul_pos (sub_pos.mpr hdiv) A_pos

lemma Kglaisher_nonneg {m : ℕ} (hm : 2 ≤ m) : 0 ≤ Kglaisher m :=
  (Kglaisher_pos hm).le

theorem glaisher_laplace_log_asymptotic (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (fun t : ℝ => t * Real.log (RLaplace m t))
      (𝓝[>] 0) (𝓝 (Kglaisher m)) := by
  have hmposNat : 0 < m := lt_of_lt_of_le (by norm_num : 0 < 2) hm
  have hmain :
      Tendsto
        (fun t : ℝ =>
          t * Real.log (PartLaplace t) -
            t * Real.log (PartLaplace ((m : ℝ) * t)))
        (𝓝[>] 0) (𝓝 (A - A / (m : ℝ))) :=
    partition_laplace_log_asymptotic.sub (partition_laplace_log_asymptotic_scaled hmposNat)
  have hconv :
      Tendsto (fun t : ℝ => t * Real.log (RLaplace m t))
        (𝓝[>] 0) (𝓝 (A - A / (m : ℝ))) :=
    hmain.congr' <| by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : 0 < t := by simpa using ht
      have hmt : 0 < (m : ℝ) * t := by
        exact mul_pos (Nat.cast_pos.mpr hmposNat) htpos
      have hqeq := RLaplace_eq_partLaplace_div (m := m) hmposNat htpos
      have hp : PartLaplace t ≠ 0 := (PartLaplace_pos' htpos).ne'
      have hpm : PartLaplace ((m : ℝ) * t) ≠ 0 := (PartLaplace_pos' hmt).ne'
      change t * Real.log (PartLaplace t) -
          t * Real.log (PartLaplace ((m : ℝ) * t)) =
        t * Real.log (RLaplace m t)
      rw [hqeq, Real.log_div hp hpm]
      ring
  have hconst : A - A / (m : ℝ) = Kglaisher m := by
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hmposNat.ne'
    dsimp [Kglaisher]
    field_simp [hmR]
  simpa [hconst] using hconv

theorem glaisher_cum_log_asymptotic (m : ℕ) (hm : 2 ≤ m) :
    Tendsto
      (fun N : ℕ => Real.log (RPartCum m N) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 (2 * Real.sqrt (Kglaisher m))) := by
  have h :=
    Tauberian.log_tauberian_cumulative_sqrt
      (a := rpart m)
      (ha := rpart_nonneg m)
      (ha0 := by rw [rpart_zero])
      (hK := Kglaisher_pos hm)
      (hsum := fun t ht => rpartLaplace_summable m ht)
      (hF := by simpa [RLaplace, Kglaisher] using glaisher_laplace_log_asymptotic m hm)
  simpa [RPartCum] using h

/-! ### Monotone transfer from cumulative sums to coefficients -/

lemma rpart_eq_card_restricted_subtype (m n : ℕ) :
    rpart m n =
      (Fintype.card {p : Nat.Partition n // ∀ k ∈ p.parts, ¬ m ∣ k} : ℝ) := by
  classical
  norm_num [rpart, Nat.Partition.restricted, Fintype.card_subtype]

def addOnesRestrictedPartition {m a b : ℕ} (hm : 2 ≤ m) (hab : a ≤ b)
    (p : {p : Nat.Partition a // ∀ k ∈ p.parts, ¬ m ∣ k}) :
    {p : Nat.Partition b // ∀ k ∈ p.parts, ¬ m ∣ k} where
  val := addOnesPartition hab p.1
  property := by
    intro k hk
    dsimp [addOnesPartition] at hk
    rw [Multiset.mem_add] at hk
    rcases hk with hk | hk
    · exact p.2 k hk
    · have hkone : k = 1 := Multiset.eq_of_mem_replicate hk
      rw [hkone]
      intro hdvd
      exact Nat.not_dvd_of_pos_of_lt Nat.one_pos (by omega) hdvd

lemma addOnesRestrictedPartition_injective {m a b : ℕ} (hm : 2 ≤ m) (hab : a ≤ b) :
    Function.Injective (addOnesRestrictedPartition (m := m) (a := a) (b := b) hm hab) := by
  intro p q hpq
  apply Subtype.ext
  exact addOnesPartition_injective hab (Subtype.ext_iff.mp hpq)

theorem rpart_mono {m : ℕ} (hm : 2 ≤ m) : Monotone (rpart m) := by
  intro a b hab
  rw [rpart_eq_card_restricted_subtype m a, rpart_eq_card_restricted_subtype m b]
  exact_mod_cast
    Fintype.card_le_of_injective
      (addOnesRestrictedPartition (m := m) hm hab)
      (addOnesRestrictedPartition_injective (m := m) hm hab)

theorem rpart_le_RPartCum (m N : ℕ) :
    rpart m N ≤ RPartCum m N := by
  simpa [RPartCum] using
    (Tauberian.term_le_Cum (a := rpart m) (rpart_nonneg m) N)

theorem RPartCum_le_mul_rpart {m : ℕ} (hm : 2 ≤ m) (N : ℕ) :
    RPartCum m N ≤ (N + 1 : ℝ) * rpart m N := by
  unfold RPartCum Tauberian.Cum
  calc
    (∑ n ∈ Finset.range (N + 1), rpart m n)
        ≤ ∑ n ∈ Finset.range (N + 1), rpart m N := by
          exact Finset.sum_le_sum fun n hn =>
            rpart_mono hm (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
    _ = (N + 1 : ℝ) * rpart m N := by
          simp [Finset.sum_const, nsmul_eq_mul]

lemma RPartCum_log_rpart_log_gap_tendsto_zero {m : ℕ} (hm : 2 ≤ m) :
    Tendsto
      (fun N : ℕ =>
        (Real.log (RPartCum m N) - Real.log (rpart m N)) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    log_nat_succ_div_sqrt_tendsto_zero ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
    have hrpart_pos : 0 < rpart m N := by
      have h0 : 0 < rpart m 0 := by
        rw [rpart_zero]
        norm_num
      exact h0.trans_le (rpart_mono hm (Nat.zero_le N))
    have hcum_pos : 0 < RPartCum m N := hrpart_pos.trans_le (rpart_le_RPartCum m N)
    have hlog_le : Real.log (rpart m N) ≤ Real.log (RPartCum m N) :=
      Real.log_le_log hrpart_pos (rpart_le_RPartCum m N)
    rw [div_nonneg_iff]
    exact Or.inl ⟨sub_nonneg.mpr hlog_le, hsqrtN_pos.le⟩
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
    have hrpart_pos : 0 < rpart m N := by
      have h0 : 0 < rpart m 0 := by
        rw [rpart_zero]
        norm_num
      exact h0.trans_le (rpart_mono hm (Nat.zero_le N))
    have hcum_pos : 0 < RPartCum m N := hrpart_pos.trans_le (rpart_le_RPartCum m N)
    have hlog_upper :
        Real.log (RPartCum m N) ≤ Real.log ((N + 1 : ℝ) * rpart m N) :=
      Real.log_le_log hcum_pos (RPartCum_le_mul_rpart hm N)
    have hlog_mul :
        Real.log ((N + 1 : ℝ) * rpart m N) =
          Real.log ((N : ℝ) + 1) + Real.log (rpart m N) := by
      rw [Real.log_mul (by positivity : ((N : ℝ) + 1) ≠ 0) hrpart_pos.ne']
    have hnum :
        Real.log (RPartCum m N) - Real.log (rpart m N) ≤ Real.log ((N : ℝ) + 1) := by
      calc
        Real.log (RPartCum m N) - Real.log (rpart m N)
            ≤ Real.log ((N + 1 : ℝ) * rpart m N) - Real.log (rpart m N) := by
              exact sub_le_sub_right hlog_upper _
        _ = Real.log ((N : ℝ) + 1) := by
              rw [hlog_mul]
              ring
    exact div_le_div_of_nonneg_right hnum hsqrtN_pos.le

lemma RPartCum_rpart_log_div_gap_tendsto_zero {m : ℕ} (hm : 2 ≤ m) :
    Tendsto
      (fun N : ℕ =>
        Real.log (RPartCum m N) / Real.sqrt (N : ℝ) -
          Real.log (rpart m N) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 0) := by
  refine (RPartCum_log_rpart_log_gap_tendsto_zero hm).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hsqrtN_ne : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
  field_simp [hsqrtN_ne]

theorem two_sqrt_Kglaisher_const_eq (m : ℕ) (hm : 2 ≤ m) :
    2 * Real.sqrt (Kglaisher m) =
      Real.pi * Real.sqrt (2 * (1 - 1 / (m : ℝ)) / 3) := by
  have hcoef_nonneg : 0 ≤ 1 - 1 / (m : ℝ) := by
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
    have hmone : 1 < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm)
    have hdiv : 1 / (m : ℝ) < 1 := by
      rw [div_lt_iff₀ hmpos]
      simpa using hmone
    exact (sub_pos.mpr hdiv).le
  have hleft_nonneg : 0 ≤ 2 * Real.sqrt (Kglaisher m) := by positivity
  have hright_nonneg : 0 ≤ Real.pi * Real.sqrt (2 * (1 - 1 / (m : ℝ)) / 3) := by
    positivity
  have harg_nonneg : 0 ≤ 2 * (1 - 1 / (m : ℝ)) / 3 := by positivity
  have hsq :
      (2 * Real.sqrt (Kglaisher m)) ^ 2 =
        (Real.pi * Real.sqrt (2 * (1 - 1 / (m : ℝ)) / 3)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Kglaisher_nonneg hm)]
    rw [mul_pow, Real.sq_sqrt harg_nonneg]
    simp [Kglaisher, A]
    ring_nf
  have habs := (sq_eq_sq_iff_abs_eq_abs
    (2 * Real.sqrt (Kglaisher m))
    (Real.pi * Real.sqrt (2 * (1 - 1 / (m : ℝ)) / 3))).mp hsq
  rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] at habs
  exact habs

/-- Glaisher restricted-partitions log-asymptotic. -/
theorem glaisher_log_asymptotic (m : ℕ) (hm : 2 ≤ m) :
    Tendsto (fun n : ℕ => Real.log (rpart m n) / Real.sqrt n) atTop
      (𝓝 (Real.pi * Real.sqrt (2 * (1 - 1 / (m : ℝ)) / 3))) := by
  have h_to_cum :=
    (glaisher_cum_log_asymptotic m hm).sub (RPartCum_rpart_log_div_gap_tendsto_zero hm)
  have hr :
      Tendsto
        (fun n : ℕ => Real.log (rpart m n) / Real.sqrt (n : ℝ))
        atTop
        (𝓝 (2 * Real.sqrt (Kglaisher m))) := by
    simpa using
      (h_to_cum.congr' <| by
        filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
        ring)
  simpa [two_sqrt_Kglaisher_const_eq m hm] using hr

/-- At `m = 2`, the restricted count is the odd-parts count. -/
theorem rpart_two_eq_opart (n : ℕ) :
    rpart 2 n = Odd.opart n := by
  have hfin :
      Nat.Partition.restricted n (fun k => ¬ 2 ∣ k) = Nat.Partition.odds n := by
    ext p
    simp [Nat.Partition.restricted, Nat.Partition.odds, even_iff_two_dvd]
  change ((Nat.Partition.restricted n (fun k => ¬ 2 ∣ k)).card : ℝ) =
    ((Nat.Partition.odds n).card : ℝ)
  rw [hfin]

/-- The `m = 2` specialization has the odd-parts constant `π√(1/3)`. -/
theorem glaisher_log_asymptotic_two :
    Tendsto (fun n : ℕ => Real.log (rpart 2 n) / Real.sqrt n) atTop
      (𝓝 (Real.pi * Real.sqrt (1 / 3))) := by
  convert glaisher_log_asymptotic 2 (by norm_num) using 1
  norm_num

end AnalyticCombinatorics.Ch8.Partitions.Glaisher
