/-
  Analytic Combinatorics — Examples
  Binary strings (sequences over a 2-letter alphabet)

  The combinatorial class of binary strings is SEQ(B), where B has Bool as its
  Obj and every letter has size 1.

  OGF identity: B(z) = 2z, hence STRINGS(z) = 1 / (1 - 2z) = ∑ 2ⁿ zⁿ.
  Combinatorial identity: there are 2ⁿ binary strings of length n.

  Reference: F&S Example I.4.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import AnalyticCombinatorics.PartA.Ch2.LabelledClass

open PowerSeries CombinatorialClass

/-- The 2-letter alphabet: every Bool is an atom of size 1. -/
def boolClass : CombinatorialClass where
  Obj := Bool
  size _ := 1
  finite_level _ := Set.finite_univ.subset (Set.subset_univ _)

-- Bridge instances so that `Finset boolClass.Obj` is well-behaved.
instance : DecidableEq boolClass.Obj := inferInstanceAs (DecidableEq Bool)
instance : Fintype boolClass.Obj := inferInstanceAs (Fintype Bool)

namespace boolClass

/-- Both Bool elements have size 1, so `boolClass.count 0 = 0`. -/
lemma count_zero : boolClass.count 0 = 0 := by
  simp only [count]
  rw [Finset.card_eq_zero]
  ext b
  simp only [Finset.notMem_empty, iff_false]
  intro hb
  have hsz : boolClass.size b = 0 :=
    (boolClass.finite_level 0).mem_toFinset.mp hb
  exact absurd hsz (by show (1 : ℕ) ≠ 0; omega)

/-- There are exactly 2 letters of size 1. -/
lemma count_one : boolClass.count 1 = 2 := by
  show (boolClass.level 1).card = 2
  have h_false : false ∈ boolClass.level 1 :=
    (boolClass.finite_level 1).mem_toFinset.mpr (rfl : boolClass.size false = 1)
  have h_true : true ∈ boolClass.level 1 :=
    (boolClass.finite_level 1).mem_toFinset.mpr (rfl : boolClass.size true = 1)
  have h_card : boolClass.level 1 = ({false, true} : Finset boolClass.Obj) := by
    ext b
    refine ⟨fun _ => ?_, fun hb => ?_⟩
    · cases b
      · exact Finset.mem_insert_self false _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self true)
    · rcases Finset.mem_insert.mp hb with rfl | hb'
      · exact h_false
      · obtain rfl := Finset.mem_singleton.mp hb'
        exact h_true
  rw [h_card]
  rfl

/-- For `k ≠ 1`, no letter has size `k`. -/
private lemma count_eq_zero_of_ne_one {k : ℕ} (hk : k ≠ 1) : boolClass.count k = 0 := by
  simp only [count]
  rw [Finset.card_eq_zero]
  ext b
  simp only [Finset.notMem_empty, iff_false]
  intro hb
  have hsz : boolClass.size b = k :=
    (boolClass.finite_level k).mem_toFinset.mp hb
  exact hk hsz.symm

end boolClass

/-- The class of binary strings: finite sequences of bits. -/
noncomputable def stringClass : CombinatorialClass :=
  seqClass boolClass boolClass.count_zero

/-- A binary string of length n is a `List Bool` whose total size (= length, since
    each letter has size 1) equals n. There are 2ⁿ such strings. -/
theorem stringClass_count_eq_pow (n : ℕ) : stringClass.count n = 2 ^ n := by
  induction n with
  | zero =>
    show (seqClass boolClass _).count 0 = 1
    rw [seqClass.count_zero]
  | succ m ih =>
    show (seqClass boolClass _).count (m + 1) = 2 ^ (m + 1)
    rw [seqClass.count_succ]
    rw [Finset.sum_eq_single (1, m)]
    · show boolClass.count 1 * (seqClass boolClass _).count m = 2 ^ (m + 1)
      rw [boolClass.count_one]
      change 2 * stringClass.count m = 2 ^ (m + 1)
      rw [ih, pow_succ]; ring
    · rintro ⟨k, j⟩ hkj hne
      by_cases hk : k = 1
      · exfalso
        subst hk
        rw [Finset.mem_antidiagonal] at hkj
        apply hne
        congr; omega
      · rw [boolClass.count_eq_zero_of_ne_one hk, zero_mul]
    · intro h
      exfalso
      apply h
      rw [Finset.mem_antidiagonal]
      omega

/-! Sanity checks: 2⁰=1, 2¹=2, 2²=4, 2³=8 binary strings. -/
example : stringClass.count 0 = 1 := stringClass_count_eq_pow 0
example : stringClass.count 1 = 2 := stringClass_count_eq_pow 1
example : stringClass.count 3 = 8 := stringClass_count_eq_pow 3

/-- Closed form for the OGF of binary strings: `1 / (1 - 2z)`. -/
theorem stringClass_ogfZ_mul_one_sub_two_X :
    ogfZ stringClass * (1 - 2 * PowerSeries.X) = 1 := by
  rw [show ogfZ stringClass * (1 - 2 * PowerSeries.X) =
      ogfZ stringClass - 2 * (ogfZ stringClass * PowerSeries.X) by ring]
  ext n
  rcases n with _ | m
  · simp only [map_sub]
    rw [show coeff 0 (ogfZ stringClass) = (stringClass.count 0 : ℤ) by
      simp [ogfZ, coeff_ogf]]
    simp [stringClass_count_eq_pow]
  · have hshift : coeff (m + 1) (2 * (ogfZ stringClass * PowerSeries.X)) =
        2 * (stringClass.count m : ℤ) := by
      rw [show (2 : PowerSeries ℤ) = PowerSeries.C (2 : ℤ) by
        ext n
        simp]
      rw [PowerSeries.coeff_C_mul]
      rw [PowerSeries.coeff_succ_mul_X]
      simp [ogfZ, coeff_ogf]
    rw [map_sub, hshift]
    simp [ogfZ, coeff_ogf, stringClass_count_eq_pow, pow_succ]
    ring

example : stringClass.count 2 = 4 := by rw [stringClass_count_eq_pow]; decide
example : stringClass.count 4 = 16 := by rw [stringClass_count_eq_pow]; decide
example : stringClass.count 5 = 32 := by rw [stringClass_count_eq_pow]; decide

lemma boolClass_count_eq_zero_of_ne_one {k : ℕ} (hk : k ≠ 1) : boolClass.count k = 0 := by
  simp only [CombinatorialClass.count]
  rw [Finset.card_eq_zero]
  ext b
  simp only [Finset.notMem_empty, iff_false]
  intro hb
  have hsz : boolClass.size b = k :=
    (boolClass.finite_level k).mem_toFinset.mp hb
  exact hk hsz.symm

lemma boolClass_egf : boolClass.egf = PowerSeries.C (2 : ℚ) * PowerSeries.X := by
  ext n
  rw [CombinatorialClass.coeff_egf]
  rw [show PowerSeries.X = (PowerSeries.X : PowerSeries ℚ) ^ 1 by simp]
  rw [PowerSeries.coeff_C_mul_X_pow]
  by_cases hn : n = 1
  · subst n
    rw [boolClass.count_one]
    norm_num
  · rw [boolClass_count_eq_zero_of_ne_one hn]
    simp [hn]

lemma coeff_C_two_mul_X_pow (k n : ℕ) :
    coeff n ((PowerSeries.C (2 : ℚ) * PowerSeries.X) ^ k) =
      if n = k then (2 ^ k : ℚ) else 0 := by
  have hbase : PowerSeries.C (2 : ℚ) * PowerSeries.X = PowerSeries.monomial 1 (2 : ℚ) := by
    ext m
    rw [show PowerSeries.X = (PowerSeries.X : PowerSeries ℚ) ^ 1 by simp]
    rw [PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_monomial]
  rw [hbase]
  have hpow : (PowerSeries.monomial 1 (2 : ℚ)) ^ k =
      PowerSeries.monomial k (2 ^ k : ℚ) := by
    induction k with
    | zero => simp [PowerSeries.monomial_zero_eq_C_apply]
    | succ k ih =>
      rw [pow_succ, ih, PowerSeries.monomial_mul_monomial]
      congr
      rw [pow_succ]
  rw [hpow, PowerSeries.coeff_monomial]

/-- `(labelPow boolClass k).count n = 2^k · k!` when `n = k`, else 0.
    A labelled k-tuple of binary atoms has `2^k` label choices and `k!` orderings. -/
theorem labelPow_boolClass_count (k n : ℕ) :
    (CombinatorialClass.labelPow boolClass k).count n =
      if n = k then 2 ^ k * k.factorial else 0 := by
  have hcoeff := CombinatorialClass.labelPow_count_div_factorial_eq_coeff_pow boolClass k n
  rw [boolClass_egf, coeff_C_two_mul_X_pow] at hcoeff
  by_cases hnk : n = k
  · subst n
    simp only [if_true] at hcoeff ⊢
    field_simp [Nat.cast_ne_zero.mpr k.factorial_pos.ne'] at hcoeff
    rw [Nat.mul_comm]
    exact_mod_cast hcoeff
  · simp only [if_false, hnk] at hcoeff ⊢
    field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne'] at hcoeff
    rw [mul_zero] at hcoeff
    exact Nat.cast_eq_zero.mp hcoeff

/-- `labelSetCount boolClass n = 2^n`. -/
theorem labelSetCount_boolClass (n : ℕ) :
    CombinatorialClass.labelSetCount boolClass n = 2 ^ n := by
  rw [CombinatorialClass.labelSetCount]
  rw [Finset.sum_eq_single n]
  · rw [labelPow_boolClass_count n n, if_pos rfl]
    rw [Nat.cast_mul]
    field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne']
    norm_num
  · intro k _ hkn
    rw [labelPow_boolClass_count k n, if_neg (Ne.symm hkn)]
    simp
  · intro hn
    exfalso
    exact hn (Finset.mem_range.mpr (Nat.lt_succ_self n))

/-- Direct coefficient form: [zⁿ] stringClass.ogfZ = 2^n. -/
theorem stringClass_ogfZ_coeff (n : ℕ) :
    PowerSeries.coeff n (ogfZ stringClass) = (2 ^ n : ℤ) := by
  unfold ogfZ
  rw [PowerSeries.coeff_map, coeff_ogf, stringClass_count_eq_pow]
  push_cast
  rfl
