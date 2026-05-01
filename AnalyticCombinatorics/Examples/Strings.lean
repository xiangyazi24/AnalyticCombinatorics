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
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Count
import Mathlib.Algebra.BigOperators.Fin
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
import AnalyticCombinatorics.PartA.Ch3.Parameters

set_option linter.style.show false

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

example (n : ℕ) :
    stringClass.egf.coeff n = (2 ^ n : ℚ) / n.factorial := by
  rw [CombinatorialClass.coeff_egf, stringClass_count_eq_pow]
  push_cast
  rfl

/-- The disjoint sum of two stringClasses doubles the count: 2 · 2^n = 2^(n+1). -/
example (n : ℕ) :
    (stringClass.disjSum stringClass).count n = 2 ^ (n + 1) := by
  rw [CombinatorialClass.disjSum_count, stringClass_count_eq_pow]
  rw [pow_succ]
  ring

/-- The cartesian product convolution:
    `∑ p ∈ antidiag n, 2^p.1 · 2^p.2 = (n+1) · 2^n`. -/
theorem stringClass_cartProd_count (n : ℕ) :
    (stringClass.cartProd stringClass).count n = (n + 1) * 2 ^ n := by
  rw [CombinatorialClass.cartProd_count]
  rw [show ∑ p ∈ Finset.antidiagonal n, stringClass.count p.1 * stringClass.count p.2
        = ∑ _p ∈ Finset.antidiagonal n, 2 ^ n from ?_]
  · simp [Finset.sum_const, Finset.Nat.card_antidiagonal]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    rw [stringClass_count_eq_pow, stringClass_count_eq_pow]
    rw [← pow_add, hp]

/-! ## Parameter: number of ones in a binary string -/

/-- Parameter: number of `true`s in a binary string. -/
def numOnes : Parameter stringClass := fun (xs : List Bool) => xs.count true

/-- Parameter: number of `true`s in a binary string. -/
def stringNumTrue : Parameter stringClass := numOnes

private lemma bool_foldr_one_eq_length (xs : List Bool) :
    xs.foldr (fun _ acc => 1 + acc) 0 = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih =>
      simp only [List.foldr_cons, List.length_cons]
      rw [ih]
      omega

private lemma stringClass_size_eq_length (xs : List Bool) :
    stringClass.size xs = xs.length := by
  change xs.foldr (fun b acc => boolClass.size b + acc) 0 = xs.length
  simpa [boolClass] using bool_foldr_one_eq_length xs

private lemma list_countP_congr {α : Type*} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.countP p = l.countP q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp [List.countP_cons, h.1, ih h.2]

private lemma count_true_ofFn {n : ℕ} (f : Fin n → Bool) :
    (List.ofFn f).count true = Fin.countP f := by
  rw [Fin.countP_eq_countP_map_finRange]
  rw [List.ofFn_eq_map]
  simp only [List.count, List.countP_map]
  apply list_countP_congr
  intro i _hi
  cases hfi : f i <;> simp [hfi]

private lemma fin_countP_eq_card_filter {n : ℕ} (f : Fin n → Bool) :
    Fin.countP f = ((Finset.univ : Finset (Fin n)).filter (fun i => f i = true)).card := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.countP_succ]
      rw [Finset.card_filter]
      rw [Fin.sum_univ_succ]
      rw [← Finset.card_filter]
      rw [ih (fun i => f i.succ)]
      cases h0 : f 0 <;> simp

private lemma count_true_subsetString {n : ℕ} (s : Finset (Fin n)) :
    (List.ofFn (fun i : Fin n => decide (i ∈ s) : Fin n → Bool)).count true = s.card := by
  rw [count_true_ofFn]
  rw [fin_countP_eq_card_filter]
  rw [show ((Finset.univ : Finset (Fin n)).filter
      (fun i => (decide (i ∈ s) : Bool) = true)) = s by
    ext i
    by_cases hi : i ∈ s <;> simp [hi]]

private lemma subsetString_injective {n : ℕ} :
    Function.Injective (fun s : Finset (Fin n) =>
      List.ofFn (fun i : Fin n => decide (i ∈ s) : Fin n → Bool)) := by
  intro s t hst
  rw [List.ofFn_inj] at hst
  ext i
  have h := congrFun hst i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;> simp [his, hit] at h ⊢

/-- Joint count is the binomial coefficient: C(n, k). -/
theorem stringClass_jointCount_numOnes (n k : ℕ) :
    stringClass.jointCount numOnes n k = n.choose k := by
  classical
  let source : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard k
  let target : Finset (List Bool) := (stringClass.level n).filter (fun xs => numOnes xs = k)
  have hcard : source.card = target.card := by
    apply Finset.card_bij
      (fun s _hs => List.ofFn (fun i : Fin n => decide (i ∈ s) : Fin n → Bool))
    · intro s hs
      have hs_card : s.card = k := (Finset.mem_powersetCard.mp hs).2
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · apply (CombinatorialClass.level_mem_iff (C := stringClass) _).mpr
        rw [stringClass_size_eq_length, List.length_ofFn]
      · simp [numOnes, count_true_subsetString, hs_card]
    · intro s₁ _hs₁ s₂ _hs₂ h
      exact subsetString_injective h
    · intro xs hxs
      have hx_level : xs ∈ stringClass.level n := (Finset.mem_filter.mp hxs).1
      have hx_param : numOnes xs = k := (Finset.mem_filter.mp hxs).2
      have hx_size : stringClass.size xs = n :=
        (CombinatorialClass.level_mem_iff (C := stringClass) xs).mp hx_level
      have hlen : xs.length = n := by
        rw [← stringClass_size_eq_length xs]
        exact hx_size
      clear hx_size hx_level hxs
      subst n
      let s : Finset (Fin xs.length) :=
        (Finset.univ : Finset (Fin xs.length)).filter (fun i => xs.get i = true)
      refine ⟨s, ?_, ?_⟩
      · apply Finset.mem_powersetCard.mpr
        refine ⟨Finset.subset_univ _, ?_⟩
        have hcount : xs.count true = s.card := by
          have h1 := count_true_ofFn (fun i : Fin xs.length => xs.get i)
          rw [fin_countP_eq_card_filter] at h1
          simpa [s, List.ofFn_get xs] using h1
        rw [← hx_param]
        exact hcount.symm
      · have hlist :
            (List.ofFn fun i : Fin xs.length => decide (i ∈ s)) =
              List.ofFn (fun i : Fin xs.length => xs.get i) := by
          rw [List.ofFn_inj]
          funext i
          by_cases _h : xs.get i = true <;> simp [s]
        exact hlist.trans (List.ofFn_get xs)
  rw [CombinatorialClass.jointCount]
  change target.card = n.choose k
  rw [← hcard]
  simp [source]

/-- Sanity at small sizes:
    n = 0: 1 string with 0 ones.
    n = 1: 1 string with 0 ones (false), 1 string with 1 one (true).
    n = 2: 1 string with 0 ones (ff), 2 with 1 one (ft, tf), 1 with 2 ones (tt). -/
example : stringClass.jointCount numOnes 0 0 = 1 := by
  rw [stringClass_jointCount_numOnes]
  rfl

example : stringClass.jointCount numOnes 1 0 = 1 := by
  rw [stringClass_jointCount_numOnes]
  rfl

example : stringClass.jointCount numOnes 1 1 = 1 := by
  rw [stringClass_jointCount_numOnes]
  rfl

example : stringClass.jointCount numOnes 2 0 = 1 := by
  rw [stringClass_jointCount_numOnes]
  rfl

example : stringClass.jointCount numOnes 2 1 = 2 := by
  rw [stringClass_jointCount_numOnes]
  rfl

example : stringClass.jointCount numOnes 2 2 = 1 := by
  rw [stringClass_jointCount_numOnes]
  rfl

/-! Sanity checks for the requested `stringNumTrue` parameter. -/

example : stringClass.jointCount stringNumTrue 3 0 = 1 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 3 1 = 3 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 3 2 = 3 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 3 3 = 1 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 4 2 = 6 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 5 0 = 1 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 5 1 = 5 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 5 2 = 10 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 5 3 = 10 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 5 4 = 5 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 5 5 = 1 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 6 0 = 1 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 6 1 = 6 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 6 2 = 15 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 6 3 = 20 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 6 4 = 15 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 6 5 = 6 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example : stringClass.jointCount stringNumTrue 6 6 = 1 := by
  rw [show stringNumTrue = numOnes by rfl, stringClass_jointCount_numOnes]
  decide

example :
    ∑ k ∈ (stringClass.level 4).image stringNumTrue,
      stringClass.jointCount stringNumTrue 4 k = 16 := by
  rw [CombinatorialClass.jointCount_sum_eq_count]
  rw [stringClass_count_eq_pow]
  norm_num

example : stringClass.count 6 = 64 := stringClass_count_eq_pow 6
example : stringClass.count 7 = 128 := stringClass_count_eq_pow 7
example : stringClass.count 8 = 256 := stringClass_count_eq_pow 8
example : stringClass.count 9 = 512 := stringClass_count_eq_pow 9
example : stringClass.count 10 = 1024 := stringClass_count_eq_pow 10

/-- The stringClass.egf coefficient at 0 is 1. -/
example : stringClass.egf.coeff 0 = 1 := by
  rw [CombinatorialClass.coeff_egf, stringClass_count_eq_pow]
  simp

/-- The stringClass.ogf at coeff 0 is 1. -/
example : stringClass.ogf.coeff 0 = 1 := by
  rw [coeff_ogf, stringClass_count_eq_pow]
  simp

example : (stringClass.disjSum stringClass).count 0 = 2 := by
  rw [CombinatorialClass.disjSum_count, stringClass_count_eq_pow]
  decide

example : (stringClass.disjSum stringClass).count 3 = 16 := by
  rw [CombinatorialClass.disjSum_count, stringClass_count_eq_pow]
  decide

/-! ## Ternary strings -/

/-- The 3-letter alphabet: every `Fin 3` is an atom of size 1. -/
def ternaryClass : CombinatorialClass where
  Obj := Fin 3
  size _ := 1
  finite_level _ := Set.finite_univ.subset (Set.subset_univ _)

-- Bridge instances so that `Finset ternaryClass.Obj` is well-behaved.
instance : DecidableEq ternaryClass.Obj := inferInstanceAs (DecidableEq (Fin 3))
instance : Fintype ternaryClass.Obj := inferInstanceAs (Fintype (Fin 3))

namespace ternaryClass

/-- All `Fin 3` elements have size 1, so `ternaryClass.count 0 = 0`. -/
lemma count_zero : ternaryClass.count 0 = 0 := by
  simp only [count]
  rw [Finset.card_eq_zero]
  ext a
  simp only [Finset.notMem_empty, iff_false]
  intro ha
  have hsz : ternaryClass.size a = 0 :=
    (ternaryClass.finite_level 0).mem_toFinset.mp ha
  exact absurd hsz (by show (1 : ℕ) ≠ 0; omega)

/-- There are exactly 3 letters of size 1. -/
lemma count_one : ternaryClass.count 1 = 3 := by
  show (ternaryClass.level 1).card = 3
  have h_level : ternaryClass.level 1 = (Finset.univ : Finset ternaryClass.Obj) := by
    ext a
    constructor
    · intro _
      exact Finset.mem_univ a
    · intro _
      rw [CombinatorialClass.level_mem_iff]
      rfl
  rw [h_level]
  exact Fintype.card_fin 3

/-- For `k ≠ 1`, no letter has size `k`. -/
private lemma count_eq_zero_of_ne_one {k : ℕ} (hk : k ≠ 1) :
    ternaryClass.count k = 0 := by
  simp only [count]
  rw [Finset.card_eq_zero]
  ext a
  simp only [Finset.notMem_empty, iff_false]
  intro ha
  have hsz : ternaryClass.size a = k :=
    (ternaryClass.finite_level k).mem_toFinset.mp ha
  exact hk hsz.symm

end ternaryClass

/-- The class of ternary strings: finite sequences over a 3-letter alphabet. -/
noncomputable def ternaryStringClass : CombinatorialClass :=
  seqClass ternaryClass ternaryClass.count_zero

/-- A ternary string of length n is a `List (Fin 3)` whose total size is n.
    There are 3ⁿ such strings. -/
theorem ternaryStringClass_count_eq_pow (n : ℕ) :
    ternaryStringClass.count n = 3 ^ n := by
  induction n with
  | zero =>
    show (seqClass ternaryClass _).count 0 = 1
    rw [seqClass.count_zero]
  | succ m ih =>
    show (seqClass ternaryClass _).count (m + 1) = 3 ^ (m + 1)
    rw [seqClass.count_succ]
    rw [Finset.sum_eq_single (1, m)]
    · show ternaryClass.count 1 * (seqClass ternaryClass _).count m = 3 ^ (m + 1)
      rw [ternaryClass.count_one]
      change 3 * ternaryStringClass.count m = 3 ^ (m + 1)
      rw [ih, pow_succ]
      ring
    · rintro ⟨k, j⟩ hkj hne
      by_cases hk : k = 1
      · exfalso
        subst hk
        rw [Finset.mem_antidiagonal] at hkj
        apply hne
        congr
        omega
      · rw [ternaryClass.count_eq_zero_of_ne_one hk, zero_mul]
    · intro h
      exfalso
      apply h
      rw [Finset.mem_antidiagonal]
      omega

/-! Sanity checks: 3⁰ through 3⁶ ternary strings. -/
example : ternaryStringClass.count 0 = 1 := ternaryStringClass_count_eq_pow 0
example : ternaryStringClass.count 1 = 3 := ternaryStringClass_count_eq_pow 1
example : ternaryStringClass.count 2 = 9 := ternaryStringClass_count_eq_pow 2
example : ternaryStringClass.count 3 = 27 := ternaryStringClass_count_eq_pow 3
example : ternaryStringClass.count 4 = 81 := ternaryStringClass_count_eq_pow 4
example : ternaryStringClass.count 5 = 243 := ternaryStringClass_count_eq_pow 5
example : ternaryStringClass.count 6 = 729 := ternaryStringClass_count_eq_pow 6
