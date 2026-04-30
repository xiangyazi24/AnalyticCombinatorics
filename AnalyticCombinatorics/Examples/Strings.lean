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
