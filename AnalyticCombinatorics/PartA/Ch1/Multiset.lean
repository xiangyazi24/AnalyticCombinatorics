/-
  Chapter I § I.2 — Multisets (MSET construction)

  MSET(B) is the class of all finite multisets of objects from B.
  If B has no size-zero objects, each level is finite.

  Reference: F&S Proposition I.2.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Set.Finite.List
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

set_option linter.style.show false
set_option linter.style.multiGoal false
set_option linter.style.nativeDecide false

open PowerSeries CombinatorialClass

namespace CombinatorialClass

private lemma mem_level_iff' (C : CombinatorialClass) (m : ℕ) (x : C.Obj) :
    x ∈ C.level m ↔ C.size x = m := by
  change x ∈ (C.finite_level m).toFinset ↔ C.size x = m
  exact (C.finite_level m).mem_toFinset.trans (by simp)

private lemma size_pos {B : CombinatorialClass} (h : B.count 0 = 0) (b : B.Obj) :
    1 ≤ B.size b := by
  rcases Nat.eq_zero_or_pos (B.size b) with h0 | hp
  · exfalso
    have hcard : 0 < (B.level 0).card :=
      Finset.card_pos.mpr ⟨b, (mem_level_iff' B 0 b).mpr h0⟩
    simp only [count] at h
    omega
  · omega

private lemma mset_card_le_size_sum {B : CombinatorialClass} (h : B.count 0 = 0)
    (s : Multiset B.Obj) : s.card ≤ (s.map B.size).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
      rw [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
      have hb := size_pos h b
      omega

private lemma mset_mem_size_le_sum {B : CombinatorialClass} {s : Multiset B.Obj} {b : B.Obj}
    (hb : b ∈ s) : B.size b ≤ (s.map B.size).sum :=
  Multiset.le_sum_of_mem (Multiset.mem_map_of_mem B.size hb)

/-- MSET(B): finite multisets of objects from B, including the empty multiset.
    Requires B(0) = 0 to ensure level sets are finite. -/
def msetClass (B : CombinatorialClass) (hB : B.count 0 = 0) : CombinatorialClass where
  Obj := Multiset B.Obj
  size := fun s => (s.map B.size).sum
  finite_level n := by
    let S : Set B.Obj := ⋃ k : Fin (n + 1), ↑(B.level k.val)
    have hSfin : S.Finite := Set.finite_iUnion (fun k => (B.level k.val).finite_toSet)
    have hmemS : ∀ s : Multiset B.Obj, (s.map B.size).sum = n →
        ∀ b ∈ s, b ∈ S := by
      intro s hs b hb
      simp only [S, Set.mem_iUnion, Finset.mem_coe]
      exact ⟨⟨B.size b, by
          have hle := mset_mem_size_le_sum (B := B) (s := s) hb
          omega⟩, (mem_level_iff' B _ b).mpr rfl⟩
    haveI : Finite {x : B.Obj // x ∈ S} := hSfin.to_subtype
    apply Set.Finite.subset
      ((List.finite_length_le {x : B.Obj // x ∈ S} n).image
        (fun xs : List {x : B.Obj // x ∈ S} =>
          ((xs.map Subtype.val : List B.Obj) : Multiset B.Obj)))
    intro s hs
    simp only [Set.mem_image, Set.mem_setOf_eq]
    let xs : List {x : B.Obj // x ∈ S} :=
      s.toList.attachWith (· ∈ S) (by
        intro b hb
        exact hmemS s hs b ((Multiset.mem_toList).mp hb))
    refine ⟨xs, ?_, ?_⟩
    · change xs.length ≤ n
      rw [List.length_attachWith, Multiset.length_toList]
      have hle := mset_card_le_size_sum hB s
      rw [hs] at hle
      exact hle
    · change ((xs.map Subtype.val : List B.Obj) : Multiset B.Obj) = s
      dsimp [xs]
      rw [List.attachWith_map_subtype_val]
      exact Multiset.coe_toList s

private lemma mset_eq_zero_of_size_zero {B : CombinatorialClass} (h : B.count 0 = 0)
    {s : Multiset B.Obj} (hs : (s.map B.size).sum = 0) : s = 0 := by
  have hle := mset_card_le_size_sum h s
  rw [hs] at hle
  exact Multiset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hle)

/-- The empty multiset is the unique MSET object of size 0. -/
theorem msetClass_count_zero (B : CombinatorialClass) (h : B.count 0 = 0) :
    (msetClass B h).count 0 = 1 := by
  simp only [count]
  rw [Finset.card_eq_one]
  refine ⟨(0 : Multiset B.Obj), ?_⟩
  ext s
  simp only [Finset.mem_singleton]
  rw [mem_level_iff' (msetClass B h) 0 s]
  constructor
  · intro hs
    exact mset_eq_zero_of_size_zero h hs
  · rintro rfl
    show (Multiset.map B.size (0 : Multiset B.Obj)).sum = 0
    simp

private lemma mset_exists_singleton_of_size_one {B : CombinatorialClass} (h : B.count 0 = 0)
    {s : Multiset B.Obj} (hs : (s.map B.size).sum = 1) :
    ∃ b : B.Obj, s = {b} ∧ B.size b = 1 := by
  have hcard_le := mset_card_le_size_sum h s
  rw [hs] at hcard_le
  have hne : s ≠ 0 := by
    intro hz
    rw [hz] at hs
    simp at hs
  have hcard_pos : 0 < s.card := Multiset.card_pos.mpr hne
  have hcard : s.card = 1 := by omega
  rcases Multiset.card_eq_one.mp hcard with ⟨b, rfl⟩
  refine ⟨b, rfl, ?_⟩
  simpa using hs

/-- MSET objects of size 1 are exactly singleton multisets of size-1 objects. -/
theorem msetClass_count_one (B : CombinatorialClass) (h : B.count 0 = 0) :
    (msetClass B h).count 1 = B.count 1 := by
  simp only [count]
  refine Finset.card_bij'
    (fun s hs => Classical.choose
      (mset_exists_singleton_of_size_one h
        ((mem_level_iff' (msetClass B h) 1 s).mp hs)))
    (fun b _ => ({b} : Multiset B.Obj)) ?_ ?_ ?_ ?_
  · intro s hs
    have hspec := Classical.choose_spec
      (mset_exists_singleton_of_size_one h
        ((mem_level_iff' (msetClass B h) 1 s).mp hs))
    exact (mem_level_iff' B 1 _).mpr hspec.2
  · intro b hb
    have hbsz : B.size b = 1 := (mem_level_iff' B 1 b).mp hb
    apply (mem_level_iff' (msetClass B h) 1 ({b} : Multiset B.Obj)).mpr
    simp [msetClass, hbsz]
  · intro s hs
    have hspec := Classical.choose_spec
      (mset_exists_singleton_of_size_one h
        ((mem_level_iff' (msetClass B h) 1 s).mp hs))
    exact hspec.1.symm
  · intro b hb
    have hbsz : B.size b = 1 := (mem_level_iff' B 1 b).mp hb
    have hspec := Classical.choose_spec
      (mset_exists_singleton_of_size_one h
        (s := ({b} : Multiset B.Obj)) (by simp [hbsz]))
    have hmem : b ∈ ({Classical.choose
        (mset_exists_singleton_of_size_one h
          (s := ({b} : Multiset B.Obj)) (by simp [hbsz]))} : Multiset B.Obj) := by
      rw [← hspec.1]
      simp
    exact (Multiset.mem_singleton.mp hmem).symm

/-!
The task request says that `MSET(Atom)` gives integer partitions.  In this
repository `Atom` is one size-1 object, so `MSET(Atom)` has one object at
each size.  Integer partitions are instead `MSET` of the class with one
object at each positive size.
-/

private theorem Atom_count_zero : Atom.count 0 = 0 := by
  rw [show Atom = atomOfSize 1 from rfl, atomOfSize_count]
  simp

example : (msetClass Atom Atom_count_zero).count 0 = 1 :=
  msetClass_count_zero Atom Atom_count_zero

example : (msetClass Atom Atom_count_zero).count 1 = 1 := by
  rw [msetClass_count_one, show Atom = atomOfSize 1 from rfl, atomOfSize_count]
  simp

/-- One object at each positive size.  Its MSET construction is the class of
integer partitions. -/
private def positiveSizeClass : CombinatorialClass where
  Obj := {n : ℕ // 0 < n}
  size := fun n => n.1
  finite_level n := by
    rcases n with _ | n
    · apply Set.Finite.subset (Set.finite_empty)
      intro x hx
      simp only [Set.mem_empty_iff_false]
      exact (Nat.ne_of_gt x.2) hx
    · apply Set.Finite.subset
        (Set.finite_singleton (⟨n + 1, Nat.succ_pos n⟩ : {m : ℕ // 0 < m}))
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      ext
      exact hx

private lemma positiveSizeClass_count_zero : positiveSizeClass.count 0 = 0 := by
  simp only [count]
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  have hsz : positiveSizeClass.size x = 0 :=
    (mem_level_iff' positiveSizeClass 0 x).mp hx
  exact (Nat.ne_of_gt x.2) hsz

private noncomputable def positiveMSetToPartition {n : ℕ}
    (s : (msetClass positiveSizeClass positiveSizeClass_count_zero).Obj)
    (hs : s ∈ (msetClass positiveSizeClass positiveSizeClass_count_zero).level n) :
    Nat.Partition n where
  parts := s.map Subtype.val
  parts_pos := by
    intro i hi
    rcases Multiset.mem_map.mp hi with ⟨x, -, rfl⟩
    exact x.2
  parts_sum := by
    exact (mem_level_iff' (msetClass positiveSizeClass positiveSizeClass_count_zero) n s).mp hs

private def partitionToPositiveMSet {n : ℕ} (p : Nat.Partition n) :
    (msetClass positiveSizeClass positiveSizeClass_count_zero).Obj :=
  p.parts.attach.map (fun i => (⟨i.1, p.parts_pos i.2⟩ : positiveSizeClass.Obj))

private lemma map_partitionToPositiveMSet_parts {n : ℕ} (p : Nat.Partition n) :
    (partitionToPositiveMSet p).map Subtype.val = p.parts := by
  unfold partitionToPositiveMSet
  exact (Multiset.map_map Subtype.val
    (fun i => (⟨i.1, p.parts_pos i.2⟩ : positiveSizeClass.Obj)) p.parts.attach).trans (by
      change p.parts.attach.map (fun i => i.1) = p.parts
      exact Multiset.attach_map_val p.parts)

private theorem positiveMSet_count_eq_partition_card (n : ℕ) :
    (msetClass positiveSizeClass positiveSizeClass_count_zero).count n =
      Fintype.card (Nat.Partition n) := by
  simp only [count]
  change ((msetClass positiveSizeClass positiveSizeClass_count_zero).level n).card =
    (Finset.univ : Finset (Nat.Partition n)).card
  refine Finset.card_bij positiveMSetToPartition ?_ ?_ ?_
  · intro s hs
    exact Finset.mem_univ _
  · intro s hs t ht heq
    apply_fun Nat.Partition.parts at heq
    change s.map Subtype.val = t.map Subtype.val at heq
    exact Multiset.map_injective Subtype.val_injective heq
  · intro p hp
    refine ⟨partitionToPositiveMSet p, ?_, ?_⟩
    · apply (mem_level_iff' (msetClass positiveSizeClass positiveSizeClass_count_zero) n _).mpr
      change ((partitionToPositiveMSet p).map Subtype.val).sum = n
      rw [map_partitionToPositiveMSet_parts, p.parts_sum]
    · apply Nat.Partition.ext
      exact map_partitionToPositiveMSet_parts p

example : (msetClass positiveSizeClass positiveSizeClass_count_zero).count 0 = 1 := by
  rw [positiveMSet_count_eq_partition_card]
  native_decide

example : (msetClass positiveSizeClass positiveSizeClass_count_zero).count 1 = 1 := by
  rw [positiveMSet_count_eq_partition_card]
  native_decide

example : (msetClass positiveSizeClass positiveSizeClass_count_zero).count 2 = 2 := by
  rw [positiveMSet_count_eq_partition_card]
  native_decide

example : (msetClass positiveSizeClass positiveSizeClass_count_zero).count 3 = 3 := by
  rw [positiveMSet_count_eq_partition_card]
  native_decide

example : (msetClass positiveSizeClass positiveSizeClass_count_zero).count 4 = 5 := by
  rw [positiveMSet_count_eq_partition_card]
  native_decide

example : (msetClass positiveSizeClass positiveSizeClass_count_zero).count 5 = 7 := by
  rw [positiveMSet_count_eq_partition_card]
  native_decide

end CombinatorialClass
