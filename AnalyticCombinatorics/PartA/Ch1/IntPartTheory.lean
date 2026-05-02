/-
  Chapter I § I.3 — Integer partitions and the MSET/OGF framework.

  Integer partitions are multisets of positive sizes.  The full Euler product
  and pentagonal-number theorem are analytic identities; this file records the
  finite coefficient side needed for Chapter I sanity checks.
-/
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Multiset

set_option linter.style.show false
set_option linter.style.multiGoal false
set_option linter.style.nativeDecide false

open PowerSeries CombinatorialClass

namespace Nat.Partition

/-- The partition-counting function `p(n)`.  This Mathlib version provides a
`Fintype` for `Nat.Partition n`, but no named `count`, so we expose the local
name used below. -/
def count (n : ℕ) : ℕ :=
  (Finset.univ : Finset (Nat.Partition n)).card

end Nat.Partition

/-- One object of each positive size. -/
def positiveSizeClass : CombinatorialClass where
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

lemma positiveSizeClass_count_zero : positiveSizeClass.count 0 = 0 := by
  simp only [CombinatorialClass.count]
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  have hsz : positiveSizeClass.size x = 0 :=
    (CombinatorialClass.level_mem_iff (C := positiveSizeClass) (n := 0) x).mp hx
  exact (Nat.ne_of_gt x.2) hsz

/-- Integer partitions as `MSET` of the class with one object in each positive
size.  The corresponding OGF is Euler's product
`∏ k ≥ 1, 1 / (1 - z^k)` at the informal analytic level. -/
def intPartClass : CombinatorialClass :=
  CombinatorialClass.msetClass positiveSizeClass positiveSizeClass_count_zero

private def positiveMSetToPartition {n : ℕ} (s : intPartClass.Obj)
    (hs : s ∈ intPartClass.level n) : Nat.Partition n where
  parts := s.map Subtype.val
  parts_pos := by
    intro i hi
    rcases Multiset.mem_map.mp hi with ⟨x, -, rfl⟩
    exact x.2
  parts_sum := by
    exact (CombinatorialClass.level_mem_iff (C := intPartClass) (n := n) s).mp hs

private def partitionToPositiveMSet {n : ℕ} (p : Nat.Partition n) : intPartClass.Obj :=
  p.parts.attach.map (fun i => (⟨i.1, p.parts_pos i.2⟩ : positiveSizeClass.Obj))

private lemma map_partitionToPositiveMSet_parts {n : ℕ} (p : Nat.Partition n) :
    (partitionToPositiveMSet p).map Subtype.val = p.parts := by
  unfold partitionToPositiveMSet
  exact (Multiset.map_map Subtype.val
    (fun i => (⟨i.1, p.parts_pos i.2⟩ : positiveSizeClass.Obj)) p.parts.attach).trans (by
      change p.parts.attach.map (fun i => i.1) = p.parts
      exact Multiset.attach_map_val p.parts)

private theorem intPartClass_count_eq_partition_card (n : ℕ) :
    intPartClass.count n = (Finset.univ : Finset (Nat.Partition n)).card := by
  simp only [CombinatorialClass.count]
  refine Finset.card_bij positiveMSetToPartition ?_ ?_ ?_
  · intro s hs
    exact Finset.mem_univ _
  · intro s hs t ht heq
    apply_fun Nat.Partition.parts at heq
    change s.map Subtype.val = t.map Subtype.val at heq
    exact Multiset.map_injective Subtype.val_injective heq
  · intro p hp
    refine ⟨partitionToPositiveMSet p, ?_, ?_⟩
    · apply (CombinatorialClass.level_mem_iff (C := intPartClass) (n := n) _).mpr
      change ((partitionToPositiveMSet p).map Subtype.val).sum = n
      rw [map_partitionToPositiveMSet_parts, p.parts_sum]
    · apply Nat.Partition.ext
      exact map_partitionToPositiveMSet_parts p

/-- Coefficient/count form: `MSET` of one object in each positive size counts
integer partitions. -/
theorem intPartition_ogf_coeff (n : ℕ) :
    intPartClass.count n = Nat.Partition.count n := by
  rw [intPartClass_count_eq_partition_card, Nat.Partition.count]

/-- Number of partitions of `n` into odd parts. -/
def oddPartCount (n : ℕ) : ℕ :=
  (Nat.Partition.odds n).card

/-- Number of partitions of `n` into distinct parts. -/
def distinctPartCount (n : ℕ) : ℕ :=
  (Nat.Partition.distincts n).card

theorem oddPartCount_eq_distinctPartCount_0 : oddPartCount 0 = distinctPartCount 0 := by
  native_decide

theorem oddPartCount_eq_distinctPartCount_1 : oddPartCount 1 = distinctPartCount 1 := by
  native_decide

theorem oddPartCount_eq_distinctPartCount_2 : oddPartCount 2 = distinctPartCount 2 := by
  native_decide

theorem oddPartCount_eq_distinctPartCount_3 : oddPartCount 3 = distinctPartCount 3 := by
  native_decide

theorem oddPartCount_eq_distinctPartCount_4 : oddPartCount 4 = distinctPartCount 4 := by
  native_decide

theorem oddPartCount_eq_distinctPartCount_5 : oddPartCount 5 = distinctPartCount 5 := by
  native_decide

theorem oddPartCount_eq_distinctPartCount_6 : oddPartCount 6 = distinctPartCount 6 := by
  native_decide

theorem oddPartCount_eq_distinctPartCount_7 : oddPartCount 7 = distinctPartCount 7 := by
  native_decide

theorem oddPartCount_eq_distinctPartCount_8 : oddPartCount 8 = distinctPartCount 8 := by
  native_decide

theorem oddPartCount_eq_distinctPartCount_9 : oddPartCount 9 = distinctPartCount 9 := by
  native_decide

theorem oddPartCount_eq_distinctPartCount_10 : oddPartCount 10 = distinctPartCount 10 := by
  native_decide

/-- Generalized pentagonal number `k(3k-1)/2`, viewed as a natural number. -/
def pentagonal (k : ℤ) : ℕ :=
  (k * (3 * k - 1) / 2).toNat

private def eulerSign (k : ℕ) : ℤ :=
  if k % 2 = 1 then 1 else -1

private def partitionAt (n g : ℕ) : ℤ :=
  if g ≤ n then (Nat.Partition.count (n - g) : ℤ) else 0

/-- The finite Euler-pentagonal recurrence sum for `p(n)`. -/
def pentagonalRecurrenceSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if k = 0 then 0 else
    eulerSign k *
      (partitionAt n (pentagonal (k : ℤ)) + partitionAt n (pentagonal (-(k : ℤ))))

theorem partition_euler_recurrence_1 :
    (Nat.Partition.count 1 : ℤ) = pentagonalRecurrenceSum 1 := by
  native_decide

theorem partition_euler_recurrence_2 :
    (Nat.Partition.count 2 : ℤ) = pentagonalRecurrenceSum 2 := by
  native_decide

theorem partition_euler_recurrence_3 :
    (Nat.Partition.count 3 : ℤ) = pentagonalRecurrenceSum 3 := by
  native_decide

theorem partition_euler_recurrence_4 :
    (Nat.Partition.count 4 : ℤ) = pentagonalRecurrenceSum 4 := by
  native_decide

theorem partition_euler_recurrence_5 :
    (Nat.Partition.count 5 : ℤ) = pentagonalRecurrenceSum 5 := by
  native_decide

theorem partition_euler_recurrence_6 :
    (Nat.Partition.count 6 : ℤ) = pentagonalRecurrenceSum 6 := by
  native_decide

theorem partition_euler_recurrence_7 :
    (Nat.Partition.count 7 : ℤ) = pentagonalRecurrenceSum 7 := by
  native_decide

theorem partition_euler_recurrence_8 :
    (Nat.Partition.count 8 : ℤ) = pentagonalRecurrenceSum 8 := by
  native_decide

theorem partition_euler_recurrence_9 :
    (Nat.Partition.count 9 : ℤ) = pentagonalRecurrenceSum 9 := by
  native_decide

theorem partition_euler_recurrence_10 :
    (Nat.Partition.count 10 : ℤ) = pentagonalRecurrenceSum 10 := by
  native_decide

theorem partition_count_0 : Nat.Partition.count 0 = 1 := by
  native_decide

theorem partition_count_1 : Nat.Partition.count 1 = 1 := by
  native_decide

theorem partition_count_2 : Nat.Partition.count 2 = 2 := by
  native_decide

theorem partition_count_3 : Nat.Partition.count 3 = 3 := by
  native_decide

theorem partition_count_4 : Nat.Partition.count 4 = 5 := by
  native_decide

theorem partition_count_5 : Nat.Partition.count 5 = 7 := by
  native_decide

theorem partition_count_6 : Nat.Partition.count 6 = 11 := by
  native_decide

theorem partition_count_7 : Nat.Partition.count 7 = 15 := by
  native_decide

theorem partition_count_8 : Nat.Partition.count 8 = 22 := by
  native_decide

theorem partition_count_9 : Nat.Partition.count 9 = 30 := by
  native_decide

theorem partition_count_10 : Nat.Partition.count 10 = 42 := by
  native_decide
