/-
  Analytic Combinatorics — Examples
  Integer partitions

  A partition of n is a multiset of positive integers summing to n, with
  order ignored.  Mathlib's `Nat.Partition n` already uses exactly this
  representation and provides finite levels.

  Reference: F&S Section I.3.
-/
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

set_option linter.style.show false
set_option linter.style.multiGoal false
set_option linter.style.nativeDecide false

open CombinatorialClass Finset

/-- The class of all integer partitions, indexed by the integer being partitioned. -/
def intPartitionClass : CombinatorialClass where
  Obj := Σ n : ℕ, Nat.Partition n
  size := fun p => p.1
  finite_level n := by
    classical
    refine Set.Finite.subset
      ((Finset.univ : Finset (Nat.Partition n)).image
        (fun p => (⟨n, p⟩ : Σ m : ℕ, Nat.Partition m))).finite_toSet ?_
    rintro ⟨m, p⟩ hp
    simp only [Set.mem_setOf_eq] at hp
    change m = n at hp
    subst m
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩

/-- Each size level of integer partitions is finite. -/
theorem intPartitionClass_finite_level (n : ℕ) :
    Set.Finite {p : intPartitionClass.Obj | intPartitionClass.size p = n} :=
  intPartitionClass.finite_level n

/-- The level count agrees with Mathlib's cardinality of `Nat.Partition n`. -/
theorem intPartitionClass_count_eq_card (n : ℕ) :
    intPartitionClass.count n = Fintype.card (Nat.Partition n) := by
  rw [CombinatorialClass.count]
  change (intPartitionClass.level n).card = (Finset.univ : Finset (Nat.Partition n)).card
  refine Finset.card_bij
    (fun x hx => by
      have hsz : intPartitionClass.size x = n :=
        (CombinatorialClass.level_mem_iff (C := intPartitionClass) x).mp hx
      cases x with
      | mk m p =>
          change m = n at hsz
          subst m
          exact p)
    ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_univ _
  · intro x hx y hy hxy
    have hxsz : intPartitionClass.size x = n :=
      (CombinatorialClass.level_mem_iff (C := intPartitionClass) x).mp hx
    have hysz : intPartitionClass.size y = n :=
      (CombinatorialClass.level_mem_iff (C := intPartitionClass) y).mp hy
    cases x with
    | mk mx px =>
      cases y with
      | mk my py =>
        change mx = n at hxsz
        change my = n at hysz
        subst mx
        subst my
        change px = py at hxy
        subst hxy
        rfl
  · intro p hp
    refine ⟨(⟨n, p⟩ : intPartitionClass.Obj), ?_, ?_⟩
    · exact (CombinatorialClass.level_mem_iff (C := intPartitionClass) _).mpr rfl
    · simp

/-!
Sanity checks: partition numbers p(n) for n = 0, ..., 6 are
1, 1, 2, 3, 5, 7, 11.
-/

example : intPartitionClass.count 0 = 1 := by
  rw [intPartitionClass_count_eq_card]
  native_decide

example : intPartitionClass.count 1 = 1 := by
  rw [intPartitionClass_count_eq_card]
  native_decide

example : intPartitionClass.count 2 = 2 := by
  rw [intPartitionClass_count_eq_card]
  native_decide

example : intPartitionClass.count 3 = 3 := by
  rw [intPartitionClass_count_eq_card]
  native_decide

example : intPartitionClass.count 4 = 5 := by
  rw [intPartitionClass_count_eq_card]
  native_decide

example : intPartitionClass.count 5 = 7 := by
  rw [intPartitionClass_count_eq_card]
  native_decide

example : intPartitionClass.count 6 = 11 := by
  rw [intPartitionClass_count_eq_card]
  native_decide

-- TODO: State the F&S OGF identity in project notation:
--   intPartitionClass.ogf = ∏_{k ≥ 1} (1 - z^k)⁻¹.
-- Mathlib's `Nat.Partition.genFun` already contains the corresponding product
-- theorem for weighted partition generating functions; bridging it to this
-- `CombinatorialClass.ogf` is a separate task.
