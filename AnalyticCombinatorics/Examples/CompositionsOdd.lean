/-
  Analytic Combinatorics — Examples
  Compositions into odd parts

  A composition of n into odd parts is a sequence of positive odd integers
  summing to n.  The empty composition accounts for n = 0.

  The counts begin 1, 1, 1, 2, 3, 5, 8, ...
-/
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import Mathlib.Data.Nat.Fib.Basic

open CombinatorialClass Finset

/-- Positive odd integers as a combinatorial class: one object at each odd size. -/
def oddPartClass : CombinatorialClass where
  Obj := {n : ℕ // n % 2 = 1}
  size := fun n => n.1
  finite_level n := by
    by_cases h : n % 2 = 1
    · apply Set.Finite.subset (Set.finite_singleton (⟨n, h⟩ : {k : ℕ // k % 2 = 1}))
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨v, hv⟩ := x
      change v = n at hx
      subst hx
      exact Set.mem_singleton _
    · apply Set.Finite.subset Set.finite_empty
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨v, hv⟩ := x
      change v = n at hx
      subst hx
      exact (h hv).elim

namespace oddPartClass

/-- No odd part has size 0. -/
lemma count_zero : oddPartClass.count 0 = 0 := by
  change (oddPartClass.level 0).card = 0
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hsz : oddPartClass.size x = 0 :=
    (oddPartClass.finite_level 0).mem_toFinset.mp hx
  obtain ⟨v, hv⟩ := x
  change v = 0 at hsz
  subst hsz
  omega

/-- For each positive odd k, exactly one odd part has size k. -/
lemma count_odd {k : ℕ} (hk : k % 2 = 1) : oddPartClass.count k = 1 := by
  change (oddPartClass.level k).card = 1
  rw [Finset.card_eq_one]
  refine ⟨⟨k, hk⟩, ?_⟩
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hsz : oddPartClass.size x = k :=
      (oddPartClass.finite_level k).mem_toFinset.mp hx
    obtain ⟨v, hv⟩ := x
    change v = k at hsz
    subst hsz
    exact Finset.mem_singleton_self _
  · rw [Finset.mem_singleton] at hx
    subst hx
    exact (oddPartClass.finite_level k).mem_toFinset.mpr rfl

/-- Even sizes have no odd part. -/
lemma count_not_odd {k : ℕ} (hk : k % 2 ≠ 1) : oddPartClass.count k = 0 := by
  change (oddPartClass.level k).card = 0
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hsz : oddPartClass.size x = k :=
    (oddPartClass.finite_level k).mem_toFinset.mp hx
  obtain ⟨v, hv⟩ := x
  change v = k at hsz
  subst hsz
  exact (hk hv).elim

/-- Count is 1 at odd sizes and 0 at even sizes. -/
lemma count_eq (k : ℕ) : oddPartClass.count k = if k % 2 = 1 then 1 else 0 := by
  by_cases hk : k % 2 = 1
  · simp [hk, count_odd hk]
  · simp [hk, count_not_odd hk]

end oddPartClass

/-- The class of compositions into odd parts. -/
noncomputable def oddCompClass : CombinatorialClass :=
  seqClass oddPartClass oddPartClass.count_zero

/-- Empty composition is the unique composition of 0. -/
theorem oddCompClass_count_zero : oddCompClass.count 0 = 1 := by
  change (seqClass oddPartClass oddPartClass.count_zero).count 0 = 1
  rw [seqClass.count_zero]

/-- Recurrence: prepend the first odd part. -/
private lemma oddCompClass_count_succ (n : ℕ) :
    oddCompClass.count (n + 1) =
      ∑ p ∈ Finset.antidiagonal (n + 1),
        (if p.1 % 2 = 1 then oddCompClass.count p.2 else 0) := by
  unfold oddCompClass
  rw [seqClass.count_succ]
  apply Finset.sum_congr rfl
  intro p hp
  rw [oddPartClass.count_eq]
  by_cases hpodd : p.1 % 2 = 1
  · simp [hpodd]
  · simp [hpodd]

private lemma oddCompClass_count_one : oddCompClass.count 1 = 1 := by
  calc
    oddCompClass.count 1
        = ∑ p ∈ Finset.antidiagonal 1,
            (if p.1 % 2 = 1 then oddCompClass.count p.2 else 0) := by
          simpa using oddCompClass_count_succ 0
    _ = 1 := by
          simp [Finset.antidiagonal, oddCompClass_count_zero]

private lemma oddCompClass_count_two : oddCompClass.count 2 = 1 := by
  calc
    oddCompClass.count 2
        = ∑ p ∈ Finset.antidiagonal 2,
            (if p.1 % 2 = 1 then oddCompClass.count p.2 else 0) := by
          simpa using oddCompClass_count_succ 1
    _ = 1 := by
          simp [Finset.antidiagonal, oddCompClass_count_one]

private lemma oddCompClass_count_three : oddCompClass.count 3 = 2 := by
  calc
    oddCompClass.count 3
        = ∑ p ∈ Finset.antidiagonal 3,
            (if p.1 % 2 = 1 then oddCompClass.count p.2 else 0) := by
          simpa using oddCompClass_count_succ 2
    _ = 2 := by
          simp [Finset.antidiagonal, oddCompClass_count_two, oddCompClass_count_zero]

private lemma oddCompClass_count_four : oddCompClass.count 4 = 3 := by
  calc
    oddCompClass.count 4
        = ∑ p ∈ Finset.antidiagonal 4,
            (if p.1 % 2 = 1 then oddCompClass.count p.2 else 0) := by
          simpa using oddCompClass_count_succ 3
    _ = 3 := by
          simp [Finset.antidiagonal, oddCompClass_count_three, oddCompClass_count_one]

private lemma oddCompClass_count_five : oddCompClass.count 5 = 5 := by
  calc
    oddCompClass.count 5
        = ∑ p ∈ Finset.antidiagonal 5,
            (if p.1 % 2 = 1 then oddCompClass.count p.2 else 0) := by
          simpa using oddCompClass_count_succ 4
    _ = 5 := by
          simp [Finset.antidiagonal, oddCompClass_count_four, oddCompClass_count_two,
            oddCompClass_count_zero]

private lemma oddCompClass_count_six : oddCompClass.count 6 = 8 := by
  calc
    oddCompClass.count 6
        = ∑ p ∈ Finset.antidiagonal 6,
            (if p.1 % 2 = 1 then oddCompClass.count p.2 else 0) := by
          simpa using oddCompClass_count_succ 5
    _ = 8 := by
          simp [Finset.antidiagonal, oddCompClass_count_five, oddCompClass_count_three,
            oddCompClass_count_one]

/-!
Sanity checks: compositions into odd parts have counts
`1, 1, 1, 2, 3, 5, 8, ...` for `n = 0, 1, 2, 3, 4, 5, 6, ...`.

TODO: prove the standard closed form `oddCompClass.count n = Nat.fib (n + 1)`,
with the convention `Nat.fib 1 = 1` for the empty composition at `n = 0`.
-/
example : oddCompClass.count 0 = 1 := oddCompClass_count_zero
example : oddCompClass.count 1 = 1 := oddCompClass_count_one
example : oddCompClass.count 2 = 1 := oddCompClass_count_two
example : oddCompClass.count 3 = 2 := oddCompClass_count_three
example : oddCompClass.count 4 = 3 := oddCompClass_count_four
example : oddCompClass.count 5 = 5 := oddCompClass_count_five
example : oddCompClass.count 6 = 8 := oddCompClass_count_six
