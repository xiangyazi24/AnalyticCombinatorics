/-
  Analytic Combinatorics — Examples
  Compositions into even parts

  A composition of n into even parts is a sequence of positive even integers
  summing to n. The empty composition accounts for n = 0.

  The counts begin 1, 0, 1, 0, 2, 0, 4, 0, 8, 0, 16, ...
-/
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences

set_option linter.style.nativeDecide false

open CombinatorialClass Finset

/-- Positive even integers as a combinatorial class: one object at each positive even size. -/
def evenPartClass : CombinatorialClass where
  Obj := {n : ℕ // n % 2 = 0 ∧ 0 < n}
  size := fun n => n.1
  finite_level n := by
    by_cases h : n % 2 = 0 ∧ 0 < n
    · apply Set.Finite.subset
        (Set.finite_singleton (⟨n, h⟩ : {k : ℕ // k % 2 = 0 ∧ 0 < k}))
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

namespace evenPartClass

/-- No positive even part has size 0. -/
lemma count_zero : evenPartClass.count 0 = 0 := by
  change (evenPartClass.level 0).card = 0
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hsz : evenPartClass.size x = 0 :=
    (evenPartClass.finite_level 0).mem_toFinset.mp hx
  obtain ⟨v, hv⟩ := x
  change v = 0 at hsz
  subst hsz
  omega

/-- For each positive even k, exactly one even part has size k. -/
lemma count_even_pos {k : ℕ} (hk : k % 2 = 0 ∧ 0 < k) : evenPartClass.count k = 1 := by
  change (evenPartClass.level k).card = 1
  rw [Finset.card_eq_one]
  refine ⟨⟨k, hk⟩, ?_⟩
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hsz : evenPartClass.size x = k :=
      (evenPartClass.finite_level k).mem_toFinset.mp hx
    obtain ⟨v, hv⟩ := x
    change v = k at hsz
    subst hsz
    exact Finset.mem_singleton_self _
  · rw [Finset.mem_singleton] at hx
    subst hx
    exact (evenPartClass.finite_level k).mem_toFinset.mpr rfl

/-- Sizes that are not positive even integers have no even part. -/
lemma count_not_even_pos {k : ℕ} (hk : ¬ (k % 2 = 0 ∧ 0 < k)) :
    evenPartClass.count k = 0 := by
  change (evenPartClass.level k).card = 0
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hsz : evenPartClass.size x = k :=
    (evenPartClass.finite_level k).mem_toFinset.mp hx
  obtain ⟨v, hv⟩ := x
  change v = k at hsz
  subst hsz
  exact (hk hv).elim

/-- Count is 1 at positive even sizes and 0 otherwise. -/
lemma count_eq (k : ℕ) : evenPartClass.count k = if k % 2 = 0 ∧ 0 < k then 1 else 0 := by
  by_cases hk : k % 2 = 0 ∧ 0 < k
  · simp [hk, count_even_pos hk]
  · simp [hk, count_not_even_pos hk]

end evenPartClass

/-- The class of compositions into even parts. -/
noncomputable def evenCompClass : CombinatorialClass :=
  seqClass evenPartClass evenPartClass.count_zero

/-- Empty composition is the unique composition of 0. -/
theorem evenCompClass_count_zero : evenCompClass.count 0 = 1 := by
  change (seqClass evenPartClass evenPartClass.count_zero).count 0 = 1
  rw [seqClass.count_zero]

/-- Recurrence: prepend the first even part. -/
private lemma evenCompClass_count_succ (n : ℕ) :
    evenCompClass.count (n + 1) =
      ∑ p ∈ Finset.antidiagonal (n + 1),
        (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
  unfold evenCompClass
  rw [seqClass.count_succ]
  apply Finset.sum_congr rfl
  intro p hp
  rw [evenPartClass.count_eq]
  by_cases hp_even_pos : p.1 % 2 = 0 ∧ 0 < p.1
  · simp [hp_even_pos]
  · simp [hp_even_pos]

private lemma evenCompClass_count_one : evenCompClass.count 1 = 0 := by
  calc
    evenCompClass.count 1
        = ∑ p ∈ Finset.antidiagonal 1,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 0
    _ = 0 := by
          simp [Finset.antidiagonal]

private lemma evenCompClass_count_two : evenCompClass.count 2 = 1 := by
  calc
    evenCompClass.count 2
        = ∑ p ∈ Finset.antidiagonal 2,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 1
    _ = 1 := by
          simp [Finset.antidiagonal, evenCompClass_count_zero]

private lemma evenCompClass_count_three : evenCompClass.count 3 = 0 := by
  calc
    evenCompClass.count 3
        = ∑ p ∈ Finset.antidiagonal 3,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 2
    _ = 0 := by
          simp [Finset.antidiagonal, evenCompClass_count_one]

private lemma evenCompClass_count_four : evenCompClass.count 4 = 2 := by
  calc
    evenCompClass.count 4
        = ∑ p ∈ Finset.antidiagonal 4,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 3
    _ = 2 := by
          simp [Finset.antidiagonal, evenCompClass_count_two, evenCompClass_count_zero]

private lemma evenCompClass_count_five : evenCompClass.count 5 = 0 := by
  calc
    evenCompClass.count 5
        = ∑ p ∈ Finset.antidiagonal 5,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 4
    _ = 0 := by
          simp [Finset.antidiagonal, evenCompClass_count_three, evenCompClass_count_one]

private lemma evenCompClass_count_six : evenCompClass.count 6 = 4 := by
  calc
    evenCompClass.count 6
        = ∑ p ∈ Finset.antidiagonal 6,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 5
    _ = 4 := by
          simp [Finset.antidiagonal, evenCompClass_count_four, evenCompClass_count_two,
            evenCompClass_count_zero]

private lemma evenCompClass_count_seven : evenCompClass.count 7 = 0 := by
  calc
    evenCompClass.count 7
        = ∑ p ∈ Finset.antidiagonal 7,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 6
    _ = 0 := by
          simp [Finset.antidiagonal, evenCompClass_count_five, evenCompClass_count_three,
            evenCompClass_count_one]

private lemma evenCompClass_count_eight : evenCompClass.count 8 = 8 := by
  calc
    evenCompClass.count 8
        = ∑ p ∈ Finset.antidiagonal 8,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 7
    _ = 8 := by
          simp [Finset.antidiagonal, evenCompClass_count_six, evenCompClass_count_four,
            evenCompClass_count_two, evenCompClass_count_zero]

private lemma evenCompClass_count_nine : evenCompClass.count 9 = 0 := by
  calc
    evenCompClass.count 9
        = ∑ p ∈ Finset.antidiagonal 9,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 8
    _ = 0 := by
          simp [Finset.antidiagonal, evenCompClass_count_seven, evenCompClass_count_five,
            evenCompClass_count_three, evenCompClass_count_one]

private lemma evenCompClass_count_ten : evenCompClass.count 10 = 16 := by
  calc
    evenCompClass.count 10
        = ∑ p ∈ Finset.antidiagonal 10,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 9
    _ = 16 := by
          simp [Finset.antidiagonal, evenCompClass_count_eight, evenCompClass_count_six,
            evenCompClass_count_four, evenCompClass_count_two, evenCompClass_count_zero]

/-!
Sanity checks: compositions into even parts have counts
`1, 0, 1, 0, 2, 0, 4, 0, 8, 0, 16` for `n = 0, 1, ..., 10`.
-/
example : evenCompClass.count 0 = 1 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_zero]
  native_decide
example : evenCompClass.count 1 = 0 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_one]
  native_decide
example : evenCompClass.count 2 = 1 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_two]
  native_decide
example : evenCompClass.count 3 = 0 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_three]
  native_decide
example : evenCompClass.count 4 = 2 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_four]
  native_decide
example : evenCompClass.count 5 = 0 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_five]
  native_decide
example : evenCompClass.count 6 = 4 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_six]
  native_decide
example : evenCompClass.count 7 = 0 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_seven]
  native_decide
example : evenCompClass.count 8 = 8 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_eight]
  native_decide
example : evenCompClass.count 9 = 0 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_nine]
  native_decide
example : evenCompClass.count 10 = 16 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_ten]
  native_decide
