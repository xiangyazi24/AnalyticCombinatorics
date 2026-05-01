/-
  Analytic Combinatorics — Examples
  Compositions into even parts

  A composition of n into even parts is a sequence of positive even integers
  summing to n. The empty composition accounts for n = 0.

  The counts begin 1, 0, 1, 0, 2, 0, 4, 0, 8, 0, 16, ...
-/
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import AnalyticCombinatorics.Examples.Compositions

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

private lemma evenCompClass_count_eleven : evenCompClass.count 11 = 0 := by
  calc
    evenCompClass.count 11
        = ∑ p ∈ Finset.antidiagonal 11,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 10
    _ = 0 := by
          simp [Finset.antidiagonal, evenCompClass_count_nine, evenCompClass_count_seven,
            evenCompClass_count_five, evenCompClass_count_three, evenCompClass_count_one]

private lemma evenCompClass_count_twelve : evenCompClass.count 12 = 32 := by
  calc
    evenCompClass.count 12
        = ∑ p ∈ Finset.antidiagonal 12,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 11
    _ = 32 := by
          simp [Finset.antidiagonal, evenCompClass_count_ten, evenCompClass_count_eight,
            evenCompClass_count_six, evenCompClass_count_four, evenCompClass_count_two,
            evenCompClass_count_zero]

private lemma evenCompClass_count_thirteen : evenCompClass.count 13 = 0 := by
  calc
    evenCompClass.count 13
        = ∑ p ∈ Finset.antidiagonal 13,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 12
    _ = 0 := by
          simp [Finset.antidiagonal, evenCompClass_count_eleven, evenCompClass_count_nine,
            evenCompClass_count_seven, evenCompClass_count_five, evenCompClass_count_three,
            evenCompClass_count_one]

private lemma evenCompClass_count_fourteen : evenCompClass.count 14 = 64 := by
  calc
    evenCompClass.count 14
        = ∑ p ∈ Finset.antidiagonal 14,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 13
    _ = 64 := by
          simp [Finset.antidiagonal, evenCompClass_count_twelve, evenCompClass_count_ten,
            evenCompClass_count_eight, evenCompClass_count_six, evenCompClass_count_four,
            evenCompClass_count_two, evenCompClass_count_zero]

private lemma evenCompClass_count_fifteen : evenCompClass.count 15 = 0 := by
  calc
    evenCompClass.count 15
        = ∑ p ∈ Finset.antidiagonal 15,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 14
    _ = 0 := by
          simp [Finset.antidiagonal, evenCompClass_count_thirteen, evenCompClass_count_eleven,
            evenCompClass_count_nine, evenCompClass_count_seven, evenCompClass_count_five,
            evenCompClass_count_three, evenCompClass_count_one]

private lemma evenCompClass_count_sixteen : evenCompClass.count 16 = 128 := by
  calc
    evenCompClass.count 16
        = ∑ p ∈ Finset.antidiagonal 16,
            (if p.1 % 2 = 0 ∧ 0 < p.1 then evenCompClass.count p.2 else 0) := by
          simpa using evenCompClass_count_succ 15
    _ = 128 := by
          simp [Finset.antidiagonal, evenCompClass_count_fourteen, evenCompClass_count_twelve,
            evenCompClass_count_ten, evenCompClass_count_eight, evenCompClass_count_six,
            evenCompClass_count_four, evenCompClass_count_two, evenCompClass_count_zero]

/-!
Sanity checks: compositions into even parts have counts
`1, 0, 1, 0, 2, 0, 4, 0, 8, 0, 16, 0, 32, 0, 64, 0, 128`
for `n = 0, 1, ..., 16`.
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
example : evenCompClass.count 11 = 0 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_eleven]
  native_decide
example : evenCompClass.count 12 = 32 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_twelve]
  native_decide
example : evenCompClass.count 13 = 0 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_thirteen]
  native_decide
example : evenCompClass.count 14 = 64 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_fourteen]
  native_decide
example : evenCompClass.count 15 = 0 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_fifteen]
  native_decide
example : evenCompClass.count 16 = 128 := by
  apply of_decide_eq_true
  rw [evenCompClass_count_sixteen]
  native_decide

private def halveEvenPart (x : evenPartClass.Obj) : posIntClass.Obj :=
  ⟨x.1 / 2, by
    obtain ⟨a, ha⟩ : ∃ a, x.1 = 2 * a := Nat.dvd_iff_mod_eq_zero.mpr x.2.1
    have hx_pos : 0 < x.1 := x.2.2
    rw [ha] at hx_pos
    have ha_pos : 0 < a := by omega
    have hdiv : x.1 / 2 = a := by
      calc
        x.1 / 2 = (2 * a) / 2 := by rw [ha]
        _ = a := Nat.mul_div_right a (by decide : 0 < 2)
    rw [hdiv]
    exact Nat.succ_le_of_lt ha_pos⟩

private def doublePosPart (x : posIntClass.Obj) : evenPartClass.Obj :=
  ⟨2 * x.1, by
    constructor
    · rw [Nat.mul_mod_right]
    · exact Nat.mul_pos (by decide : 0 < 2) (Nat.lt_of_lt_of_le Nat.zero_lt_one x.2)⟩

private lemma evenPart_size_halve (x : evenPartClass.Obj) :
    evenPartClass.size x = 2 * posIntClass.size (halveEvenPart x) := by
  obtain ⟨a, ha⟩ : ∃ a, x.1 = 2 * a := Nat.dvd_iff_mod_eq_zero.mpr x.2.1
  change x.1 = 2 * (x.1 / 2)
  have hdiv : x.1 / 2 = a := by
    calc
      x.1 / 2 = (2 * a) / 2 := by rw [ha]
      _ = a := Nat.mul_div_right a (by decide : 0 < 2)
  rw [hdiv]
  exact ha

private lemma halveEvenList_size (xs : List evenPartClass.Obj) :
    (seqClass evenPartClass evenPartClass.count_zero).size xs =
      2 * (seqClass posIntClass posIntClass.count_zero).size (xs.map halveEvenPart) := by
  induction xs with
  | nil => simp [seqClass]
  | cons x xs ih =>
      change evenPartClass.size x +
          (seqClass evenPartClass evenPartClass.count_zero).size xs =
        2 * (posIntClass.size (halveEvenPart x) +
          (seqClass posIntClass posIntClass.count_zero).size (xs.map halveEvenPart))
      rw [evenPart_size_halve x, ih]
      ring

private lemma doublePosList_size (xs : List posIntClass.Obj) :
    (seqClass evenPartClass evenPartClass.count_zero).size (xs.map doublePosPart) =
      2 * (seqClass posIntClass posIntClass.count_zero).size xs := by
  induction xs with
  | nil => simp [seqClass]
  | cons x xs ih =>
      change evenPartClass.size (doublePosPart x) +
          (seqClass evenPartClass evenPartClass.count_zero).size (xs.map doublePosPart) =
        2 * (posIntClass.size x +
          (seqClass posIntClass posIntClass.count_zero).size xs)
      change 2 * posIntClass.size x +
          (seqClass evenPartClass evenPartClass.count_zero).size (xs.map doublePosPart) =
        2 * (posIntClass.size x +
          (seqClass posIntClass posIntClass.count_zero).size xs)
      rw [ih]
      ring

private lemma doublePosPart_halveEvenPart (x : evenPartClass.Obj) :
    doublePosPart (halveEvenPart x) = x := by
  apply Subtype.ext
  change 2 * (halveEvenPart x).1 = x.1
  exact (evenPart_size_halve x).symm

private lemma halveEvenPart_doublePosPart (x : posIntClass.Obj) :
    halveEvenPart (doublePosPart x) = x := by
  apply Subtype.ext
  change (2 * x.1) / 2 = x.1
  exact Nat.mul_div_right x.1 (by decide : 0 < 2)

private lemma evenCompClass_count_even_eq_compositionClass (n : ℕ) :
    evenCompClass.count (2 * n) = compositionClass.count n := by
  unfold evenCompClass compositionClass
  change ((seqClass evenPartClass evenPartClass.count_zero).level (2 * n)).card =
    ((seqClass posIntClass posIntClass.count_zero).level n).card
  apply Finset.card_bij (fun xs _ => xs.map halveEvenPart)
  · intro xs hxs
    rw [CombinatorialClass.level_mem_iff] at hxs ⊢
    have hsize := halveEvenList_size xs
    omega
  · intro xs₁ _ xs₂ _ hmap
    have h := congrArg (List.map doublePosPart) hmap
    simpa [List.map_map, Function.comp_def, doublePosPart_halveEvenPart] using h
  · intro ys hys
    refine ⟨ys.map doublePosPart, ?_, ?_⟩
    · rw [CombinatorialClass.level_mem_iff] at hys ⊢
      rw [doublePosList_size, hys]
    · simp [List.map_map, Function.comp_def, halveEvenPart_doublePosPart]

theorem evenCompClass_count_odd (k : ℕ) :
    evenCompClass.count (2 * k + 1) = 0 := by
  unfold evenCompClass
  change ((seqClass evenPartClass evenPartClass.count_zero).level (2 * k + 1)).card = 0
  rw [Finset.card_eq_zero]
  ext xs
  simp only [Finset.notMem_empty, iff_false]
  intro hxs
  rw [CombinatorialClass.level_mem_iff] at hxs
  have hsize := halveEvenList_size xs
  omega

theorem evenCompClass_count_even_succ (k : ℕ) :
    evenCompClass.count (2 * (k + 1)) = 2 ^ k := by
  rw [evenCompClass_count_even_eq_compositionClass]
  exact compositionClass_count_succ k
