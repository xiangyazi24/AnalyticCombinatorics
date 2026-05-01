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

private lemma oddCompClass_mem_level_iff (n : ℕ) (xs : List oddPartClass.Obj) :
    xs ∈ oddCompClass.level n ↔ xs.foldr (fun b acc => b.1 + acc) 0 = n := by
  exact CombinatorialClass.level_mem_iff (C := oddCompClass) (n := n) xs

private def oddPartOne : oddPartClass.Obj :=
  ⟨1, by decide⟩

private def oddPartPred2 (a : oddPartClass.Obj) (h : a.1 ≠ 1) : oddPartClass.Obj :=
  ⟨a.1 - 2, by
    have haodd : a.1 % 2 = 1 := a.2
    omega⟩

private def oddPartAdd2 (a : oddPartClass.Obj) : oddPartClass.Obj :=
  ⟨a.1 + 2, by
    have haodd : a.1 % 2 = 1 := a.2
    omega⟩

private lemma oddPart_eq_one_of_val_eq_one (a : oddPartClass.Obj) (h : a.1 = 1) :
    a = oddPartOne := by
  apply Subtype.ext
  exact h

private lemma oddPart_add2_pred2 (a : oddPartClass.Obj) (h : a.1 ≠ 1) :
    oddPartAdd2 (oddPartPred2 a h) = a := by
  apply Subtype.ext
  have haodd : a.1 % 2 = 1 := a.2
  have ha3 : 3 ≤ a.1 := by omega
  change (a.1 - 2) + 2 = a.1
  omega

private lemma oddPart_pred2_add2 (a : oddPartClass.Obj) (h : (oddPartAdd2 a).1 ≠ 1) :
    oddPartPred2 (oddPartAdd2 a) h = a := by
  apply Subtype.ext
  change (a.1 + 2) - 2 = a.1
  omega

private lemma mem_left_of_inl_mem_disjSum {α β : Type*} {s : Finset α} {t : Finset β}
    {x : α} (h : Sum.inl x ∈ s.disjSum t) : x ∈ s := by
  rcases Finset.mem_disjSum.mp h with ⟨a, ha, hx⟩ | ⟨b, _hb, hx⟩
  · cases hx
    exact ha
  · cases hx

private lemma mem_right_of_inr_mem_disjSum {α β : Type*} {s : Finset α} {t : Finset β}
    {x : β} (h : Sum.inr x ∈ s.disjSum t) : x ∈ t := by
  rcases Finset.mem_disjSum.mp h with ⟨a, _ha, hx⟩ | ⟨b, hb, hx⟩
  · cases hx
  · cases hx
    exact hb

private def oddCompSplit (xs : List oddPartClass.Obj) :
    List oddPartClass.Obj ⊕ List oddPartClass.Obj :=
  match xs with
  | [] => Sum.inl []
  | a :: ys =>
      if h : a.1 = 1 then
        Sum.inl ys
      else
        Sum.inr (oddPartPred2 a h :: ys)

private def oddCompUnsplit :
    List oddPartClass.Obj ⊕ List oddPartClass.Obj → List oddPartClass.Obj
  | Sum.inl ys => oddPartOne :: ys
  | Sum.inr [] => []
  | Sum.inr (a :: ys) => oddPartAdd2 a :: ys

/-- Fibonacci recurrence for compositions into odd parts, starting at size `1`. -/
private lemma oddCompClass_count_add_three (n : ℕ) :
    oddCompClass.count (n + 3) =
      oddCompClass.count (n + 2) + oddCompClass.count (n + 1) := by
  let target :=
    (oddCompClass.level (n + 2)).disjSum (oddCompClass.level (n + 1))
  have hcard : (oddCompClass.level (n + 3)).card = target.card := by
    apply Finset.card_bij'
      (s := oddCompClass.level (n + 3))
      (t := target)
      (fun xs _ => oddCompSplit xs)
      (fun y _ => oddCompUnsplit y)
    · intro xs hxs
      cases xs with
      | nil =>
          have hsz := (oddCompClass_mem_level_iff (n + 3) ([] : List oddPartClass.Obj)).mp hxs
          simp at hsz
      | cons a ys =>
          by_cases h1 : a.1 = 1
          · have hys : ys ∈ oddCompClass.level (n + 2) := by
              have hsz :=
                (oddCompClass_mem_level_iff (n + 3) (a :: ys)).mp hxs
              apply (oddCompClass_mem_level_iff (n + 2) ys).mpr
              simp only [List.foldr_cons] at hsz
              omega
            change oddCompSplit (a :: ys) ∈ target
            rw [oddCompSplit]
            rw [dif_pos h1]
            exact Finset.mem_disjSum.mpr (Or.inl ⟨ys, hys, rfl⟩)
          · have hys : oddPartPred2 a h1 :: ys ∈ oddCompClass.level (n + 1) := by
              have hsz :=
                (oddCompClass_mem_level_iff (n + 3) (a :: ys)).mp hxs
              apply (oddCompClass_mem_level_iff (n + 1) (oddPartPred2 a h1 :: ys)).mpr
              simp only [List.foldr_cons] at hsz
              change a.1 - 2 + ys.foldr (fun b acc => b.1 + acc) 0 = n + 1
              have haodd : a.1 % 2 = 1 := a.2
              have ha3 : 3 ≤ a.1 := by omega
              omega
            change oddCompSplit (a :: ys) ∈ target
            rw [oddCompSplit]
            rw [dif_neg h1]
            exact Finset.mem_disjSum.mpr (Or.inr ⟨oddPartPred2 a h1 :: ys, hys, rfl⟩)
    · intro y hy
      cases y with
      | inl ys =>
          have hys : ys ∈ oddCompClass.level (n + 2) :=
            mem_left_of_inl_mem_disjSum hy
          have hsz := (oddCompClass_mem_level_iff (n + 2) ys).mp hys
          apply (oddCompClass_mem_level_iff (n + 3) (oddCompUnsplit (Sum.inl ys))).mpr
          simp only [oddCompUnsplit, List.foldr_cons]
          change 1 + ys.foldr (fun b acc => b.1 + acc) 0 = n + 3
          omega
      | inr zs =>
          have hzs : zs ∈ oddCompClass.level (n + 1) :=
            mem_right_of_inr_mem_disjSum hy
          cases zs with
          | nil =>
              have hsz :=
                (oddCompClass_mem_level_iff (n + 1) ([] : List oddPartClass.Obj)).mp hzs
              simp at hsz
          | cons a ys =>
              have hsz := (oddCompClass_mem_level_iff (n + 1) (a :: ys)).mp hzs
              apply (oddCompClass_mem_level_iff (n + 3)
                (oddCompUnsplit (Sum.inr (a :: ys)))).mpr
              simp only [oddCompUnsplit, List.foldr_cons]
              change a.1 + 2 + ys.foldr (fun b acc => b.1 + acc) 0 = n + 3
              simp only [List.foldr_cons] at hsz
              omega
    · intro xs hxs
      cases xs with
      | nil =>
          have hsz := (oddCompClass_mem_level_iff (n + 3) ([] : List oddPartClass.Obj)).mp hxs
          simp at hsz
      | cons a ys =>
          by_cases h1 : a.1 = 1
          · rw [oddPart_eq_one_of_val_eq_one a h1]
            simp [oddCompSplit, oddCompUnsplit, oddPartOne]
          · simp [oddCompSplit, oddCompUnsplit, h1, oddPart_add2_pred2 a h1]
    · intro y hy
      cases y with
      | inl ys =>
          simp [oddCompSplit, oddCompUnsplit, oddPartOne]
          rfl
      | inr zs =>
          have hzs : zs ∈ oddCompClass.level (n + 1) :=
            mem_right_of_inr_mem_disjSum hy
          cases zs with
          | nil =>
              have hsz :=
                (oddCompClass_mem_level_iff (n + 1) ([] : List oddPartClass.Obj)).mp hzs
              simp at hsz
          | cons a ys =>
              have hne : (oddPartAdd2 a).1 ≠ 1 := by
                change a.1 + 2 ≠ 1
                omega
              simp [oddCompSplit, oddCompUnsplit, hne, oddPart_pred2_add2 a hne]
              rfl
  rw [show oddCompClass.count (n + 3) = (oddCompClass.level (n + 3)).card from rfl,
    hcard]
  dsimp [target]
  rw [Finset.card_disjSum]
  rfl

/-- Compositions of `n + 1` into odd parts are counted by `fib (n + 1)`. -/
theorem oddCompClass_count_succ_eq_fib (n : ℕ) :
    oddCompClass.count (n + 1) = Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [oddCompClass_count_one, Nat.fib_one]
  | one =>
      rw [oddCompClass_count_two, Nat.fib_two]
  | more n ih0 ih1 =>
      rw [show n + 2 + 1 = n + 3 by omega]
      rw [oddCompClass_count_add_three, ih0, ih1]
      rw [show n + 1 + 1 = n + 2 by omega]
      rw [show n + 2 + 1 = n + 3 by omega]
      rw [show Nat.fib (n + 2) + Nat.fib (n + 1) =
        Nat.fib (n + 1) + Nat.fib (n + 2) by ac_rfl]
      exact (Nat.fib_add_two (n := n + 1)).symm

example : oddCompClass.count 7 = 13 := by
  rw [show 7 = 6 + 1 by decide, oddCompClass_count_succ_eq_fib]
  decide

example : oddCompClass.count 8 = 21 := by
  rw [show 8 = 7 + 1 by decide, oddCompClass_count_succ_eq_fib]
  decide

example : oddCompClass.count 9 = 34 := by
  rw [show 9 = 8 + 1 by decide, oddCompClass_count_succ_eq_fib]
  decide

example : oddCompClass.count 10 = 55 := by
  rw [show 10 = 9 + 1 by decide, oddCompClass_count_succ_eq_fib]
  decide

example : oddCompClass.count 11 = 89 := by
  rw [show 11 = 10 + 1 by decide, oddCompClass_count_succ_eq_fib]
  decide

example : oddCompClass.count 12 = 144 := by
  rw [show 12 = 11 + 1 by decide, oddCompClass_count_succ_eq_fib]
  decide
