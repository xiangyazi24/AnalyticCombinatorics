/-
  Chapter I § I.3 — Strings and regular languages

  Strings over a k-letter alphabet are SEQ(A), where A has k atoms of size 1.
  The binary language avoiding the pattern "11" is a direct restricted class
  of words over Fin 2.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Vector.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences

set_option linter.style.show false

open PowerSeries CombinatorialClass
open List.Vector

/-! ## Strings over a finite alphabet -/

/-- The k-letter alphabet: each letter is an atom of size 1. -/
def alphabetClass (k : ℕ) : CombinatorialClass where
  Obj := Fin k
  size _ := 1
  finite_level _ := Set.finite_univ.subset (Set.subset_univ _)

namespace alphabetClass

/-- A k-letter alphabet has no size-0 letters. -/
lemma count_zero (k : ℕ) : (alphabetClass k).count 0 = 0 := by
  simp only [count]
  rw [Finset.card_eq_zero]
  ext a
  simp only [Finset.notMem_empty, iff_false]
  intro ha
  have hsz : (alphabetClass k).size a = 0 :=
    ((alphabetClass k).finite_level 0).mem_toFinset.mp ha
  exact absurd hsz (by show (1 : ℕ) ≠ 0; omega)

/-- There are exactly k letters of size 1. -/
lemma count_one (k : ℕ) : (alphabetClass k).count 1 = k := by
  letI : Fintype (alphabetClass k).Obj := inferInstanceAs (Fintype (Fin k))
  show ((alphabetClass k).level 1).card = k
  have h_level : (alphabetClass k).level 1 = (Finset.univ : Finset (Fin k)) := by
    ext a
    constructor
    · intro _
      exact Finset.mem_univ a
    · intro _
      rw [CombinatorialClass.level_mem_iff]
      rfl
  rw [h_level]
  exact Fintype.card_fin k

/-- For sizes other than 1, the alphabet has no objects. -/
lemma count_eq_zero_of_ne_one {k n : ℕ} (hn : n ≠ 1) :
    (alphabetClass k).count n = 0 := by
  simp only [count]
  rw [Finset.card_eq_zero]
  ext a
  simp only [Finset.notMem_empty, iff_false]
  intro ha
  have hsz : (alphabetClass k).size a = n :=
    ((alphabetClass k).finite_level n).mem_toFinset.mp ha
  exact hn hsz.symm

/-- Count formula for the alphabet itself. -/
theorem count (k n : ℕ) :
    (alphabetClass k).count n = if n = 1 then k else 0 := by
  by_cases hn : n = 1
  · subst n
    rw [count_one]
    simp
  · rw [count_eq_zero_of_ne_one hn]
    simp [hn]

/-- OGF of the k-letter alphabet: `k z`. -/
theorem ogfZ_eq (k : ℕ) :
    ogfZ (alphabetClass k) = PowerSeries.C (k : ℤ) * PowerSeries.X := by
  ext n
  rw [show PowerSeries.X = (PowerSeries.X : PowerSeries ℤ) ^ 1 by simp]
  rw [PowerSeries.coeff_C_mul_X_pow]
  by_cases hn : n = 1
  · subst n
    simp [ogfZ, coeff_ogf, count_one]
  · simp [ogfZ, coeff_ogf, count_eq_zero_of_ne_one hn, hn]

end alphabetClass

/-- The class of strings over a k-letter alphabet. -/
noncomputable def stringsClass (k : ℕ) : CombinatorialClass :=
  seqClass (alphabetClass k) (alphabetClass.count_zero k)

/-- Strings over a k-letter alphabet are counted by `k^n`. -/
theorem stringCount_eq_pow (k : ℕ) (_hk : 0 < k) (n : ℕ) :
    (seqClass (alphabetClass k) (alphabetClass.count_zero k)).count n = k ^ n := by
  induction n with
  | zero =>
      rw [seqClass.count_zero]
      simp
  | succ m ih =>
      rw [seqClass.count_succ]
      rw [Finset.sum_eq_single (1, m)]
      · rw [alphabetClass.count_one, ih, pow_succ]
        ring
      · rintro ⟨i, j⟩ hij hne
        by_cases hi : i = 1
        · exfalso
          subst i
          rw [Finset.mem_antidiagonal] at hij
          apply hne
          ext <;> omega
        · rw [alphabetClass.count_eq_zero_of_ne_one hi, zero_mul]
      · intro h
        exfalso
        apply h
        rw [Finset.mem_antidiagonal]
        omega

/-- Version without the positivity hypothesis; useful for examples and coefficients. -/
theorem stringsClass_count_eq_pow (k n : ℕ) : (stringsClass k).count n = k ^ n := by
  rcases k with _ | k
  · induction n with
    | zero =>
        rw [stringsClass, seqClass.count_zero]
        simp
    | succ m ih =>
        rw [stringsClass, seqClass.count_succ]
        rw [Finset.sum_eq_single (1, m)]
        · rw [alphabetClass.count_one]
          simp
        · rintro ⟨i, j⟩ hij hne
          by_cases hi : i = 1
          · exfalso
            subst i
            rw [Finset.mem_antidiagonal] at hij
            apply hne
            ext <;> omega
          · rw [alphabetClass.count_eq_zero_of_ne_one hi, zero_mul]
        · intro h
          exfalso
          apply h
          rw [Finset.mem_antidiagonal]
          omega
  · exact stringCount_eq_pow (k + 1) (Nat.succ_pos k) n

/-- The OGF identity for strings over k letters: `(1 - k z) S(z) = 1`. -/
theorem stringsClass_ogfZ_eq (k : ℕ) :
    (1 - PowerSeries.C (k : ℤ) * PowerSeries.X) * ogfZ (stringsClass k) = 1 := by
  unfold stringsClass
  rw [← alphabetClass.ogfZ_eq k]
  exact seqClass_ogf_eq (alphabetClass k) (alphabetClass.count_zero k)

/-! Sanity checks for binary and ternary strings. -/

example : (stringsClass 2).count 0 = 1 := by rw [stringsClass_count_eq_pow]; decide
example : (stringsClass 2).count 1 = 2 := by rw [stringsClass_count_eq_pow]; decide
example : (stringsClass 2).count 2 = 4 := by rw [stringsClass_count_eq_pow]; decide
example : (stringsClass 2).count 3 = 8 := by rw [stringsClass_count_eq_pow]; decide

example : (stringsClass 3).count 0 = 1 := by rw [stringsClass_count_eq_pow]; decide
example : (stringsClass 3).count 1 = 3 := by rw [stringsClass_count_eq_pow]; decide
example : (stringsClass 3).count 2 = 9 := by rw [stringsClass_count_eq_pow]; decide

/-! ## Binary strings avoiding "11" -/

/-- No two adjacent letters are both `1`. -/
def noConsecOnes : List (Fin 2) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      ¬ (a = (1 : Fin 2) ∧ b = (1 : Fin 2)) ∧ noConsecOnes (b :: rest)

instance instDecidableNoConsecOnes (w : List (Fin 2)) : Decidable (noConsecOnes w) := by
  induction w with
  | nil => exact isTrue trivial
  | cons a t ih =>
      cases t with
      | nil => exact isTrue trivial
      | cons b rest =>
          dsimp [noConsecOnes]
          haveI := ih
          infer_instance

/-- Length-n binary words avoiding `11`. -/
abbrev NoConsecOnesWord (n : ℕ) :=
  { w : List.Vector (Fin 2) n // noConsecOnes w.val }

/-- Binary strings, with size = length, restricted to words avoiding `11`. -/
def stringsNoConsecOnesClass : CombinatorialClass where
  Obj := Σ n : ℕ, NoConsecOnesWord n
  size := Sigma.fst
  finite_level n := by
    have hfin : Set.Finite (Set.univ : Set (NoConsecOnesWord n)) := Set.toFinite _
    apply Set.Finite.subset (hfin.image (Sigma.mk n))
    rintro ⟨k, w⟩ hw
    simp only [Set.mem_setOf_eq] at hw
    change k = n at hw
    subst k
    exact ⟨w, Set.mem_univ _, rfl⟩

namespace stringsNoConsecOnesClass

/-- Level n is the finite type of length-n words avoiding `11`. -/
theorem count_eq_card (n : ℕ) :
    stringsNoConsecOnesClass.count n = Fintype.card (NoConsecOnesWord n) := by
  rw [CombinatorialClass.count]
  have hcard : (stringsNoConsecOnesClass.level n).card =
      (Finset.univ : Finset (NoConsecOnesWord n)).card := by
    refine Finset.card_bij'
      (s := stringsNoConsecOnesClass.level n)
      (t := (Finset.univ : Finset (NoConsecOnesWord n)))
      (fun x hx => by
        obtain ⟨k, w⟩ := x
        have hsize : stringsNoConsecOnesClass.size ⟨k, w⟩ = n :=
          (CombinatorialClass.level_mem_iff (C := stringsNoConsecOnesClass) ⟨k, w⟩).mp hx
        change k = n at hsize
        subst k
        exact w)
      (fun w _ => (⟨n, w⟩ : stringsNoConsecOnesClass.Obj))
      ?_ ?_ ?_ ?_
    · intro _ _
      exact Finset.mem_univ _
    · intro w _
      exact (CombinatorialClass.level_mem_iff (C := stringsNoConsecOnesClass) ⟨n, w⟩).mpr rfl
    · intro x hx
      obtain ⟨k, w⟩ := x
      have hsize : stringsNoConsecOnesClass.size ⟨k, w⟩ = n :=
        (CombinatorialClass.level_mem_iff (C := stringsNoConsecOnesClass) ⟨k, w⟩).mp hx
      change k = n at hsize
      subst k
      rfl
    · intro w _
      rfl
  rw [hcard, Finset.card_univ]

end stringsNoConsecOnesClass

private lemma noConsecOnes_tail_list {w : List (Fin 2)} (h : noConsecOnes w) :
    noConsecOnes w.tail := by
  cases w with
  | nil => trivial
  | cons a t =>
      cases t with
      | nil => trivial
      | cons b rest => exact h.2

private lemma noConsecOnes_vector_tail {n : ℕ} (v : List.Vector (Fin 2) (n + 1))
    (h : noConsecOnes v.val) : noConsecOnes v.tail.val := by
  simpa [List.Vector.tail_val] using noConsecOnes_tail_list h

private lemma noConsecOnes_zero_cons {w : List (Fin 2)} (h : noConsecOnes w) :
    noConsecOnes ((0 : Fin 2) :: w) := by
  cases w with
  | nil => trivial
  | cons b rest =>
      simp [noConsecOnes, h]

private lemma noConsecOnes_one_zero_cons {w : List (Fin 2)} (h : noConsecOnes w) :
    noConsecOnes ((1 : Fin 2) :: (0 : Fin 2) :: w) := by
  exact ⟨by simp, noConsecOnes_zero_cons h⟩

/-- Split a valid word of length `n + 2` by its first letter. -/
private def noConsecOnesWord_splitEquiv (n : ℕ) :
    NoConsecOnesWord (n + 2) ≃ NoConsecOnesWord (n + 1) ⊕ NoConsecOnesWord n where
  toFun w :=
    if h : w.1.head = (0 : Fin 2) then
      Sum.inl ⟨w.1.tail, noConsecOnes_vector_tail w.1 w.2⟩
    else
      Sum.inr ⟨w.1.tail.tail,
        noConsecOnes_vector_tail w.1.tail (noConsecOnes_vector_tail w.1 w.2)⟩
  invFun
    | Sum.inl w =>
        ⟨(0 : Fin 2) ::ᵥ w.1, by
          simpa [List.Vector.cons_val] using noConsecOnes_zero_cons w.2⟩
    | Sum.inr w =>
        ⟨(1 : Fin 2) ::ᵥ (0 : Fin 2) ::ᵥ w.1, by
          simpa [List.Vector.cons_val] using noConsecOnes_one_zero_cons w.2⟩
  left_inv := by
    intro w
    cases w with
    | mk v hv =>
        obtain ⟨a, t, rfl⟩ := List.Vector.exists_eq_cons v
        obtain ⟨b, r, rfl⟩ := List.Vector.exists_eq_cons t
        fin_cases a <;> fin_cases b <;> simp [noConsecOnes] at hv ⊢
  right_inv := by
    intro w
    cases w with
    | inl w =>
        cases w with
        | mk val h =>
            simp
    | inr w =>
        cases w with
        | mk val h =>
            simp

private lemma stringsNoConsecOnes_count_zero :
    stringsNoConsecOnesClass.count 0 = 1 := by
  rw [stringsNoConsecOnesClass.count_eq_card]
  decide

private lemma stringsNoConsecOnes_count_one :
    stringsNoConsecOnesClass.count 1 = 2 := by
  rw [stringsNoConsecOnesClass.count_eq_card]
  decide

/-- Fibonacci recurrence for binary strings avoiding `11`. -/
theorem stringsNoConsecOnes_count_succ_succ (n : ℕ) :
    stringsNoConsecOnesClass.count (n + 2) =
      stringsNoConsecOnesClass.count (n + 1) + stringsNoConsecOnesClass.count n := by
  rw [stringsNoConsecOnesClass.count_eq_card, stringsNoConsecOnesClass.count_eq_card,
    stringsNoConsecOnesClass.count_eq_card]
  calc
    Fintype.card (NoConsecOnesWord (n + 2))
        = Fintype.card (NoConsecOnesWord (n + 1) ⊕ NoConsecOnesWord n) := by
          exact Fintype.card_congr (noConsecOnesWord_splitEquiv n)
    _ = Fintype.card (NoConsecOnesWord (n + 1)) +
        Fintype.card (NoConsecOnesWord n) := by
          rw [Fintype.card_sum]

/-- Binary strings of length n avoiding `11` are counted by `fib (n + 2)`. -/
theorem stringsNoConsecOnes_count (n : ℕ) :
    stringsNoConsecOnesClass.count n = Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [stringsNoConsecOnes_count_zero, Nat.fib_two]
  | one =>
      rw [stringsNoConsecOnes_count_one]
      decide
  | more n ih0 ih1 =>
      rw [stringsNoConsecOnes_count_succ_succ, ih0, ih1]
      rw [show n + 1 + 2 = (n + 1) + 2 by omega]
      rw [show n + 2 + 2 = (n + 2) + 2 by omega]
      rw [show (n + 1) + 2 = (n + 2) + 1 by omega]
      rw [show Nat.fib ((n + 2) + 1) + Nat.fib (n + 2) =
        Nat.fib (n + 2) + Nat.fib ((n + 2) + 1) by ac_rfl]
      exact (Nat.fib_add_two (n := n + 2)).symm

set_option linter.flexible false in
/-- OGF identity for binary strings avoiding `11`: `S(z)(1 - z - z^2) = 1 + z`. -/
theorem stringsNoConsecOnes_ogfZ_mul_one_sub_X_sub_X_sq :
    ogfZ stringsNoConsecOnesClass * (1 - PowerSeries.X - PowerSeries.X ^ 2) =
      1 + PowerSeries.X := by
  rw [show ogfZ stringsNoConsecOnesClass * (1 - PowerSeries.X - PowerSeries.X ^ 2) =
      ogfZ stringsNoConsecOnesClass - ogfZ stringsNoConsecOnesClass * PowerSeries.X -
        ogfZ stringsNoConsecOnesClass * PowerSeries.X ^ 2 by ring]
  ext n
  rcases n with _ | m
  · simp only [map_sub]
    rw [show coeff 0 (ogfZ stringsNoConsecOnesClass) =
        (stringsNoConsecOnesClass.count 0 : ℤ) by
      simp [ogfZ, coeff_ogf]]
    simp [stringsNoConsecOnes_count_zero, PowerSeries.coeff_mul_X_pow']
  · have hshiftX : coeff (m + 1) (ogfZ stringsNoConsecOnesClass * PowerSeries.X) =
        (stringsNoConsecOnesClass.count m : ℤ) := by
      rw [PowerSeries.coeff_succ_mul_X]
      simp [ogfZ, coeff_ogf]
    rw [map_sub, map_sub, hshiftX]
    cases m with
    | zero =>
        simp [ogfZ, coeff_ogf, stringsNoConsecOnes_count, PowerSeries.coeff_mul_X_pow',
          PowerSeries.coeff_one]
        rw [show Nat.fib 3 = 2 by decide]
        norm_num
    | succ m =>
        have hshiftX2 :
            coeff (m + 2) (ogfZ stringsNoConsecOnesClass * PowerSeries.X ^ 2) =
              (stringsNoConsecOnesClass.count m : ℤ) := by
          rw [show m + 2 = m + 2 by rfl]
          rw [PowerSeries.coeff_mul_X_pow]
          simp [ogfZ, coeff_ogf]
        rw [hshiftX2]
        rw [show coeff (m + 2) (ogfZ stringsNoConsecOnesClass) =
            (stringsNoConsecOnesClass.count (m + 2) : ℤ) by
          simp [ogfZ, coeff_ogf]]
        rw [show (stringsNoConsecOnesClass.count (m + 1) : ℤ) =
            coeff (m + 1) (ogfZ stringsNoConsecOnesClass) by
          simp [ogfZ, coeff_ogf]]
        simp [ogfZ, coeff_ogf, stringsNoConsecOnes_count, Nat.fib_add_two, PowerSeries.coeff_X]

/-! Sanity checks for no-11 strings. -/

example : stringsNoConsecOnesClass.count 0 = 1 := by
  rw [stringsNoConsecOnesClass.count_eq_card]
  decide

example : stringsNoConsecOnesClass.count 1 = 2 := by
  rw [stringsNoConsecOnesClass.count_eq_card]
  decide

example : stringsNoConsecOnesClass.count 2 = 3 := by
  rw [stringsNoConsecOnesClass.count_eq_card]
  decide

example : stringsNoConsecOnesClass.count 3 = 5 := by
  rw [stringsNoConsecOnesClass.count_eq_card]
  decide

example : stringsNoConsecOnesClass.count 4 = 8 := by
  rw [stringsNoConsecOnesClass.count_eq_card]
  decide
