/-
  Analytic Combinatorics — Examples
  Fibonacci compositions

  Compositions of n into parts of size 1 or 2, equivalently domino tilings
  of a 1 × n strip by monomers and dimers.
-/
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import Mathlib.Data.Nat.Fib.Basic

open CombinatorialClass Finset

/-- The atom class for parts of size 1 or 2. Count is 1 at sizes 1 and 2, else 0. -/
noncomputable def stepClass : CombinatorialClass :=
  (atomOfSize 1).disjSum (atomOfSize 2)

/-- stepClass has no size-0 part. -/
theorem stepClass_count_zero : stepClass.count 0 = 0 := by
  change (CombinatorialClass.disjSum (atomOfSize 1) (atomOfSize 2)).count 0 = 0
  rw [CombinatorialClass.disjSum_count, atomOfSize_count, atomOfSize_count]
  decide

/-- Compositions into parts of size 1 or 2. -/
noncomputable def fibClass : CombinatorialClass :=
  seqClass stepClass stepClass_count_zero

private lemma stepClass_count (k : ℕ) :
    stepClass.count k = if k = 1 then 1 else if k = 2 then 1 else 0 := by
  unfold stepClass
  rw [CombinatorialClass.disjSum_count, atomOfSize_count, atomOfSize_count]
  by_cases h1 : k = 1
  · simp [h1]
  · by_cases h2 : k = 2
    · simp [h2]
    · simp [h1, h2]

/-- The empty composition is the unique composition of 0. -/
theorem fibClass_count_zero : fibClass.count 0 = 1 := by
  change (seqClass stepClass stepClass_count_zero).count 0 = 1
  rw [seqClass.count_zero]

/-- There is exactly one composition of 1 into parts 1 and 2. -/
private lemma fibClass_count_one : fibClass.count 1 = 1 := by
  change (seqClass stepClass stepClass_count_zero).count (0 + 1) = 1
  rw [seqClass.count_succ]
  rw [Finset.sum_eq_single_of_mem (1, 0)]
  · rw [stepClass_count, seqClass.count_zero]
    simp
  · rw [Finset.mem_antidiagonal]
    omega
  · intro p hp hp_ne
    have hp_sum : p.1 + p.2 = 1 := Finset.mem_antidiagonal.mp hp
    rw [stepClass_count]
    by_cases h1 : p.1 = 1
    · have hp_eq : p = (1, 0) := by
        ext <;> omega
      exact (hp_ne hp_eq).elim
    · have h2 : p.1 ≠ 2 := by omega
      simp [h1, h2]

private lemma stepClass_mul_count_eq (n : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ Finset.antidiagonal (n + 2)) :
    stepClass.count p.1 * fibClass.count p.2 =
      (if p = (1, n + 1) then fibClass.count (n + 1) else 0) +
        (if p = (2, n) then fibClass.count n else 0) := by
  have hp_sum : p.1 + p.2 = n + 2 := Finset.mem_antidiagonal.mp hp
  rw [stepClass_count]
  by_cases h1 : p.1 = 1
  · have hp_eq : p = (1, n + 1) := by
      ext <;> omega
    simp [hp_eq]
  · by_cases h2 : p.1 = 2
    · have hp_eq : p = (2, n) := by
        ext <;> omega
      simp [hp_eq]
    · have hp_ne1 : p ≠ (1, n + 1) := by
        intro hp_eq
        exact h1 (congrArg Prod.fst hp_eq)
      have hp_ne2 : p ≠ (2, n) := by
        intro hp_eq
        exact h2 (congrArg Prod.fst hp_eq)
      simp [h1, h2, hp_ne1, hp_ne2]

/-- Fibonacci recurrence for compositions into parts 1 and 2. -/
private lemma fibClass_count_succ_succ (n : ℕ) :
    fibClass.count (n + 2) = fibClass.count (n + 1) + fibClass.count n := by
  change (seqClass stepClass stepClass_count_zero).count ((n + 1) + 1) =
    fibClass.count (n + 1) + fibClass.count n
  rw [seqClass.count_succ]
  rw [show (n + 1) + 1 = n + 2 by omega]
  calc
    ∑ p ∈ Finset.antidiagonal (n + 2), stepClass.count p.1 * fibClass.count p.2
        = ∑ p ∈ Finset.antidiagonal (n + 2),
            ((if p = (1, n + 1) then fibClass.count (n + 1) else 0) +
              (if p = (2, n) then fibClass.count n else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact stepClass_mul_count_eq n p hp
    _ = (∑ p ∈ Finset.antidiagonal (n + 2),
            if p = (1, n + 1) then fibClass.count (n + 1) else 0) +
          (∑ p ∈ Finset.antidiagonal (n + 2),
            if p = (2, n) then fibClass.count n else 0) := by
          rw [Finset.sum_add_distrib]
    _ = fibClass.count (n + 1) + fibClass.count n := by
          have hmem1 : (1, n + 1) ∈ Finset.antidiagonal (n + 2) := by
            rw [Finset.mem_antidiagonal]
            omega
          have hmem2 : (2, n) ∈ Finset.antidiagonal (n + 2) := by
            rw [Finset.mem_antidiagonal]
            omega
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp [hmem1, hmem2]

/-- The number of compositions of n into 1s and 2s equals fib(n+1). -/
theorem fibClass_count_eq_fib (n : ℕ) : fibClass.count n = Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [fibClass_count_zero, Nat.fib_one]
  | one =>
      rw [fibClass_count_one, Nat.fib_two]
  | more n ih0 ih1 =>
      rw [fibClass_count_succ_succ, ih0, ih1]
      rw [show n + 1 + 1 = (n + 1) + 1 by omega]
      rw [show n + 2 + 1 = (n + 1) + 2 by omega]
      rw [show Nat.fib ((n + 1) + 1) + Nat.fib (n + 1) =
        Nat.fib (n + 1) + Nat.fib ((n + 1) + 1) by ac_rfl]
      exact (Nat.fib_add_two (n := n + 1)).symm

/-! Sanity checks: 1 composition of 0, 1 of 1, 2 of 2, 3 of 3, 5 of 4. -/
example : fibClass.count 0 = 1 := fibClass_count_zero
example : fibClass.count 1 = 1 := fibClass_count_eq_fib 1
example : fibClass.count 2 = 2 := fibClass_count_eq_fib 2
example : fibClass.count 3 = 3 := fibClass_count_eq_fib 3
example : fibClass.count 4 = 5 := fibClass_count_eq_fib 4
