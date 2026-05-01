/-
  Analytic Combinatorics — Examples
  Tribonacci compositions

  Compositions of n into parts of size 1, 2, or 3.
-/
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences

open PowerSeries CombinatorialClass Finset

/-- The atom class for parts of size 1, 2, or 3. -/
noncomputable def step123Class : CombinatorialClass :=
  ((atomOfSize 1).disjSum (atomOfSize 2)).disjSum (atomOfSize 3)

/-- step123Class has no size-0 part. -/
theorem step123Class_count_zero : step123Class.count 0 = 0 := by
  unfold step123Class
  rw [CombinatorialClass.disjSum_count, CombinatorialClass.disjSum_count,
    atomOfSize_count, atomOfSize_count, atomOfSize_count]
  decide

/-- Compositions into parts of size 1, 2, or 3. -/
noncomputable def tribClass : CombinatorialClass :=
  seqClass step123Class step123Class_count_zero

private lemma step123Class_count (k : ℕ) :
    step123Class.count k =
      if k = 1 then 1 else if k = 2 then 1 else if k = 3 then 1 else 0 := by
  unfold step123Class
  rw [CombinatorialClass.disjSum_count, CombinatorialClass.disjSum_count,
    atomOfSize_count, atomOfSize_count, atomOfSize_count]
  by_cases h1 : k = 1
  · simp [h1]
  · by_cases h2 : k = 2
    · simp [h2]
    · by_cases h3 : k = 3
      · simp [h3]
      · simp [h1, h2, h3]

/-- The empty composition is the unique composition of 0. -/
theorem tribClass_count_zero : tribClass.count 0 = 1 := by
  change (seqClass step123Class step123Class_count_zero).count 0 = 1
  rw [seqClass.count_zero]

private lemma tribClass_count_one : tribClass.count 1 = 1 := by
  change (seqClass step123Class step123Class_count_zero).count (0 + 1) = 1
  rw [seqClass.count_succ]
  rw [Finset.sum_eq_single_of_mem (1, 0)]
  · rw [step123Class_count, seqClass.count_zero]
    simp
  · rw [Finset.mem_antidiagonal]
    omega
  · intro p hp hp_ne
    have hp_sum : p.1 + p.2 = 1 := Finset.mem_antidiagonal.mp hp
    rw [step123Class_count]
    by_cases h1 : p.1 = 1
    · have hp_eq : p = (1, 0) := by
        ext <;> omega
      exact (hp_ne hp_eq).elim
    · have h2 : p.1 ≠ 2 := by omega
      have h3 : p.1 ≠ 3 := by omega
      simp [h1, h2, h3]

private lemma tribClass_count_two : tribClass.count 2 = 2 := by
  change (seqClass step123Class step123Class_count_zero).count (1 + 1) = 2
  rw [seqClass.count_succ]
  calc
    ∑ p ∈ Finset.antidiagonal 2, step123Class.count p.1 * tribClass.count p.2
        = ∑ p ∈ Finset.antidiagonal 2,
            ((if p = (1, 1) then tribClass.count 1 else 0) +
              (if p = (2, 0) then tribClass.count 0 else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hp_sum : p.1 + p.2 = 2 := Finset.mem_antidiagonal.mp hp
          rw [step123Class_count]
          by_cases h1 : p.1 = 1
          · have hp_eq : p = (1, 1) := by
              ext <;> omega
            simp [hp_eq]
          · by_cases h2 : p.1 = 2
            · have hp_eq : p = (2, 0) := by
                ext <;> omega
              simp [hp_eq]
            · have h3 : p.1 ≠ 3 := by omega
              have hp_ne1 : p ≠ (1, 1) := by
                intro hp_eq
                exact h1 (congrArg Prod.fst hp_eq)
              have hp_ne2 : p ≠ (2, 0) := by
                intro hp_eq
                exact h2 (congrArg Prod.fst hp_eq)
              simp [h1, h2, h3, hp_ne1, hp_ne2]
    _ = (∑ p ∈ Finset.antidiagonal 2,
            if p = (1, 1) then tribClass.count 1 else 0) +
          (∑ p ∈ Finset.antidiagonal 2,
            if p = (2, 0) then tribClass.count 0 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = tribClass.count 1 + tribClass.count 0 := by
          have hmem1 : (1, 1) ∈ Finset.antidiagonal 2 := by
            rw [Finset.mem_antidiagonal]
            decide
          have hmem2 : (2, 0) ∈ Finset.antidiagonal 2 := by
            rw [Finset.mem_antidiagonal]
            decide
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp [hmem1, hmem2]
    _ = 2 := by
          rw [tribClass_count_one, tribClass_count_zero]

private lemma step123Class_mul_count_eq (n : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ Finset.antidiagonal (n + 3)) :
    step123Class.count p.1 * tribClass.count p.2 =
      (if p = (1, n + 2) then tribClass.count (n + 2) else 0) +
        (if p = (2, n + 1) then tribClass.count (n + 1) else 0) +
          (if p = (3, n) then tribClass.count n else 0) := by
  have hp_sum : p.1 + p.2 = n + 3 := Finset.mem_antidiagonal.mp hp
  rw [step123Class_count]
  by_cases h1 : p.1 = 1
  · have hp_eq : p = (1, n + 2) := by
      ext <;> omega
    simp [hp_eq]
  · by_cases h2 : p.1 = 2
    · have hp_eq : p = (2, n + 1) := by
        ext <;> omega
      simp [hp_eq]
    · by_cases h3 : p.1 = 3
      · have hp_eq : p = (3, n) := by
          ext <;> omega
        simp [hp_eq]
      · have hp_ne1 : p ≠ (1, n + 2) := by
          intro hp_eq
          exact h1 (congrArg Prod.fst hp_eq)
        have hp_ne2 : p ≠ (2, n + 1) := by
          intro hp_eq
          exact h2 (congrArg Prod.fst hp_eq)
        have hp_ne3 : p ≠ (3, n) := by
          intro hp_eq
          exact h3 (congrArg Prod.fst hp_eq)
        simp [h1, h2, h3, hp_ne1, hp_ne2, hp_ne3]

/-- Tribonacci recurrence for compositions into parts 1, 2, and 3. -/
private lemma tribClass_count_succ_succ_succ (n : ℕ) :
    tribClass.count (n + 3) =
      tribClass.count (n + 2) + tribClass.count (n + 1) + tribClass.count n := by
  change (seqClass step123Class step123Class_count_zero).count ((n + 2) + 1) =
    tribClass.count (n + 2) + tribClass.count (n + 1) + tribClass.count n
  rw [seqClass.count_succ]
  rw [show (n + 2) + 1 = n + 3 by omega]
  calc
    ∑ p ∈ Finset.antidiagonal (n + 3), step123Class.count p.1 * tribClass.count p.2
        = ∑ p ∈ Finset.antidiagonal (n + 3),
            ((if p = (1, n + 2) then tribClass.count (n + 2) else 0) +
              (if p = (2, n + 1) then tribClass.count (n + 1) else 0) +
                (if p = (3, n) then tribClass.count n else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact step123Class_mul_count_eq n p hp
    _ = (∑ p ∈ Finset.antidiagonal (n + 3),
            if p = (1, n + 2) then tribClass.count (n + 2) else 0) +
          (∑ p ∈ Finset.antidiagonal (n + 3),
            if p = (2, n + 1) then tribClass.count (n + 1) else 0) +
          (∑ p ∈ Finset.antidiagonal (n + 3),
            if p = (3, n) then tribClass.count n else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = tribClass.count (n + 2) + tribClass.count (n + 1) + tribClass.count n := by
          have hmem1 : (1, n + 2) ∈ Finset.antidiagonal (n + 3) := by
            rw [Finset.mem_antidiagonal]
            omega
          have hmem2 : (2, n + 1) ∈ Finset.antidiagonal (n + 3) := by
            rw [Finset.mem_antidiagonal]
            omega
          have hmem3 : (3, n) ∈ Finset.antidiagonal (n + 3) := by
            rw [Finset.mem_antidiagonal]
            omega
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp [hmem1, hmem2, hmem3]

/-! Sanity checks: 1, 1, 2, 4, 7, 13, 24, 44. -/
example : tribClass.count 0 = 1 := by
  calc
    tribClass.count 0 = 1 := tribClass_count_zero
    _ = 1 := by decide

example : tribClass.count 1 = 1 := by
  calc
    tribClass.count 1 = 1 := tribClass_count_one
    _ = 1 := by decide

example : tribClass.count 2 = 2 := by
  calc
    tribClass.count 2 = 2 := tribClass_count_two
    _ = 2 := by decide

example : tribClass.count 3 = 4 := by
  calc
    tribClass.count 3 = tribClass.count 2 + tribClass.count 1 + tribClass.count 0 :=
      tribClass_count_succ_succ_succ 0
    _ = 2 + 1 + 1 := by rw [tribClass_count_two, tribClass_count_one, tribClass_count_zero]
    _ = 4 := by decide

example : tribClass.count 4 = 7 := by
  calc
    tribClass.count 4 = tribClass.count 3 + tribClass.count 2 + tribClass.count 1 :=
      tribClass_count_succ_succ_succ 1
    _ = (2 + 1 + 1) + 2 + 1 := by
      rw [tribClass_count_succ_succ_succ, tribClass_count_two, tribClass_count_one,
        tribClass_count_zero]
    _ = 7 := by decide

example : tribClass.count 5 = 13 := by
  calc
    tribClass.count 5 = tribClass.count 4 + tribClass.count 3 + tribClass.count 2 :=
      tribClass_count_succ_succ_succ 2
    _ = ((2 + 1 + 1) + 2 + 1) + (2 + 1 + 1) + 2 := by
      rw [tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_two, tribClass_count_one, tribClass_count_zero]
    _ = 13 := by decide

example : tribClass.count 6 = 24 := by
  calc
    tribClass.count 6 = tribClass.count 5 + tribClass.count 4 + tribClass.count 3 :=
      tribClass_count_succ_succ_succ 3
    _ = (((2 + 1 + 1) + 2 + 1) + (2 + 1 + 1) + 2) +
        ((2 + 1 + 1) + 2 + 1) + (2 + 1 + 1) := by
      rw [tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_two, tribClass_count_one,
        tribClass_count_zero]
    _ = 24 := by decide

example : tribClass.count 7 = 44 := by
  calc
    tribClass.count 7 = tribClass.count 6 + tribClass.count 5 + tribClass.count 4 :=
      tribClass_count_succ_succ_succ 4
    _ = ((((2 + 1 + 1) + 2 + 1) + (2 + 1 + 1) + 2) +
        ((2 + 1 + 1) + 2 + 1) + (2 + 1 + 1)) +
        (((2 + 1 + 1) + 2 + 1) + (2 + 1 + 1) + 2) +
        ((2 + 1 + 1) + 2 + 1) := by
      rw [tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_two, tribClass_count_one, tribClass_count_zero]
    _ = 44 := by decide

/-- The OGF for a single part of size 1, 2, or 3 is `z + z^2 + z^3`. -/
private lemma step123Class_ogfZ :
    ogfZ step123Class = PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 := by
  ext n
  rw [show coeff n (ogfZ step123Class) = (step123Class.count n : ℤ) by
    simp [ogfZ, coeff_ogf]]
  rw [step123Class_count]
  simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  by_cases h1 : n = 1
  · simp [h1]
  · by_cases h2 : n = 2
    · simp [h2]
    · by_cases h3 : n = 3
      · simp [h3]
      · simp [h1, h2, h3]

/-- Closed form for the OGF of compositions into parts of size 1, 2, or 3. -/
theorem tribClass_ogfZ_mul_one_sub_X_sub_X_sq_sub_X_cub :
    ogfZ tribClass *
      (1 - PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3) = 1 := by
  have hseq := seqClass_ogf_eq step123Class step123Class_count_zero
  change (1 - ogfZ step123Class) * ogfZ tribClass = 1 at hseq
  rw [step123Class_ogfZ] at hseq
  calc
    ogfZ tribClass *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3)
        = (1 - (PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3)) *
            ogfZ tribClass := by ring
    _ = 1 := hseq

/-- Tribonacci recurrence for compositions into parts 1, 2, and 3. -/
theorem tribClass_count_recurrence (n : ℕ) :
    tribClass.count (n + 3) =
      tribClass.count (n + 2) + tribClass.count (n + 1) + tribClass.count n := by
  exact tribClass_count_succ_succ_succ n
