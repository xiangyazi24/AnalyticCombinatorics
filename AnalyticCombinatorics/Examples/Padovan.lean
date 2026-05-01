/-
  Analytic Combinatorics — Examples
  Padovan compositions

  Compositions of n into parts of size 2 or 3.
-/
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences

open PowerSeries CombinatorialClass Finset

/-- The atom class for parts of size 2 or 3. -/
noncomputable def step23Class : CombinatorialClass :=
  (atomOfSize 2).disjSum (atomOfSize 3)

/-- step23Class has no size-0 part. -/
theorem step23Class_count_zero : step23Class.count 0 = 0 := by
  unfold step23Class
  rw [CombinatorialClass.disjSum_count, atomOfSize_count, atomOfSize_count]
  decide

/-- Compositions into parts of size 2 or 3. -/
noncomputable def padovanClass : CombinatorialClass :=
  seqClass step23Class step23Class_count_zero

private lemma step23Class_count (k : ℕ) :
    step23Class.count k = if k = 2 then 1 else if k = 3 then 1 else 0 := by
  unfold step23Class
  rw [CombinatorialClass.disjSum_count, atomOfSize_count, atomOfSize_count]
  by_cases h2 : k = 2
  · simp [h2]
  · by_cases h3 : k = 3
    · simp [h3]
    · simp [h2, h3]

/-- The empty composition is the unique composition of 0. -/
theorem padovanClass_count_zero : padovanClass.count 0 = 1 := by
  change (seqClass step23Class step23Class_count_zero).count 0 = 1
  rw [seqClass.count_zero]

/-- There are no compositions of 1 into parts 2 and 3. -/
private lemma padovanClass_count_one : padovanClass.count 1 = 0 := by
  change (seqClass step23Class step23Class_count_zero).count (0 + 1) = 0
  rw [seqClass.count_succ]
  apply Finset.sum_eq_zero
  intro p hp
  have hp_sum : p.1 + p.2 = 1 := Finset.mem_antidiagonal.mp hp
  rw [step23Class_count]
  have h2 : p.1 ≠ 2 := by omega
  have h3 : p.1 ≠ 3 := by omega
  simp [h2, h3]

/-- The only composition of 2 is `[2]`. -/
private lemma padovanClass_count_two : padovanClass.count 2 = 1 := by
  change (seqClass step23Class step23Class_count_zero).count (1 + 1) = 1
  rw [seqClass.count_succ]
  rw [Finset.sum_eq_single_of_mem (2, 0)]
  · rw [step23Class_count, seqClass.count_zero]
    simp
  · rw [Finset.mem_antidiagonal]
    omega
  · intro p hp hp_ne
    have hp_sum : p.1 + p.2 = 2 := Finset.mem_antidiagonal.mp hp
    rw [step23Class_count]
    by_cases h2 : p.1 = 2
    · have hp_eq : p = (2, 0) := by
        ext <;> omega
      exact (hp_ne hp_eq).elim
    · have h3 : p.1 ≠ 3 := by omega
      simp [h2, h3]

private lemma step23Class_mul_count_eq (n : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ Finset.antidiagonal (n + 3)) :
    step23Class.count p.1 * padovanClass.count p.2 =
      (if p = (2, n + 1) then padovanClass.count (n + 1) else 0) +
        (if p = (3, n) then padovanClass.count n else 0) := by
  have hp_sum : p.1 + p.2 = n + 3 := Finset.mem_antidiagonal.mp hp
  rw [step23Class_count]
  by_cases h2 : p.1 = 2
  · have hp_eq : p = (2, n + 1) := by
      ext <;> omega
    simp [hp_eq]
  · by_cases h3 : p.1 = 3
    · have hp_eq : p = (3, n) := by
        ext <;> omega
      simp [hp_eq]
    · have hp_ne2 : p ≠ (2, n + 1) := by
        intro hp_eq
        exact h2 (congrArg Prod.fst hp_eq)
      have hp_ne3 : p ≠ (3, n) := by
        intro hp_eq
        exact h3 (congrArg Prod.fst hp_eq)
      simp [h2, h3, hp_ne2, hp_ne3]

/-- Padovan recurrence for compositions into parts 2 and 3. -/
private lemma padovanClass_count_succ_succ_succ (n : ℕ) :
    padovanClass.count (n + 3) =
      padovanClass.count (n + 1) + padovanClass.count n := by
  change (seqClass step23Class step23Class_count_zero).count ((n + 2) + 1) =
    padovanClass.count (n + 1) + padovanClass.count n
  rw [seqClass.count_succ]
  rw [show (n + 2) + 1 = n + 3 by omega]
  calc
    ∑ p ∈ Finset.antidiagonal (n + 3), step23Class.count p.1 * padovanClass.count p.2
        = ∑ p ∈ Finset.antidiagonal (n + 3),
            ((if p = (2, n + 1) then padovanClass.count (n + 1) else 0) +
              (if p = (3, n) then padovanClass.count n else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact step23Class_mul_count_eq n p hp
    _ = (∑ p ∈ Finset.antidiagonal (n + 3),
            if p = (2, n + 1) then padovanClass.count (n + 1) else 0) +
          (∑ p ∈ Finset.antidiagonal (n + 3),
            if p = (3, n) then padovanClass.count n else 0) := by
          rw [Finset.sum_add_distrib]
    _ = padovanClass.count (n + 1) + padovanClass.count n := by
          have hmem2 : (2, n + 1) ∈ Finset.antidiagonal (n + 3) := by
            rw [Finset.mem_antidiagonal]
            omega
          have hmem3 : (3, n) ∈ Finset.antidiagonal (n + 3) := by
            rw [Finset.mem_antidiagonal]
            omega
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp [hmem2, hmem3]

private lemma padovanClass_count_three : padovanClass.count 3 = 1 := by
  calc
    padovanClass.count 3 = padovanClass.count 1 + padovanClass.count 0 :=
      padovanClass_count_succ_succ_succ 0
    _ = 0 + 1 := by rw [padovanClass_count_one, padovanClass_count_zero]
    _ = 1 := by decide

private lemma padovanClass_count_four : padovanClass.count 4 = 1 := by
  calc
    padovanClass.count 4 = padovanClass.count 2 + padovanClass.count 1 :=
      padovanClass_count_succ_succ_succ 1
    _ = 1 + 0 := by rw [padovanClass_count_two, padovanClass_count_one]
    _ = 1 := by decide

private lemma padovanClass_count_five : padovanClass.count 5 = 2 := by
  calc
    padovanClass.count 5 = padovanClass.count 3 + padovanClass.count 2 :=
      padovanClass_count_succ_succ_succ 2
    _ = 1 + 1 := by rw [padovanClass_count_three, padovanClass_count_two]
    _ = 2 := by decide

private lemma padovanClass_count_six : padovanClass.count 6 = 2 := by
  calc
    padovanClass.count 6 = padovanClass.count 4 + padovanClass.count 3 :=
      padovanClass_count_succ_succ_succ 3
    _ = 1 + 1 := by rw [padovanClass_count_four, padovanClass_count_three]
    _ = 2 := by decide

private lemma padovanClass_count_seven : padovanClass.count 7 = 3 := by
  calc
    padovanClass.count 7 = padovanClass.count 5 + padovanClass.count 4 :=
      padovanClass_count_succ_succ_succ 4
    _ = 2 + 1 := by rw [padovanClass_count_five, padovanClass_count_four]
    _ = 3 := by decide

private lemma padovanClass_count_eight : padovanClass.count 8 = 4 := by
  calc
    padovanClass.count 8 = padovanClass.count 6 + padovanClass.count 5 :=
      padovanClass_count_succ_succ_succ 5
    _ = 2 + 2 := by rw [padovanClass_count_six, padovanClass_count_five]
    _ = 4 := by decide

private lemma padovanClass_count_nine : padovanClass.count 9 = 5 := by
  calc
    padovanClass.count 9 = padovanClass.count 7 + padovanClass.count 6 :=
      padovanClass_count_succ_succ_succ 6
    _ = 3 + 2 := by rw [padovanClass_count_seven, padovanClass_count_six]
    _ = 5 := by decide

private lemma padovanClass_count_ten : padovanClass.count 10 = 7 := by
  calc
    padovanClass.count 10 = padovanClass.count 8 + padovanClass.count 7 :=
      padovanClass_count_succ_succ_succ 7
    _ = 4 + 3 := by rw [padovanClass_count_eight, padovanClass_count_seven]
    _ = 7 := by decide

/-! Sanity checks: 1, 0, 1, 1, 1, 2, 2, 3, 4, 5, 7. -/
example : padovanClass.count 0 = 1 := by
  calc
    padovanClass.count 0 = 1 := padovanClass_count_zero
    _ = 1 := by decide

example : padovanClass.count 1 = 0 := by
  calc
    padovanClass.count 1 = 0 := padovanClass_count_one
    _ = 0 := by decide

example : padovanClass.count 2 = 1 := by
  calc
    padovanClass.count 2 = 1 := padovanClass_count_two
    _ = 1 := by decide

example : padovanClass.count 3 = 1 := by
  calc
    padovanClass.count 3 = 1 := padovanClass_count_three
    _ = 1 := by decide

example : padovanClass.count 4 = 1 := by
  calc
    padovanClass.count 4 = 1 := padovanClass_count_four
    _ = 1 := by decide

example : padovanClass.count 5 = 2 := by
  calc
    padovanClass.count 5 = 2 := padovanClass_count_five
    _ = 2 := by decide

example : padovanClass.count 6 = 2 := by
  calc
    padovanClass.count 6 = 2 := padovanClass_count_six
    _ = 2 := by decide

example : padovanClass.count 7 = 3 := by
  calc
    padovanClass.count 7 = 3 := padovanClass_count_seven
    _ = 3 := by decide

example : padovanClass.count 8 = 4 := by
  calc
    padovanClass.count 8 = 4 := padovanClass_count_eight
    _ = 4 := by decide

example : padovanClass.count 9 = 5 := by
  calc
    padovanClass.count 9 = 5 := padovanClass_count_nine
    _ = 5 := by decide

example : padovanClass.count 10 = 7 := by
  calc
    padovanClass.count 10 = 7 := padovanClass_count_ten
    _ = 7 := by decide

/-- The OGF for a single part of size 2 or 3 is `z^2 + z^3`. -/
private lemma step23Class_ogfZ :
    ogfZ step23Class = PowerSeries.X ^ 2 + PowerSeries.X ^ 3 := by
  ext n
  rw [show coeff n (ogfZ step23Class) = (step23Class.count n : ℤ) by
    simp [ogfZ, coeff_ogf]]
  rw [step23Class_count]
  simp [PowerSeries.coeff_X_pow]
  by_cases h2 : n = 2
  · simp [h2]
  · by_cases h3 : n = 3
    · simp [h3]
    · simp [h2, h3]

/-- Closed form for the OGF of compositions into parts of size 2 or 3. -/
theorem padovanClass_ogfZ_mul_one_sub_X_sq_sub_X_cub :
    ogfZ padovanClass * (1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3) = 1 := by
  have hseq := seqClass_ogf_eq step23Class step23Class_count_zero
  change (1 - ogfZ step23Class) * ogfZ padovanClass = 1 at hseq
  rw [step23Class_ogfZ] at hseq
  calc
    ogfZ padovanClass * (1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3)
        = (1 - (PowerSeries.X ^ 2 + PowerSeries.X ^ 3)) * ogfZ padovanClass := by ring
    _ = 1 := hseq
