/-
  Analytic Combinatorics — Examples
  Tetranacci compositions

  Compositions of n into parts of size 1, 2, 3, or 4.
-/
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences

open PowerSeries CombinatorialClass Finset

/-- The atom class for parts of size 1, 2, 3, or 4. -/
noncomputable def step1234Class : CombinatorialClass :=
  (((atomOfSize 1).disjSum (atomOfSize 2)).disjSum (atomOfSize 3)).disjSum
    (atomOfSize 4)

/-- step1234Class has no size-0 part. -/
theorem step1234Class_count_zero : step1234Class.count 0 = 0 := by
  unfold step1234Class
  rw [CombinatorialClass.disjSum_count, CombinatorialClass.disjSum_count,
    CombinatorialClass.disjSum_count, atomOfSize_count, atomOfSize_count,
    atomOfSize_count, atomOfSize_count]
  decide

/-- Compositions into parts of size 1, 2, 3, or 4. -/
noncomputable def tetraClass : CombinatorialClass :=
  seqClass step1234Class step1234Class_count_zero

private lemma step1234Class_count (k : ℕ) :
    step1234Class.count k =
      if k = 1 then 1 else if k = 2 then 1 else if k = 3 then 1 else
        if k = 4 then 1 else 0 := by
  unfold step1234Class
  rw [CombinatorialClass.disjSum_count, CombinatorialClass.disjSum_count,
    CombinatorialClass.disjSum_count, atomOfSize_count, atomOfSize_count,
    atomOfSize_count, atomOfSize_count]
  by_cases h1 : k = 1
  · simp [h1]
  · by_cases h2 : k = 2
    · simp [h2]
    · by_cases h3 : k = 3
      · simp [h3]
      · by_cases h4 : k = 4
        · simp [h4]
        · simp [h1, h2, h3, h4]

/-- The empty composition is the unique composition of 0. -/
theorem tetraClass_count_zero : tetraClass.count 0 = 1 := by
  change (seqClass step1234Class step1234Class_count_zero).count 0 = 1
  rw [seqClass.count_zero]

private lemma tetraClass_count_one : tetraClass.count 1 = 1 := by
  change (seqClass step1234Class step1234Class_count_zero).count (0 + 1) = 1
  rw [seqClass.count_succ]
  rw [Finset.sum_eq_single_of_mem (1, 0)]
  · rw [step1234Class_count, seqClass.count_zero]
    simp
  · rw [Finset.mem_antidiagonal]
    omega
  · intro p hp hp_ne
    have hp_sum : p.1 + p.2 = 1 := Finset.mem_antidiagonal.mp hp
    rw [step1234Class_count]
    by_cases h1 : p.1 = 1
    · have hp_eq : p = (1, 0) := by
        ext <;> omega
      exact (hp_ne hp_eq).elim
    · have h2 : p.1 ≠ 2 := by omega
      have h3 : p.1 ≠ 3 := by omega
      have h4 : p.1 ≠ 4 := by omega
      simp [h1, h2, h3, h4]

private lemma tetraClass_count_two : tetraClass.count 2 = 2 := by
  change (seqClass step1234Class step1234Class_count_zero).count (1 + 1) = 2
  rw [seqClass.count_succ]
  calc
    ∑ p ∈ Finset.antidiagonal 2, step1234Class.count p.1 * tetraClass.count p.2
        = ∑ p ∈ Finset.antidiagonal 2,
            ((if p = (1, 1) then tetraClass.count 1 else 0) +
              (if p = (2, 0) then tetraClass.count 0 else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hp_sum : p.1 + p.2 = 2 := Finset.mem_antidiagonal.mp hp
          rw [step1234Class_count]
          by_cases h1 : p.1 = 1
          · have hp_eq : p = (1, 1) := by
              ext <;> omega
            simp [hp_eq]
          · by_cases h2 : p.1 = 2
            · have hp_eq : p = (2, 0) := by
                ext <;> omega
              simp [hp_eq]
            · have h3 : p.1 ≠ 3 := by omega
              have h4 : p.1 ≠ 4 := by omega
              have hp_ne1 : p ≠ (1, 1) := by
                intro hp_eq
                exact h1 (congrArg Prod.fst hp_eq)
              have hp_ne2 : p ≠ (2, 0) := by
                intro hp_eq
                exact h2 (congrArg Prod.fst hp_eq)
              simp [h1, h2, h3, h4, hp_ne1, hp_ne2]
    _ = (∑ p ∈ Finset.antidiagonal 2,
            if p = (1, 1) then tetraClass.count 1 else 0) +
          (∑ p ∈ Finset.antidiagonal 2,
            if p = (2, 0) then tetraClass.count 0 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = tetraClass.count 1 + tetraClass.count 0 := by
          have hmem1 : (1, 1) ∈ Finset.antidiagonal 2 := by
            rw [Finset.mem_antidiagonal]
            decide
          have hmem2 : (2, 0) ∈ Finset.antidiagonal 2 := by
            rw [Finset.mem_antidiagonal]
            decide
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp [hmem1, hmem2]
    _ = 2 := by
          rw [tetraClass_count_one, tetraClass_count_zero]

private lemma tetraClass_count_three : tetraClass.count 3 = 4 := by
  change (seqClass step1234Class step1234Class_count_zero).count (2 + 1) = 4
  rw [seqClass.count_succ]
  calc
    ∑ p ∈ Finset.antidiagonal 3, step1234Class.count p.1 * tetraClass.count p.2
        = ∑ p ∈ Finset.antidiagonal 3,
            ((if p = (1, 2) then tetraClass.count 2 else 0) +
              (if p = (2, 1) then tetraClass.count 1 else 0) +
                (if p = (3, 0) then tetraClass.count 0 else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hp_sum : p.1 + p.2 = 3 := Finset.mem_antidiagonal.mp hp
          rw [step1234Class_count]
          by_cases h1 : p.1 = 1
          · have hp_eq : p = (1, 2) := by
              ext <;> omega
            simp [hp_eq]
          · by_cases h2 : p.1 = 2
            · have hp_eq : p = (2, 1) := by
                ext <;> omega
              simp [hp_eq]
            · by_cases h3 : p.1 = 3
              · have hp_eq : p = (3, 0) := by
                  ext <;> omega
                simp [hp_eq]
              · have h4 : p.1 ≠ 4 := by omega
                have hp_ne1 : p ≠ (1, 2) := by
                  intro hp_eq
                  exact h1 (congrArg Prod.fst hp_eq)
                have hp_ne2 : p ≠ (2, 1) := by
                  intro hp_eq
                  exact h2 (congrArg Prod.fst hp_eq)
                have hp_ne3 : p ≠ (3, 0) := by
                  intro hp_eq
                  exact h3 (congrArg Prod.fst hp_eq)
                simp [h1, h2, h3, h4, hp_ne1, hp_ne2, hp_ne3]
    _ = (∑ p ∈ Finset.antidiagonal 3,
            if p = (1, 2) then tetraClass.count 2 else 0) +
          (∑ p ∈ Finset.antidiagonal 3,
            if p = (2, 1) then tetraClass.count 1 else 0) +
          (∑ p ∈ Finset.antidiagonal 3,
            if p = (3, 0) then tetraClass.count 0 else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = tetraClass.count 2 + tetraClass.count 1 + tetraClass.count 0 := by
          have hmem1 : (1, 2) ∈ Finset.antidiagonal 3 := by
            rw [Finset.mem_antidiagonal]
            decide
          have hmem2 : (2, 1) ∈ Finset.antidiagonal 3 := by
            rw [Finset.mem_antidiagonal]
            decide
          have hmem3 : (3, 0) ∈ Finset.antidiagonal 3 := by
            rw [Finset.mem_antidiagonal]
            decide
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp [hmem1, hmem2, hmem3]
    _ = 4 := by
          rw [tetraClass_count_two, tetraClass_count_one, tetraClass_count_zero]

private lemma step1234Class_mul_count_eq (n : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ Finset.antidiagonal (n + 4)) :
    step1234Class.count p.1 * tetraClass.count p.2 =
      (if p = (1, n + 3) then tetraClass.count (n + 3) else 0) +
        (if p = (2, n + 2) then tetraClass.count (n + 2) else 0) +
          (if p = (3, n + 1) then tetraClass.count (n + 1) else 0) +
            (if p = (4, n) then tetraClass.count n else 0) := by
  have hp_sum : p.1 + p.2 = n + 4 := Finset.mem_antidiagonal.mp hp
  rw [step1234Class_count]
  by_cases h1 : p.1 = 1
  · have hp_eq : p = (1, n + 3) := by
      ext <;> omega
    simp [hp_eq]
  · by_cases h2 : p.1 = 2
    · have hp_eq : p = (2, n + 2) := by
        ext <;> omega
      simp [hp_eq]
    · by_cases h3 : p.1 = 3
      · have hp_eq : p = (3, n + 1) := by
          ext <;> omega
        simp [hp_eq]
      · by_cases h4 : p.1 = 4
        · have hp_eq : p = (4, n) := by
            ext <;> omega
          simp [hp_eq]
        · have hp_ne1 : p ≠ (1, n + 3) := by
            intro hp_eq
            exact h1 (congrArg Prod.fst hp_eq)
          have hp_ne2 : p ≠ (2, n + 2) := by
            intro hp_eq
            exact h2 (congrArg Prod.fst hp_eq)
          have hp_ne3 : p ≠ (3, n + 1) := by
            intro hp_eq
            exact h3 (congrArg Prod.fst hp_eq)
          have hp_ne4 : p ≠ (4, n) := by
            intro hp_eq
            exact h4 (congrArg Prod.fst hp_eq)
          simp [h1, h2, h3, h4, hp_ne1, hp_ne2, hp_ne3, hp_ne4]

/-- Tetranacci recurrence for compositions into parts 1, 2, 3, and 4. -/
private lemma tetraClass_count_succ_succ_succ_succ (n : ℕ) :
    tetraClass.count (n + 4) =
      tetraClass.count (n + 3) + tetraClass.count (n + 2) +
        tetraClass.count (n + 1) + tetraClass.count n := by
  change (seqClass step1234Class step1234Class_count_zero).count ((n + 3) + 1) =
    tetraClass.count (n + 3) + tetraClass.count (n + 2) +
      tetraClass.count (n + 1) + tetraClass.count n
  rw [seqClass.count_succ]
  rw [show (n + 3) + 1 = n + 4 by omega]
  calc
    ∑ p ∈ Finset.antidiagonal (n + 4), step1234Class.count p.1 * tetraClass.count p.2
        = ∑ p ∈ Finset.antidiagonal (n + 4),
            ((if p = (1, n + 3) then tetraClass.count (n + 3) else 0) +
              (if p = (2, n + 2) then tetraClass.count (n + 2) else 0) +
                (if p = (3, n + 1) then tetraClass.count (n + 1) else 0) +
                  (if p = (4, n) then tetraClass.count n else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact step1234Class_mul_count_eq n p hp
    _ = (∑ p ∈ Finset.antidiagonal (n + 4),
            if p = (1, n + 3) then tetraClass.count (n + 3) else 0) +
          (∑ p ∈ Finset.antidiagonal (n + 4),
            if p = (2, n + 2) then tetraClass.count (n + 2) else 0) +
          (∑ p ∈ Finset.antidiagonal (n + 4),
            if p = (3, n + 1) then tetraClass.count (n + 1) else 0) +
          (∑ p ∈ Finset.antidiagonal (n + 4),
            if p = (4, n) then tetraClass.count n else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = tetraClass.count (n + 3) + tetraClass.count (n + 2) +
          tetraClass.count (n + 1) + tetraClass.count n := by
          have hmem1 : (1, n + 3) ∈ Finset.antidiagonal (n + 4) := by
            rw [Finset.mem_antidiagonal]
            omega
          have hmem2 : (2, n + 2) ∈ Finset.antidiagonal (n + 4) := by
            rw [Finset.mem_antidiagonal]
            omega
          have hmem3 : (3, n + 1) ∈ Finset.antidiagonal (n + 4) := by
            rw [Finset.mem_antidiagonal]
            omega
          have hmem4 : (4, n) ∈ Finset.antidiagonal (n + 4) := by
            rw [Finset.mem_antidiagonal]
            omega
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq',
            Finset.sum_ite_eq']
          simp [hmem1, hmem2, hmem3, hmem4]

private lemma tetraClass_count_four : tetraClass.count 4 = 8 := by
  calc
    tetraClass.count 4 =
        tetraClass.count 3 + tetraClass.count 2 + tetraClass.count 1 + tetraClass.count 0 :=
      tetraClass_count_succ_succ_succ_succ 0
    _ = 4 + 2 + 1 + 1 := by
      rw [tetraClass_count_three, tetraClass_count_two, tetraClass_count_one,
        tetraClass_count_zero]
    _ = 8 := by decide

private lemma tetraClass_count_five : tetraClass.count 5 = 15 := by
  calc
    tetraClass.count 5 =
        tetraClass.count 4 + tetraClass.count 3 + tetraClass.count 2 + tetraClass.count 1 :=
      tetraClass_count_succ_succ_succ_succ 1
    _ = 8 + 4 + 2 + 1 := by
      rw [tetraClass_count_four, tetraClass_count_three, tetraClass_count_two,
        tetraClass_count_one]
    _ = 15 := by decide

private lemma tetraClass_count_six : tetraClass.count 6 = 29 := by
  calc
    tetraClass.count 6 =
        tetraClass.count 5 + tetraClass.count 4 + tetraClass.count 3 + tetraClass.count 2 :=
      tetraClass_count_succ_succ_succ_succ 2
    _ = 15 + 8 + 4 + 2 := by
      rw [tetraClass_count_five, tetraClass_count_four, tetraClass_count_three,
        tetraClass_count_two]
    _ = 29 := by decide

private lemma tetraClass_count_seven : tetraClass.count 7 = 56 := by
  calc
    tetraClass.count 7 =
        tetraClass.count 6 + tetraClass.count 5 + tetraClass.count 4 + tetraClass.count 3 :=
      tetraClass_count_succ_succ_succ_succ 3
    _ = 29 + 15 + 8 + 4 := by
      rw [tetraClass_count_six, tetraClass_count_five, tetraClass_count_four,
        tetraClass_count_three]
    _ = 56 := by decide

private lemma tetraClass_count_eight : tetraClass.count 8 = 108 := by
  calc
    tetraClass.count 8 =
        tetraClass.count 7 + tetraClass.count 6 + tetraClass.count 5 + tetraClass.count 4 :=
      tetraClass_count_succ_succ_succ_succ 4
    _ = 56 + 29 + 15 + 8 := by
      rw [tetraClass_count_seven, tetraClass_count_six, tetraClass_count_five,
        tetraClass_count_four]
    _ = 108 := by decide

/-! Sanity checks: 1, 1, 2, 4, 8, 15, 29, 56, 108. -/
example : tetraClass.count 0 = 1 := by
  calc
    tetraClass.count 0 = 1 := tetraClass_count_zero
    _ = 1 := by decide

example : tetraClass.count 1 = 1 := by
  calc
    tetraClass.count 1 = 1 := tetraClass_count_one
    _ = 1 := by decide

example : tetraClass.count 2 = 2 := by
  calc
    tetraClass.count 2 = 2 := tetraClass_count_two
    _ = 2 := by decide

example : tetraClass.count 3 = 4 := by
  calc
    tetraClass.count 3 = 4 := tetraClass_count_three
    _ = 4 := by decide

example : tetraClass.count 4 = 8 := by
  calc
    tetraClass.count 4 = 8 := tetraClass_count_four
    _ = 8 := by decide

example : tetraClass.count 5 = 15 := by
  calc
    tetraClass.count 5 = 15 := tetraClass_count_five
    _ = 15 := by decide

example : tetraClass.count 6 = 29 := by
  calc
    tetraClass.count 6 = 29 := tetraClass_count_six
    _ = 29 := by decide

example : tetraClass.count 7 = 56 := by
  calc
    tetraClass.count 7 = 56 := tetraClass_count_seven
    _ = 56 := by decide

example : tetraClass.count 8 = 108 := by
  calc
    tetraClass.count 8 = 108 := tetraClass_count_eight
    _ = 108 := by decide

/-- The OGF for a single part of size 1, 2, 3, or 4 is `z + z^2 + z^3 + z^4`. -/
private lemma step1234Class_ogfZ :
    ogfZ step1234Class =
      PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + PowerSeries.X ^ 4 := by
  ext n
  rw [show coeff n (ogfZ step1234Class) = (step1234Class.count n : ℤ) by
    simp [ogfZ, coeff_ogf]]
  rw [step1234Class_count]
  simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  by_cases h1 : n = 1
  · simp [h1]
  · by_cases h2 : n = 2
    · simp [h2]
    · by_cases h3 : n = 3
      · simp [h3]
      · by_cases h4 : n = 4
        · simp [h4]
        · simp [h1, h2, h3, h4]

/-- Closed form for the OGF of compositions into parts of size 1, 2, 3, or 4. -/
theorem tetraClass_ogfZ_mul_one_sub_X_sub_X_sq_sub_X_cub_sub_X_fourth :
    ogfZ tetraClass *
      (1 - PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 - PowerSeries.X ^ 4) =
        1 := by
  have hseq := seqClass_ogf_eq step1234Class step1234Class_count_zero
  change (1 - ogfZ step1234Class) * ogfZ tetraClass = 1 at hseq
  rw [step1234Class_ogfZ] at hseq
  calc
    ogfZ tetraClass *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 - PowerSeries.X ^ 4)
        = (1 - (PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 +
            PowerSeries.X ^ 4)) * ogfZ tetraClass := by ring
    _ = 1 := hseq

/-- Tetranacci recurrence for compositions into parts 1, 2, 3, and 4. -/
theorem tetraClass_count_recurrence (n : ℕ) :
    tetraClass.count (n + 4)
      = tetraClass.count (n + 3) + tetraClass.count (n + 2)
        + tetraClass.count (n + 1) + tetraClass.count n := by
  exact tetraClass_count_succ_succ_succ_succ n
