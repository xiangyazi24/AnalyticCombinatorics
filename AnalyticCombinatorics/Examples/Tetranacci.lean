/-
  Analytic Combinatorics — Examples
  Tetranacci compositions

  Compositions of n into parts of size 1, 2, 3, or 4.
-/
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import AnalyticCombinatorics.PartA.Ch3.Parameters

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

private lemma tetraClass_count_nine : tetraClass.count 9 = 208 := by
  calc
    tetraClass.count 9 =
        tetraClass.count 8 + tetraClass.count 7 + tetraClass.count 6 + tetraClass.count 5 :=
      tetraClass_count_succ_succ_succ_succ 5
    _ = 108 + 56 + 29 + 15 := by
      rw [tetraClass_count_eight, tetraClass_count_seven, tetraClass_count_six,
        tetraClass_count_five]
    _ = 208 := by decide

private lemma tetraClass_count_ten : tetraClass.count 10 = 401 := by
  calc
    tetraClass.count 10 =
        tetraClass.count 9 + tetraClass.count 8 + tetraClass.count 7 + tetraClass.count 6 :=
      tetraClass_count_succ_succ_succ_succ 6
    _ = 208 + 108 + 56 + 29 := by
      rw [tetraClass_count_nine, tetraClass_count_eight, tetraClass_count_seven,
        tetraClass_count_six]
    _ = 401 := by decide

private lemma tetraClass_count_eleven : tetraClass.count 11 = 773 := by
  calc
    tetraClass.count 11 =
        tetraClass.count 10 + tetraClass.count 9 + tetraClass.count 8 + tetraClass.count 7 :=
      tetraClass_count_succ_succ_succ_succ 7
    _ = 401 + 208 + 108 + 56 := by
      rw [tetraClass_count_ten, tetraClass_count_nine, tetraClass_count_eight,
        tetraClass_count_seven]
    _ = 773 := by decide

private lemma tetraClass_count_twelve : tetraClass.count 12 = 1490 := by
  calc
    tetraClass.count 12 =
        tetraClass.count 11 + tetraClass.count 10 + tetraClass.count 9 + tetraClass.count 8 :=
      tetraClass_count_succ_succ_succ_succ 8
    _ = 773 + 401 + 208 + 108 := by
      rw [tetraClass_count_eleven, tetraClass_count_ten, tetraClass_count_nine,
        tetraClass_count_eight]
    _ = 1490 := by decide

private lemma tetraClass_count_thirteen : tetraClass.count 13 = 2872 := by
  calc
    tetraClass.count 13 =
        tetraClass.count 12 + tetraClass.count 11 + tetraClass.count 10 + tetraClass.count 9 :=
      tetraClass_count_succ_succ_succ_succ 9
    _ = 1490 + 773 + 401 + 208 := by
      rw [tetraClass_count_twelve, tetraClass_count_eleven, tetraClass_count_ten,
        tetraClass_count_nine]
    _ = 2872 := by decide

private lemma tetraClass_count_fourteen : tetraClass.count 14 = 5536 := by
  calc
    tetraClass.count 14 =
        tetraClass.count 13 + tetraClass.count 12 + tetraClass.count 11 + tetraClass.count 10 :=
      tetraClass_count_succ_succ_succ_succ 10
    _ = 2872 + 1490 + 773 + 401 := by
      rw [tetraClass_count_thirteen, tetraClass_count_twelve, tetraClass_count_eleven,
        tetraClass_count_ten]
    _ = 5536 := by decide

private lemma tetraClass_count_fifteen : tetraClass.count 15 = 10671 := by
  calc
    tetraClass.count 15 =
        tetraClass.count 14 + tetraClass.count 13 + tetraClass.count 12 + tetraClass.count 11 :=
      tetraClass_count_succ_succ_succ_succ 11
    _ = 5536 + 2872 + 1490 + 773 := by
      rw [tetraClass_count_fourteen, tetraClass_count_thirteen, tetraClass_count_twelve,
        tetraClass_count_eleven]
    _ = 10671 := by decide

private lemma tetraClass_count_sixteen : tetraClass.count 16 = 20569 := by
  calc
    tetraClass.count 16 =
        tetraClass.count 15 + tetraClass.count 14 + tetraClass.count 13 + tetraClass.count 12 :=
      tetraClass_count_succ_succ_succ_succ 12
    _ = 10671 + 5536 + 2872 + 1490 := by
      rw [tetraClass_count_fifteen, tetraClass_count_fourteen, tetraClass_count_thirteen,
        tetraClass_count_twelve]
    _ = 20569 := by decide

private lemma tetraClass_count_seventeen : tetraClass.count 17 = 39648 := by
  calc
    tetraClass.count 17 =
        tetraClass.count 16 + tetraClass.count 15 + tetraClass.count 14 + tetraClass.count 13 :=
      tetraClass_count_succ_succ_succ_succ 13
    _ = 20569 + 10671 + 5536 + 2872 := by
      rw [tetraClass_count_sixteen, tetraClass_count_fifteen, tetraClass_count_fourteen,
        tetraClass_count_thirteen]
    _ = 39648 := by decide

private lemma tetraClass_count_eighteen : tetraClass.count 18 = 76424 := by
  calc
    tetraClass.count 18 =
        tetraClass.count 17 + tetraClass.count 16 + tetraClass.count 15 + tetraClass.count 14 :=
      tetraClass_count_succ_succ_succ_succ 14
    _ = 39648 + 20569 + 10671 + 5536 := by
      rw [tetraClass_count_seventeen, tetraClass_count_sixteen, tetraClass_count_fifteen,
        tetraClass_count_fourteen]
    _ = 76424 := by decide

private lemma tetraClass_count_nineteen : tetraClass.count 19 = 147312 := by
  calc
    tetraClass.count 19 =
        tetraClass.count 18 + tetraClass.count 17 + tetraClass.count 16 + tetraClass.count 15 :=
      tetraClass_count_succ_succ_succ_succ 15
    _ = 76424 + 39648 + 20569 + 10671 := by
      rw [tetraClass_count_eighteen, tetraClass_count_seventeen, tetraClass_count_sixteen,
        tetraClass_count_fifteen]
    _ = 147312 := by decide

private lemma tetraClass_count_twenty : tetraClass.count 20 = 283953 := by
  calc
    tetraClass.count 20 =
        tetraClass.count 19 + tetraClass.count 18 + tetraClass.count 17 + tetraClass.count 16 :=
      tetraClass_count_succ_succ_succ_succ 16
    _ = 147312 + 76424 + 39648 + 20569 := by
      rw [tetraClass_count_nineteen, tetraClass_count_eighteen, tetraClass_count_seventeen,
        tetraClass_count_sixteen]
    _ = 283953 := by decide

private lemma tetraClass_count_twentyone : tetraClass.count 21 = 547337 := by
  calc
    tetraClass.count 21 =
        tetraClass.count 20 + tetraClass.count 19 + tetraClass.count 18 + tetraClass.count 17 :=
      tetraClass_count_succ_succ_succ_succ 17
    _ = 283953 + 147312 + 76424 + 39648 := by
      rw [tetraClass_count_twenty, tetraClass_count_nineteen, tetraClass_count_eighteen,
        tetraClass_count_seventeen]
    _ = 547337 := by decide

private lemma tetraClass_count_twentytwo : tetraClass.count 22 = 1055026 := by
  calc
    tetraClass.count 22 =
        tetraClass.count 21 + tetraClass.count 20 + tetraClass.count 19 + tetraClass.count 18 :=
      tetraClass_count_succ_succ_succ_succ 18
    _ = 547337 + 283953 + 147312 + 76424 := by
      rw [tetraClass_count_twentyone, tetraClass_count_twenty, tetraClass_count_nineteen,
        tetraClass_count_eighteen]
    _ = 1055026 := by decide

private lemma tetraClass_count_twentythree : tetraClass.count 23 = 2033628 := by
  calc
    tetraClass.count 23 =
        tetraClass.count 22 + tetraClass.count 21 + tetraClass.count 20 + tetraClass.count 19 :=
      tetraClass_count_succ_succ_succ_succ 19
    _ = 1055026 + 547337 + 283953 + 147312 := by
      rw [tetraClass_count_twentytwo, tetraClass_count_twentyone, tetraClass_count_twenty,
        tetraClass_count_nineteen]
    _ = 2033628 := by decide

private lemma tetraClass_count_twentyfour : tetraClass.count 24 = 3919944 := by
  calc
    tetraClass.count 24 =
        tetraClass.count 23 + tetraClass.count 22 + tetraClass.count 21 + tetraClass.count 20 :=
      tetraClass_count_succ_succ_succ_succ 20
    _ = 2033628 + 1055026 + 547337 + 283953 := by
      rw [tetraClass_count_twentythree, tetraClass_count_twentytwo,
        tetraClass_count_twentyone, tetraClass_count_twenty]
    _ = 3919944 := by decide

private lemma tetraClass_count_twentyfive : tetraClass.count 25 = 7555935 := by
  calc
    tetraClass.count 25 =
        tetraClass.count 24 + tetraClass.count 23 + tetraClass.count 22 + tetraClass.count 21 :=
      tetraClass_count_succ_succ_succ_succ 21
    _ = 3919944 + 2033628 + 1055026 + 547337 := by
      rw [tetraClass_count_twentyfour, tetraClass_count_twentythree,
        tetraClass_count_twentytwo, tetraClass_count_twentyone]
    _ = 7555935 := by decide

/-! Sanity checks:
  1, 1, 2, 4, 8, 15, 29, 56, 108, 208, 401, 773, 1490, 2872, 5536, 10671,
  20569, 39648, 76424, 147312, 283953, 547337, 1055026, 2033628, 3919944,
  7555935. -/
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

example : tetraClass.count 9 = 208 := by
  calc
    tetraClass.count 9 = 208 := tetraClass_count_nine
    _ = 208 := by decide

example : tetraClass.count 10 = 401 := by
  calc
    tetraClass.count 10 = 401 := tetraClass_count_ten
    _ = 401 := by decide

example : tetraClass.count 11 = 773 := by
  calc
    tetraClass.count 11 = 773 := tetraClass_count_eleven
    _ = 773 := by decide

example : tetraClass.count 12 = 1490 := by
  calc
    tetraClass.count 12 = 1490 := tetraClass_count_twelve
    _ = 1490 := by decide

example : tetraClass.count 13 = 2872 := by
  calc
    tetraClass.count 13 = 2872 := tetraClass_count_thirteen
    _ = 2872 := by decide

example : tetraClass.count 14 = 5536 := by
  calc
    tetraClass.count 14 = 5536 := tetraClass_count_fourteen
    _ = 5536 := by decide

example : tetraClass.count 15 = 10671 := by
  calc
    tetraClass.count 15 = 10671 := tetraClass_count_fifteen
    _ = 10671 := by decide

example : tetraClass.count 16 = 20569 := by
  calc
    tetraClass.count 16 = 20569 := tetraClass_count_sixteen
    _ = 20569 := by decide

example : tetraClass.count 17 = 39648 := by
  calc
    tetraClass.count 17 = 39648 := tetraClass_count_seventeen
    _ = 39648 := by decide

example : tetraClass.count 18 = 76424 := by
  calc
    tetraClass.count 18 = 76424 := tetraClass_count_eighteen
    _ = 76424 := by decide

example : tetraClass.count 19 = 147312 := by
  calc
    tetraClass.count 19 = 147312 := tetraClass_count_nineteen
    _ = 147312 := by decide

example : tetraClass.count 20 = 283953 := by
  calc
    tetraClass.count 20 = 283953 := tetraClass_count_twenty
    _ = 283953 := by decide

example : tetraClass.count 21 = 547337 := by
  calc
    tetraClass.count 21 = 547337 := tetraClass_count_twentyone
    _ = 547337 := by decide

example : tetraClass.count 22 = 1055026 := by
  calc
    tetraClass.count 22 = 1055026 := tetraClass_count_twentytwo
    _ = 1055026 := by decide

example : tetraClass.count 23 = 2033628 := by
  calc
    tetraClass.count 23 = 2033628 := tetraClass_count_twentythree
    _ = 2033628 := by decide

example : tetraClass.count 24 = 3919944 := by
  calc
    tetraClass.count 24 = 3919944 := tetraClass_count_twentyfour
    _ = 3919944 := by decide

example : tetraClass.count 25 = 7555935 := by
  calc
    tetraClass.count 25 = 7555935 := tetraClass_count_twentyfive
    _ = 7555935 := by decide

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

/-! ## Parameter: number of parts -/

/-- Number of parts in a Tetranacci composition. -/
def tetraNumParts : Parameter tetraClass := List.length

private abbrev tetraPart1 : step1234Class.Obj := Sum.inl (Sum.inl (Sum.inl ()))
private abbrev tetraPart2 : step1234Class.Obj := Sum.inl (Sum.inl (Sum.inr ()))
private abbrev tetraPart3 : step1234Class.Obj := Sum.inl (Sum.inr ())
private abbrev tetraPart4 : step1234Class.Obj := Sum.inr ()

private instance : DecidableEq step1234Class.Obj := by
  unfold step1234Class CombinatorialClass.disjSum atomOfSize
  infer_instance

private instance : DecidableEq tetraClass.Obj := by
  change DecidableEq (List step1234Class.Obj)
  infer_instance

private lemma tetraPart1_size : step1234Class.size tetraPart1 = 1 := rfl
private lemma tetraPart2_size : step1234Class.size tetraPart2 = 2 := rfl
private lemma tetraPart3_size : step1234Class.size tetraPart3 = 3 := rfl
private lemma tetraPart4_size : step1234Class.size tetraPart4 = 4 := rfl

private lemma step1234Class_obj_eq (x : step1234Class.Obj) :
    x = tetraPart1 ∨ x = tetraPart2 ∨ x = tetraPart3 ∨ x = tetraPart4 := by
  rcases x with x | x
  · rcases x with x | x
    · rcases x with x | x
      · cases x
        left
        rfl
      · cases x
        right
        left
        rfl
    · cases x
      right
      right
      left
      rfl
  · cases x
    right
    right
    right
    rfl

private lemma tetraClass_jointCount_tetraNumParts_eq_one_of_unique
    {n k : ℕ} (x₀ : tetraClass.Obj)
    (hx₀ : x₀ ∈ tetraClass.level n)
    (hnum₀ : tetraNumParts x₀ = k)
    (huniq : ∀ x : tetraClass.Obj,
      x ∈ tetraClass.level n → tetraNumParts x = k → x = x₀) :
    tetraClass.jointCount tetraNumParts n k = 1 := by
  unfold CombinatorialClass.jointCount
  rw [Finset.card_eq_one]
  refine ⟨x₀, ?_⟩
  ext x
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro hx
    exact huniq x hx.1 hx.2
  · intro hx
    subst hx
    exact ⟨hx₀, hnum₀⟩

private lemma tetraClass_jointCount_tetraNumParts_eq_two_of_unique_pair
    {n k : ℕ} (x₁ x₂ : tetraClass.Obj)
    (hx₁ : x₁ ∈ tetraClass.level n)
    (hx₂ : x₂ ∈ tetraClass.level n)
    (hnum₁ : tetraNumParts x₁ = k)
    (hnum₂ : tetraNumParts x₂ = k)
    (hne : x₁ ≠ x₂)
    (huniq : ∀ x : tetraClass.Obj,
      x ∈ tetraClass.level n → tetraNumParts x = k → x = x₁ ∨ x = x₂) :
    tetraClass.jointCount tetraNumParts n k = 2 := by
  classical
  unfold CombinatorialClass.jointCount
  rw [Finset.card_eq_two]
  refine ⟨x₁, x₂, hne, ?_⟩
  ext x
  rw [Finset.mem_filter]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    exact huniq x hx.1 hx.2
  · intro hx
    rcases hx with rfl | rfl
    · exact ⟨hx₁, hnum₁⟩
    · exact ⟨hx₂, hnum₂⟩

private lemma tetraClass_jointCount_tetraNumParts_eq_three_of_unique_triple
    {n k : ℕ} (x₁ x₂ x₃ : tetraClass.Obj)
    (hx₁ : x₁ ∈ tetraClass.level n)
    (hx₂ : x₂ ∈ tetraClass.level n)
    (hx₃ : x₃ ∈ tetraClass.level n)
    (hnum₁ : tetraNumParts x₁ = k)
    (hnum₂ : tetraNumParts x₂ = k)
    (hnum₃ : tetraNumParts x₃ = k)
    (hne₁₂ : x₁ ≠ x₂)
    (hne₁₃ : x₁ ≠ x₃)
    (hne₂₃ : x₂ ≠ x₃)
    (huniq : ∀ x : tetraClass.Obj,
      x ∈ tetraClass.level n → tetraNumParts x = k →
        x = x₁ ∨ x = x₂ ∨ x = x₃) :
    tetraClass.jointCount tetraNumParts n k = 3 := by
  classical
  unfold CombinatorialClass.jointCount
  rw [Finset.card_eq_three]
  refine ⟨x₁, x₂, x₃, hne₁₂, hne₁₃, hne₂₃, ?_⟩
  ext x
  rw [Finset.mem_filter]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    exact huniq x hx.1 hx.2
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨hx₁, hnum₁⟩
    · exact ⟨hx₂, hnum₂⟩
    · exact ⟨hx₃, hnum₃⟩

/-- Sanity: small jointCount values by number of parts. -/
example : tetraClass.jointCount tetraNumParts 0 0 = 1 := by
  apply tetraClass_jointCount_tetraNumParts_eq_one_of_unique ([] : tetraClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x _ hnum
    change x.length = 0 at hnum
    exact List.eq_nil_of_length_eq_zero hnum

example : tetraClass.jointCount tetraNumParts 1 1 = 1 := by
  apply tetraClass_jointCount_tetraNumParts_eq_one_of_unique
    ([tetraPart1] : tetraClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 1 := by
      exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl
            all_goals
              first
              | rfl
              | norm_num [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                  tetraPart4_size] at hsize
        | cons _ _ => simp at hnum

example : tetraClass.jointCount tetraNumParts 2 1 = 1 := by
  apply tetraClass_jointCount_tetraNumParts_eq_one_of_unique
    ([tetraPart2] : tetraClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 2 := by
      exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl
            all_goals
              first
              | rfl
              | norm_num [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                  tetraPart4_size] at hsize
        | cons _ _ => simp at hnum

example : tetraClass.jointCount tetraNumParts 2 2 = 1 := by
  apply tetraClass_jointCount_tetraNumParts_eq_one_of_unique
    ([tetraPart1, tetraPart1] : tetraClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 2 := by
      exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx
    change x.length = 2 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil => simp at hnum
        | cons b xs =>
            cases xs with
            | nil =>
                simp only [List.foldr_cons, List.foldr_nil] at hsize
                rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl <;>
                  rcases step1234Class_obj_eq b with rfl | rfl | rfl | rfl
                all_goals
                  first
                  | rfl
                  | norm_num [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                      tetraPart4_size] at hsize
            | cons _ _ => simp at hnum

example : tetraClass.jointCount tetraNumParts 3 1 = 1 := by
  apply tetraClass_jointCount_tetraNumParts_eq_one_of_unique
    ([tetraPart3] : tetraClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 3 := by
      exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl
            all_goals
              first
              | rfl
              | norm_num [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                  tetraPart4_size] at hsize
        | cons _ _ => simp at hnum

example : tetraClass.jointCount tetraNumParts 3 2 = 2 := by
  apply tetraClass_jointCount_tetraNumParts_eq_two_of_unique_pair
    ([tetraPart1, tetraPart2] : tetraClass.Obj)
    ([tetraPart2, tetraPart1] : tetraClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · decide
  · intro h
    injection h with hhead _
    cases hhead
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 3 := by
      exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx
    change x.length = 2 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil => simp at hnum
        | cons b xs =>
            cases xs with
            | nil =>
                simp only [List.foldr_cons, List.foldr_nil] at hsize
                rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl <;>
                  rcases step1234Class_obj_eq b with rfl | rfl | rfl | rfl
                all_goals
                  first
                  | left; rfl
                  | right; rfl
                  | norm_num [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                      tetraPart4_size] at hsize
            | cons _ _ => simp at hnum

example : tetraClass.jointCount tetraNumParts 3 3 = 1 := by
  apply tetraClass_jointCount_tetraNumParts_eq_one_of_unique
    ([tetraPart1, tetraPart1, tetraPart1] : tetraClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 3 := by
      exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx
    change x.length = 3 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil => simp at hnum
        | cons b xs =>
            cases xs with
            | nil => simp at hnum
            | cons c xs =>
                cases xs with
                | nil =>
                    simp only [List.foldr_cons, List.foldr_nil] at hsize
                    rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl <;>
                      rcases step1234Class_obj_eq b with rfl | rfl | rfl | rfl <;>
                        rcases step1234Class_obj_eq c with rfl | rfl | rfl | rfl
                    all_goals
                      first
                      | rfl
                      | norm_num [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                          tetraPart4_size] at hsize
                | cons _ _ => simp at hnum

example : tetraClass.jointCount tetraNumParts 4 1 = 1 := by
  apply tetraClass_jointCount_tetraNumParts_eq_one_of_unique
    ([tetraPart4] : tetraClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 4 := by
      exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl
            all_goals
              first
              | rfl
              | norm_num [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                  tetraPart4_size] at hsize
        | cons _ _ => simp at hnum

example : tetraClass.jointCount tetraNumParts 4 2 = 3 := by
  apply tetraClass_jointCount_tetraNumParts_eq_three_of_unique_triple
    ([tetraPart1, tetraPart3] : tetraClass.Obj)
    ([tetraPart3, tetraPart1] : tetraClass.Obj)
    ([tetraPart2, tetraPart2] : tetraClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · decide
  · decide
  · intro h
    injection h with hhead _
    cases hhead
  · intro h
    injection h with hhead _
    cases hhead
  · intro h
    injection h with hhead _
    cases hhead
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 4 := by
      exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx
    change x.length = 2 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil => simp at hnum
        | cons b xs =>
            cases xs with
            | nil =>
                simp only [List.foldr_cons, List.foldr_nil] at hsize
                rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl <;>
                  rcases step1234Class_obj_eq b with rfl | rfl | rfl | rfl
                all_goals
                  first
                  | left; rfl
                  | right; left; rfl
                  | right; right; rfl
                  | norm_num [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                      tetraPart4_size] at hsize
            | cons _ _ => simp at hnum

example : tetraClass.jointCount tetraNumParts 4 3 = 3 := by
  apply tetraClass_jointCount_tetraNumParts_eq_three_of_unique_triple
    ([tetraPart1, tetraPart1, tetraPart2] : tetraClass.Obj)
    ([tetraPart1, tetraPart2, tetraPart1] : tetraClass.Obj)
    ([tetraPart2, tetraPart1, tetraPart1] : tetraClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · decide
  · decide
  · intro h
    injection h with _ htail
    injection htail with hhead _
    cases hhead
  · intro h
    injection h with hhead _
    cases hhead
  · intro h
    injection h with hhead _
    cases hhead
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 4 := by
      exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx
    change x.length = 3 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil => simp at hnum
        | cons b xs =>
            cases xs with
            | nil => simp at hnum
            | cons c xs =>
                cases xs with
                | nil =>
                    simp only [List.foldr_cons, List.foldr_nil] at hsize
                    rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl <;>
                      rcases step1234Class_obj_eq b with rfl | rfl | rfl | rfl <;>
                        rcases step1234Class_obj_eq c with rfl | rfl | rfl | rfl
                    all_goals
                      first
                      | left; rfl
                      | right; left; rfl
                      | right; right; rfl
                      | norm_num [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                          tetraPart4_size] at hsize
                | cons _ _ => simp at hnum

example : tetraClass.jointCount tetraNumParts 4 4 = 1 := by
  apply tetraClass_jointCount_tetraNumParts_eq_one_of_unique
    ([tetraPart1, tetraPart1, tetraPart1, tetraPart1] : tetraClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 4 := by
      exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx
    change x.length = 4 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil => simp at hnum
        | cons b xs =>
            cases xs with
            | nil => simp at hnum
            | cons c xs =>
                cases xs with
                | nil => simp at hnum
                | cons d xs =>
                    cases xs with
                    | nil =>
                        simp only [List.foldr_cons, List.foldr_nil] at hsize
                        rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl <;>
                          rcases step1234Class_obj_eq b with rfl | rfl | rfl | rfl <;>
                            rcases step1234Class_obj_eq c with rfl | rfl | rfl | rfl <;>
                              rcases step1234Class_obj_eq d with rfl | rfl | rfl | rfl
                        all_goals
                          first
                          | rfl
                          | norm_num [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                              tetraPart4_size] at hsize
                    | cons _ _ => simp at hnum

private lemma tetraClass_jointCount_tetraNumParts_eq_card_of_finset
    {n k : ℕ} (s : Finset tetraClass.Obj)
    (hs : ∀ x : tetraClass.Obj,
      x ∈ s ↔ x ∈ tetraClass.level n ∧ tetraNumParts x = k) :
    tetraClass.jointCount tetraNumParts n k = s.card := by
  unfold CombinatorialClass.jointCount
  have hset :
      (tetraClass.level n).filter (fun a => tetraNumParts a = k) = s := by
    ext x
    rw [Finset.mem_filter]
    exact (hs x).symm
  rw [hset]

example : tetraClass.jointCount tetraNumParts 5 2 = 4 := by
  let s : Finset tetraClass.Obj :=
    ([ [tetraPart1, tetraPart4],
      [tetraPart4, tetraPart1],
      [tetraPart2, tetraPart3],
      [tetraPart3, tetraPart2] ] : List tetraClass.Obj).toFinset
  have h := tetraClass_jointCount_tetraNumParts_eq_card_of_finset (n := 5) (k := 2) s (by
    intro x
    constructor
    · intro hx
      have hx' :
          x = [tetraPart1, tetraPart4] ∨
            x = [tetraPart4, tetraPart1] ∨
              x = [tetraPart2, tetraPart3] ∨ x = [tetraPart3, tetraPart2] := by
        simpa [s] using hx
      rcases hx' with rfl | rfl | rfl | rfl
      all_goals
        constructor
        · rw [CombinatorialClass.level_mem_iff]
          rfl
        · decide
    · intro hx
      have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 5 := by
        exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx.1
      have hnum := hx.2
      change x.length = 2 at hnum
      cases x with
      | nil => simp at hnum
      | cons a xs =>
          cases xs with
          | nil => simp at hnum
          | cons b xs =>
              cases xs with
              | nil =>
                  simp only [List.foldr_cons, List.foldr_nil] at hsize
                  rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl <;>
                    rcases step1234Class_obj_eq b with rfl | rfl | rfl | rfl
                  all_goals
                    first
                    | simp only [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                        tetraPart4_size] at hsize
                      omega
                    | simp [s]
              | cons _ _ => simp at hnum)
  rw [h]
  decide

example : tetraClass.jointCount tetraNumParts 5 3 = 6 := by
  let s : Finset tetraClass.Obj :=
    ([ [tetraPart1, tetraPart1, tetraPart3],
      [tetraPart1, tetraPart3, tetraPart1],
      [tetraPart3, tetraPart1, tetraPart1],
      [tetraPart1, tetraPart2, tetraPart2],
      [tetraPart2, tetraPart1, tetraPart2],
      [tetraPart2, tetraPart2, tetraPart1] ] : List tetraClass.Obj).toFinset
  have h := tetraClass_jointCount_tetraNumParts_eq_card_of_finset (n := 5) (k := 3) s (by
    intro x
    constructor
    · intro hx
      have hx' :
          x = [tetraPart1, tetraPart1, tetraPart3] ∨
            x = [tetraPart1, tetraPart3, tetraPart1] ∨
              x = [tetraPart3, tetraPart1, tetraPart1] ∨
                x = [tetraPart1, tetraPart2, tetraPart2] ∨
                  x = [tetraPart2, tetraPart1, tetraPart2] ∨
                    x = [tetraPart2, tetraPart2, tetraPart1] := by
        simpa [s] using hx
      rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        constructor
        · rw [CombinatorialClass.level_mem_iff]
          rfl
        · decide
    · intro hx
      have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 5 := by
        exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx.1
      have hnum := hx.2
      change x.length = 3 at hnum
      cases x with
      | nil => simp at hnum
      | cons a xs =>
          cases xs with
          | nil => simp at hnum
          | cons b xs =>
              cases xs with
              | nil => simp at hnum
              | cons c xs =>
                  cases xs with
                  | nil =>
                      simp only [List.foldr_cons, List.foldr_nil] at hsize
                      rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl <;>
                        rcases step1234Class_obj_eq b with rfl | rfl | rfl | rfl <;>
                          rcases step1234Class_obj_eq c with rfl | rfl | rfl | rfl
                      all_goals
                        first
                        | simp only [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                            tetraPart4_size] at hsize
                          omega
                        | simp [s]
                  | cons _ _ => simp at hnum)
  rw [h]
  decide

example : tetraClass.jointCount tetraNumParts 5 4 = 4 := by
  let s : Finset tetraClass.Obj :=
    ([ [tetraPart1, tetraPart1, tetraPart1, tetraPart2],
      [tetraPart1, tetraPart1, tetraPart2, tetraPart1],
      [tetraPart1, tetraPart2, tetraPart1, tetraPart1],
      [tetraPart2, tetraPart1, tetraPart1, tetraPart1] ] : List tetraClass.Obj).toFinset
  have h := tetraClass_jointCount_tetraNumParts_eq_card_of_finset (n := 5) (k := 4) s (by
    intro x
    constructor
    · intro hx
      have hx' :
          x = [tetraPart1, tetraPart1, tetraPart1, tetraPart2] ∨
            x = [tetraPart1, tetraPart1, tetraPart2, tetraPart1] ∨
              x = [tetraPart1, tetraPart2, tetraPart1, tetraPart1] ∨
                x = [tetraPart2, tetraPart1, tetraPart1, tetraPart1] := by
        simpa [s] using hx
      rcases hx' with rfl | rfl | rfl | rfl
      all_goals
        constructor
        · rw [CombinatorialClass.level_mem_iff]
          rfl
        · decide
    · intro hx
      have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 5 := by
        exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx.1
      have hnum := hx.2
      change x.length = 4 at hnum
      cases x with
      | nil => simp at hnum
      | cons a xs =>
          cases xs with
          | nil => simp at hnum
          | cons b xs =>
              cases xs with
              | nil => simp at hnum
              | cons c xs =>
                  cases xs with
                  | nil => simp at hnum
                  | cons d xs =>
                      cases xs with
                      | nil =>
                          simp only [List.foldr_cons, List.foldr_nil] at hsize
                          rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl <;>
                            rcases step1234Class_obj_eq b with rfl | rfl | rfl | rfl <;>
                              rcases step1234Class_obj_eq c with rfl | rfl | rfl | rfl <;>
                                rcases step1234Class_obj_eq d with rfl | rfl | rfl | rfl
                          all_goals
                            first
                            | simp only [tetraPart1_size, tetraPart2_size, tetraPart3_size,
                                tetraPart4_size] at hsize
                              omega
                            | simp [s]
                      | cons _ _ => simp at hnum)
  rw [h]
  decide

example : tetraClass.jointCount tetraNumParts 5 5 = 1 := by
  let s : Finset tetraClass.Obj :=
    ([ [tetraPart1, tetraPart1, tetraPart1, tetraPart1, tetraPart1] ] :
      List tetraClass.Obj).toFinset
  have h := tetraClass_jointCount_tetraNumParts_eq_card_of_finset (n := 5) (k := 5) s (by
    intro x
    constructor
    · intro hx
      have hx' : x = [tetraPart1, tetraPart1, tetraPart1, tetraPart1, tetraPart1] := by
        simpa [s] using hx
      subst x
      constructor
      · rw [CombinatorialClass.level_mem_iff]
        rfl
      · decide
    · intro hx
      have hsize : x.foldr (fun b acc => step1234Class.size b + acc) 0 = 5 := by
        exact (CombinatorialClass.level_mem_iff (C := tetraClass) x).mp hx.1
      have hnum := hx.2
      change x.length = 5 at hnum
      cases x with
      | nil => simp at hnum
      | cons a xs =>
          cases xs with
          | nil => simp at hnum
          | cons b xs =>
              cases xs with
              | nil => simp at hnum
              | cons c xs =>
                  cases xs with
                  | nil => simp at hnum
                  | cons d xs =>
                      cases xs with
                      | nil => simp at hnum
                      | cons e xs =>
                          cases xs with
                          | nil =>
                              simp only [List.foldr_cons, List.foldr_nil] at hsize
                              rcases step1234Class_obj_eq a with rfl | rfl | rfl | rfl <;>
                                rcases step1234Class_obj_eq b with rfl | rfl | rfl | rfl <;>
                                  rcases step1234Class_obj_eq c with rfl | rfl | rfl | rfl <;>
                                    rcases step1234Class_obj_eq d with rfl | rfl | rfl | rfl <;>
                                      rcases step1234Class_obj_eq e with rfl | rfl | rfl | rfl
                              all_goals
                                first
                                | simp only [tetraPart1_size, tetraPart2_size,
                                    tetraPart3_size, tetraPart4_size] at hsize
                                  omega
                                | simp [s]
                          | cons _ _ => simp at hnum)
  rw [h]
  decide
