/-
  Analytic Combinatorics — Examples
  Tribonacci compositions

  Compositions of n into parts of size 1, 2, or 3.
-/
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import AnalyticCombinatorics.PartA.Ch3.Parameters

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

example : tribClass.count 8 = 81 := by
  calc
    tribClass.count 8 = tribClass.count 7 + tribClass.count 6 + tribClass.count 5 :=
      tribClass_count_succ_succ_succ 5
    _ = 44 + 24 + 13 := by
      rw [tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_two, tribClass_count_one,
        tribClass_count_zero]
    _ = 81 := by decide

example : tribClass.count 9 = 149 := by
  calc
    tribClass.count 9 = tribClass.count 8 + tribClass.count 7 + tribClass.count 6 :=
      tribClass_count_succ_succ_succ 6
    _ = 81 + 44 + 24 := by
      rw [tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_two, tribClass_count_one, tribClass_count_zero]
    _ = 149 := by decide

example : tribClass.count 10 = 274 := by
  calc
    tribClass.count 10 = tribClass.count 9 + tribClass.count 8 + tribClass.count 7 :=
      tribClass_count_succ_succ_succ 7
    _ = 149 + 81 + 44 := by
      rw [tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_two, tribClass_count_one,
        tribClass_count_zero]
    _ = 274 := by decide

example : tribClass.count 11 = 504 := by
  calc
    tribClass.count 11 = tribClass.count 10 + tribClass.count 9 + tribClass.count 8 :=
      tribClass_count_succ_succ_succ 8
    _ = 274 + 149 + 81 := by
      rw [tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_two, tribClass_count_one, tribClass_count_zero]
    _ = 504 := by decide

example : tribClass.count 12 = 927 := by
  calc
    tribClass.count 12 = tribClass.count 11 + tribClass.count 10 + tribClass.count 9 :=
      tribClass_count_succ_succ_succ 9
    _ = 504 + 274 + 149 := by
      rw [tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_two, tribClass_count_one,
        tribClass_count_zero]
    _ = 927 := by decide

example : tribClass.count 13 = 1705 := by
  calc
    tribClass.count 13 = tribClass.count 12 + tribClass.count 11 + tribClass.count 10 :=
      tribClass_count_succ_succ_succ 10
    _ = 927 + 504 + 274 := by
      rw [tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_succ_succ_succ, tribClass_count_succ_succ_succ,
        tribClass_count_two, tribClass_count_one, tribClass_count_zero]
    _ = 1705 := by decide

example : tribClass.count 14 = 3136 := by
  calc
    tribClass.count 14 = tribClass.count 13 + tribClass.count 12 + tribClass.count 11 :=
      tribClass_count_succ_succ_succ 11
    _ = 1705 + 927 + 504 := by
      repeat rw [tribClass_count_succ_succ_succ]
      rw [tribClass_count_two, tribClass_count_one, tribClass_count_zero]
    _ = 3136 := by decide

example : tribClass.count 15 = 5768 := by
  calc
    tribClass.count 15 = tribClass.count 14 + tribClass.count 13 + tribClass.count 12 :=
      tribClass_count_succ_succ_succ 12
    _ = 3136 + 1705 + 927 := by
      repeat rw [tribClass_count_succ_succ_succ]
      rw [tribClass_count_two, tribClass_count_one, tribClass_count_zero]
    _ = 5768 := by decide

example : tribClass.count 16 = 10609 := by
  calc
    tribClass.count 16 = tribClass.count 15 + tribClass.count 14 + tribClass.count 13 :=
      tribClass_count_succ_succ_succ 13
    _ = 5768 + 3136 + 1705 := by
      repeat rw [tribClass_count_succ_succ_succ]
      rw [tribClass_count_two, tribClass_count_one, tribClass_count_zero]
    _ = 10609 := by decide

example : tribClass.count 17 = 19513 := by
  calc
    tribClass.count 17 = tribClass.count 16 + tribClass.count 15 + tribClass.count 14 :=
      tribClass_count_succ_succ_succ 14
    _ = 10609 + 5768 + 3136 := by
      repeat rw [tribClass_count_succ_succ_succ]
      rw [tribClass_count_two, tribClass_count_one, tribClass_count_zero]
    _ = 19513 := by decide

example : tribClass.count 18 = 35890 := by
  calc
    tribClass.count 18 = tribClass.count 17 + tribClass.count 16 + tribClass.count 15 :=
      tribClass_count_succ_succ_succ 15
    _ = 19513 + 10609 + 5768 := by
      repeat rw [tribClass_count_succ_succ_succ]
      rw [tribClass_count_two, tribClass_count_one, tribClass_count_zero]
    _ = 35890 := by decide

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

/-! ## Parameter: number of parts -/

/-- Number of parts in a Tribonacci composition. -/
def tribNumParts : Parameter tribClass := List.length

private abbrev tribPart1 : step123Class.Obj := Sum.inl (Sum.inl ())
private abbrev tribPart2 : step123Class.Obj := Sum.inl (Sum.inr ())
private abbrev tribPart3 : step123Class.Obj := Sum.inr ()

private instance : DecidableEq step123Class.Obj := by
  unfold step123Class CombinatorialClass.disjSum atomOfSize
  infer_instance

private lemma tribPart1_size : step123Class.size tribPart1 = 1 := rfl
private lemma tribPart2_size : step123Class.size tribPart2 = 2 := rfl
private lemma tribPart3_size : step123Class.size tribPart3 = 3 := rfl

private lemma step123Class_obj_eq (x : step123Class.Obj) :
    x = tribPart1 ∨ x = tribPart2 ∨ x = tribPart3 := by
  rcases x with x | x
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
    rfl

private lemma tribClass_jointCount_tribNumParts_eq_one_of_unique
    {n k : ℕ} (x₀ : tribClass.Obj)
    (hx₀ : x₀ ∈ tribClass.level n)
    (hnum₀ : tribNumParts x₀ = k)
    (huniq : ∀ x : tribClass.Obj,
      x ∈ tribClass.level n → tribNumParts x = k → x = x₀) :
    tribClass.jointCount tribNumParts n k = 1 := by
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

private lemma tribClass_jointCount_tribNumParts_eq_two_of_unique_pair
    {n k : ℕ} (x₁ x₂ : tribClass.Obj)
    (hx₁ : x₁ ∈ tribClass.level n)
    (hx₂ : x₂ ∈ tribClass.level n)
    (hnum₁ : tribNumParts x₁ = k)
    (hnum₂ : tribNumParts x₂ = k)
    (hne : x₁ ≠ x₂)
    (huniq : ∀ x : tribClass.Obj,
      x ∈ tribClass.level n → tribNumParts x = k → x = x₁ ∨ x = x₂) :
    tribClass.jointCount tribNumParts n k = 2 := by
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

private lemma tribClass_jointCount_tribNumParts_eq_three_of_unique_triple
    {n k : ℕ} (x₁ x₂ x₃ : tribClass.Obj)
    (hx₁ : x₁ ∈ tribClass.level n)
    (hx₂ : x₂ ∈ tribClass.level n)
    (hx₃ : x₃ ∈ tribClass.level n)
    (hnum₁ : tribNumParts x₁ = k)
    (hnum₂ : tribNumParts x₂ = k)
    (hnum₃ : tribNumParts x₃ = k)
    (hne₁₂ : x₁ ≠ x₂)
    (hne₁₃ : x₁ ≠ x₃)
    (hne₂₃ : x₂ ≠ x₃)
    (huniq : ∀ x : tribClass.Obj,
      x ∈ tribClass.level n → tribNumParts x = k →
        x = x₁ ∨ x = x₂ ∨ x = x₃) :
    tribClass.jointCount tribNumParts n k = 3 := by
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
example : tribClass.jointCount tribNumParts 0 0 = 1 := by
  apply tribClass_jointCount_tribNumParts_eq_one_of_unique ([] : tribClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x _ hnum
    change x.length = 0 at hnum
    exact List.eq_nil_of_length_eq_zero hnum

example : tribClass.jointCount tribNumParts 1 1 = 1 := by
  apply tribClass_jointCount_tribNumParts_eq_one_of_unique
    ([tribPart1] : tribClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step123Class.size b + acc) 0 = 1 := by
      exact (CombinatorialClass.level_mem_iff (C := tribClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            rcases step123Class_obj_eq a with rfl | rfl | rfl
            all_goals
              first
              | rfl
              | norm_num [tribPart1_size, tribPart2_size, tribPart3_size] at hsize
        | cons _ _ => simp at hnum

example : tribClass.jointCount tribNumParts 2 1 = 1 := by
  apply tribClass_jointCount_tribNumParts_eq_one_of_unique
    ([tribPart2] : tribClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step123Class.size b + acc) 0 = 2 := by
      exact (CombinatorialClass.level_mem_iff (C := tribClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            rcases step123Class_obj_eq a with rfl | rfl | rfl
            all_goals
              first
              | rfl
              | norm_num [tribPart1_size, tribPart2_size, tribPart3_size] at hsize
        | cons _ _ => simp at hnum

example : tribClass.jointCount tribNumParts 2 2 = 1 := by
  apply tribClass_jointCount_tribNumParts_eq_one_of_unique
    ([tribPart1, tribPart1] : tribClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step123Class.size b + acc) 0 = 2 := by
      exact (CombinatorialClass.level_mem_iff (C := tribClass) x).mp hx
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
                rcases step123Class_obj_eq a with rfl | rfl | rfl <;>
                  rcases step123Class_obj_eq b with rfl | rfl | rfl
                all_goals
                  first
                  | rfl
                  | norm_num [tribPart1_size, tribPart2_size, tribPart3_size] at hsize
            | cons _ _ => simp at hnum

example : tribClass.jointCount tribNumParts 3 1 = 1 := by
  apply tribClass_jointCount_tribNumParts_eq_one_of_unique
    ([tribPart3] : tribClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step123Class.size b + acc) 0 = 3 := by
      exact (CombinatorialClass.level_mem_iff (C := tribClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            rcases step123Class_obj_eq a with rfl | rfl | rfl
            all_goals
              first
              | rfl
              | norm_num [tribPart1_size, tribPart2_size, tribPart3_size] at hsize
        | cons _ _ => simp at hnum

example : tribClass.jointCount tribNumParts 3 2 = 2 := by
  apply tribClass_jointCount_tribNumParts_eq_two_of_unique_pair
    ([tribPart1, tribPart2] : tribClass.Obj)
    ([tribPart2, tribPart1] : tribClass.Obj)
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
    have hsize : x.foldr (fun b acc => step123Class.size b + acc) 0 = 3 := by
      exact (CombinatorialClass.level_mem_iff (C := tribClass) x).mp hx
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
                rcases step123Class_obj_eq a with rfl | rfl | rfl <;>
                  rcases step123Class_obj_eq b with rfl | rfl | rfl
                all_goals
                  first
                  | left; rfl
                  | right; rfl
                  | norm_num [tribPart1_size, tribPart2_size, tribPart3_size] at hsize
            | cons _ _ => simp at hnum

example : tribClass.jointCount tribNumParts 3 3 = 1 := by
  apply tribClass_jointCount_tribNumParts_eq_one_of_unique
    ([tribPart1, tribPart1, tribPart1] : tribClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step123Class.size b + acc) 0 = 3 := by
      exact (CombinatorialClass.level_mem_iff (C := tribClass) x).mp hx
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
                    rcases step123Class_obj_eq a with rfl | rfl | rfl <;>
                      rcases step123Class_obj_eq b with rfl | rfl | rfl <;>
                        rcases step123Class_obj_eq c with rfl | rfl | rfl
                    all_goals
                      first
                      | rfl
                      | norm_num [tribPart1_size, tribPart2_size, tribPart3_size] at hsize
                | cons _ _ => simp at hnum

example : tribClass.jointCount tribNumParts 4 2 = 3 := by
  apply tribClass_jointCount_tribNumParts_eq_three_of_unique_triple
    ([tribPart1, tribPart3] : tribClass.Obj)
    ([tribPart3, tribPart1] : tribClass.Obj)
    ([tribPart2, tribPart2] : tribClass.Obj)
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
    have hsize : x.foldr (fun b acc => step123Class.size b + acc) 0 = 4 := by
      exact (CombinatorialClass.level_mem_iff (C := tribClass) x).mp hx
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
                rcases step123Class_obj_eq a with rfl | rfl | rfl <;>
                  rcases step123Class_obj_eq b with rfl | rfl | rfl
                all_goals
                  first
                  | left; rfl
                  | right; left; rfl
                  | right; right; rfl
                  | norm_num [tribPart1_size, tribPart2_size, tribPart3_size] at hsize
            | cons _ _ => simp at hnum

example : tribClass.jointCount tribNumParts 4 3 = 3 := by
  apply tribClass_jointCount_tribNumParts_eq_three_of_unique_triple
    ([tribPart1, tribPart1, tribPart2] : tribClass.Obj)
    ([tribPart1, tribPart2, tribPart1] : tribClass.Obj)
    ([tribPart2, tribPart1, tribPart1] : tribClass.Obj)
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
    have hsize : x.foldr (fun b acc => step123Class.size b + acc) 0 = 4 := by
      exact (CombinatorialClass.level_mem_iff (C := tribClass) x).mp hx
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
                    rcases step123Class_obj_eq a with rfl | rfl | rfl <;>
                      rcases step123Class_obj_eq b with rfl | rfl | rfl <;>
                        rcases step123Class_obj_eq c with rfl | rfl | rfl
                    all_goals
                      first
                      | left; rfl
                      | right; left; rfl
                      | right; right; rfl
                      | norm_num [tribPart1_size, tribPart2_size, tribPart3_size] at hsize
                | cons _ _ => simp at hnum

example : tribClass.jointCount tribNumParts 4 4 = 1 := by
  apply tribClass_jointCount_tribNumParts_eq_one_of_unique
    ([tribPart1, tribPart1, tribPart1, tribPart1] : tribClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · decide
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step123Class.size b + acc) 0 = 4 := by
      exact (CombinatorialClass.level_mem_iff (C := tribClass) x).mp hx
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
                        rcases step123Class_obj_eq a with rfl | rfl | rfl <;>
                          rcases step123Class_obj_eq b with rfl | rfl | rfl <;>
                            rcases step123Class_obj_eq c with rfl | rfl | rfl <;>
                              rcases step123Class_obj_eq d with rfl | rfl | rfl
                        all_goals
                          first
                          | rfl
                          | norm_num [tribPart1_size, tribPart2_size, tribPart3_size] at hsize
                    | cons _ _ => simp at hnum
