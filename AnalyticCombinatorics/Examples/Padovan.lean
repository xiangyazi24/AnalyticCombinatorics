/-
  Analytic Combinatorics — Examples
  Padovan compositions

  Compositions of n into parts of size 2 or 3.
-/
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import AnalyticCombinatorics.PartA.Ch3.Parameters

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

private lemma padovanClass_count_eleven : padovanClass.count 11 = 9 := by
  calc
    padovanClass.count 11 = padovanClass.count 9 + padovanClass.count 8 :=
      padovanClass_count_succ_succ_succ 8
    _ = 5 + 4 := by rw [padovanClass_count_nine, padovanClass_count_eight]
    _ = 9 := by decide

private lemma padovanClass_count_twelve : padovanClass.count 12 = 12 := by
  calc
    padovanClass.count 12 = padovanClass.count 10 + padovanClass.count 9 :=
      padovanClass_count_succ_succ_succ 9
    _ = 7 + 5 := by rw [padovanClass_count_ten, padovanClass_count_nine]
    _ = 12 := by decide

private lemma padovanClass_count_thirteen : padovanClass.count 13 = 16 := by
  calc
    padovanClass.count 13 = padovanClass.count 11 + padovanClass.count 10 :=
      padovanClass_count_succ_succ_succ 10
    _ = 9 + 7 := by rw [padovanClass_count_eleven, padovanClass_count_ten]
    _ = 16 := by decide

private lemma padovanClass_count_fourteen : padovanClass.count 14 = 21 := by
  calc
    padovanClass.count 14 = padovanClass.count 12 + padovanClass.count 11 :=
      padovanClass_count_succ_succ_succ 11
    _ = 12 + 9 := by rw [padovanClass_count_twelve, padovanClass_count_eleven]
    _ = 21 := by decide

private lemma padovanClass_count_fifteen : padovanClass.count 15 = 28 := by
  calc
    padovanClass.count 15 = padovanClass.count 13 + padovanClass.count 12 :=
      padovanClass_count_succ_succ_succ 12
    _ = 16 + 12 := by rw [padovanClass_count_thirteen, padovanClass_count_twelve]
    _ = 28 := by decide

private lemma padovanClass_count_sixteen : padovanClass.count 16 = 37 := by
  calc
    padovanClass.count 16 = padovanClass.count 14 + padovanClass.count 13 :=
      padovanClass_count_succ_succ_succ 13
    _ = 21 + 16 := by rw [padovanClass_count_fourteen, padovanClass_count_thirteen]
    _ = 37 := by decide

/-! Sanity checks: 1, 0, 1, 1, 1, 2, 2, 3, 4, 5, 7, 9, 12, 16, 21, 28, 37. -/
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

example : padovanClass.count 11 = 9 := by
  calc
    padovanClass.count 11 = 9 := padovanClass_count_eleven
    _ = 9 := by decide

example : padovanClass.count 12 = 12 := by
  calc
    padovanClass.count 12 = 12 := padovanClass_count_twelve
    _ = 12 := by decide

example : padovanClass.count 13 = 16 := by
  calc
    padovanClass.count 13 = 16 := padovanClass_count_thirteen
    _ = 16 := by decide

example : padovanClass.count 14 = 21 := by
  calc
    padovanClass.count 14 = 21 := padovanClass_count_fourteen
    _ = 21 := by decide

example : padovanClass.count 15 = 28 := by
  calc
    padovanClass.count 15 = 28 := padovanClass_count_fifteen
    _ = 28 := by decide

example : padovanClass.count 16 = 37 := by
  calc
    padovanClass.count 16 = 37 := padovanClass_count_sixteen
    _ = 37 := by decide

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

/-- Padovan recurrence for compositions into parts 2 and 3. -/
theorem padovanClass_count_recurrence (n : ℕ) :
    padovanClass.count (n + 3) = padovanClass.count (n + 1) + padovanClass.count n := by
  exact padovanClass_count_succ_succ_succ n

/-! ## Parameter: number of parts -/

/-- Number of parts in a Padovan composition. -/
def padovanNumParts : Parameter padovanClass := List.length

private abbrev padovanPart2 : step23Class.Obj := Sum.inl ()
private abbrev padovanPart3 : step23Class.Obj := Sum.inr ()

private lemma step23Class_size_ge_two (x : step23Class.Obj) : 2 ≤ step23Class.size x := by
  rcases x with x | x <;> cases x <;> decide

private lemma padovanClass_size_ge_two_mul_length (x : padovanClass.Obj) :
    2 * x.length ≤ x.foldr (fun b acc => step23Class.size b + acc) 0 := by
  induction x with
  | nil => simp
  | cons a xs ih =>
      simp only [List.length_cons, List.foldr_cons]
      have ha := step23Class_size_ge_two a
      omega

private lemma padovanClass_jointCount_padovanNumParts_eq_one_of_unique
    {n k : ℕ} (x₀ : padovanClass.Obj)
    (hx₀ : x₀ ∈ padovanClass.level n)
    (hnum₀ : padovanNumParts x₀ = k)
    (huniq : ∀ x : padovanClass.Obj,
      x ∈ padovanClass.level n → padovanNumParts x = k → x = x₀) :
    padovanClass.jointCount padovanNumParts n k = 1 := by
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

private lemma padovanClass_jointCount_padovanNumParts_eq_two_of_unique_pair
    {n k : ℕ} (x₁ x₂ : padovanClass.Obj)
    (hx₁ : x₁ ∈ padovanClass.level n)
    (hx₂ : x₂ ∈ padovanClass.level n)
    (hnum₁ : padovanNumParts x₁ = k)
    (hnum₂ : padovanNumParts x₂ = k)
    (hne : x₁ ≠ x₂)
    (huniq : ∀ x : padovanClass.Obj,
      x ∈ padovanClass.level n → padovanNumParts x = k → x = x₁ ∨ x = x₂) :
    padovanClass.jointCount padovanNumParts n k = 2 := by
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

private lemma padovanClass_jointCount_padovanNumParts_eq_three_of_unique_triple
    {n k : ℕ} (x₁ x₂ x₃ : padovanClass.Obj)
    (hx₁ : x₁ ∈ padovanClass.level n)
    (hx₂ : x₂ ∈ padovanClass.level n)
    (hx₃ : x₃ ∈ padovanClass.level n)
    (hnum₁ : padovanNumParts x₁ = k)
    (hnum₂ : padovanNumParts x₂ = k)
    (hnum₃ : padovanNumParts x₃ = k)
    (hne₁₂ : x₁ ≠ x₂)
    (hne₁₃ : x₁ ≠ x₃)
    (hne₂₃ : x₂ ≠ x₃)
    (huniq : ∀ x : padovanClass.Obj,
      x ∈ padovanClass.level n → padovanNumParts x = k →
        x = x₁ ∨ x = x₂ ∨ x = x₃) :
    padovanClass.jointCount padovanNumParts n k = 3 := by
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

example : padovanClass.jointCount padovanNumParts 2 1 = 1 := by
  apply padovanClass_jointCount_padovanNumParts_eq_one_of_unique
    ([padovanPart2] : padovanClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step23Class.size b + acc) 0 = 2 := by
      exact (CombinatorialClass.level_mem_iff (C := padovanClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            rcases a with a | a
            · cases a
              rfl
            · cases a
              change (3 : ℕ) + 0 = 2 at hsize
              omega
        | cons _ _ => simp at hnum

example : padovanClass.jointCount padovanNumParts 3 1 = 1 := by
  apply padovanClass_jointCount_padovanNumParts_eq_one_of_unique
    ([padovanPart3] : padovanClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step23Class.size b + acc) 0 = 3 := by
      exact (CombinatorialClass.level_mem_iff (C := padovanClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            rcases a with a | a
            · cases a
              change (2 : ℕ) + 0 = 3 at hsize
              omega
            · cases a
              rfl
        | cons _ _ => simp at hnum

example : padovanClass.jointCount padovanNumParts 4 2 = 1 := by
  apply padovanClass_jointCount_padovanNumParts_eq_one_of_unique
    ([padovanPart2, padovanPart2] : padovanClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step23Class.size b + acc) 0 = 4 := by
      exact (CombinatorialClass.level_mem_iff (C := padovanClass) x).mp hx
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
                rcases a with a | a <;> rcases b with b | b
                · cases a
                  cases b
                  rfl
                · cases a
                  cases b
                  change (2 : ℕ) + (3 + 0) = 4 at hsize
                  omega
                · cases a
                  cases b
                  change (3 : ℕ) + (2 + 0) = 4 at hsize
                  omega
                · cases a
                  cases b
                  change (3 : ℕ) + (3 + 0) = 4 at hsize
                  omega
            | cons _ _ => simp at hnum

example : padovanClass.jointCount padovanNumParts 5 2 = 2 := by
  apply padovanClass_jointCount_padovanNumParts_eq_two_of_unique_pair
    ([padovanPart2, padovanPart3] : padovanClass.Obj)
    ([padovanPart3, padovanPart2] : padovanClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · rfl
  · intro h
    injection h with hhead _
    cases hhead
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step23Class.size b + acc) 0 = 5 := by
      exact (CombinatorialClass.level_mem_iff (C := padovanClass) x).mp hx
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
                rcases a with a | a <;> rcases b with b | b
                · cases a
                  cases b
                  change (2 : ℕ) + (2 + 0) = 5 at hsize
                  omega
                · cases a
                  cases b
                  left
                  rfl
                · cases a
                  cases b
                  right
                  rfl
                · cases a
                  cases b
                  change (3 : ℕ) + (3 + 0) = 5 at hsize
                  omega
            | cons _ _ => simp at hnum

example : padovanClass.jointCount padovanNumParts 6 2 = 1 := by
  apply padovanClass_jointCount_padovanNumParts_eq_one_of_unique
    ([padovanPart3, padovanPart3] : padovanClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step23Class.size b + acc) 0 = 6 := by
      exact (CombinatorialClass.level_mem_iff (C := padovanClass) x).mp hx
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
                rcases a with a | a <;> rcases b with b | b
                · cases a
                  cases b
                  change (2 : ℕ) + (2 + 0) = 6 at hsize
                  omega
                · cases a
                  cases b
                  change (2 : ℕ) + (3 + 0) = 6 at hsize
                  omega
                · cases a
                  cases b
                  change (3 : ℕ) + (2 + 0) = 6 at hsize
                  omega
                · cases a
                  cases b
                  rfl
            | cons _ _ => simp at hnum

example : padovanClass.jointCount padovanNumParts 6 3 = 1 := by
  apply padovanClass_jointCount_padovanNumParts_eq_one_of_unique
    ([padovanPart2, padovanPart2, padovanPart2] : padovanClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step23Class.size b + acc) 0 = 6 := by
      exact (CombinatorialClass.level_mem_iff (C := padovanClass) x).mp hx
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
                    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c
                    · cases a
                      cases b
                      cases c
                      rfl
                    · cases a
                      cases b
                      cases c
                      change (2 : ℕ) + (2 + (3 + 0)) = 6 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      change (2 : ℕ) + (3 + (2 + 0)) = 6 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      change (2 : ℕ) + (3 + (3 + 0)) = 6 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      change (3 : ℕ) + (2 + (2 + 0)) = 6 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      change (3 : ℕ) + (2 + (3 + 0)) = 6 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      change (3 : ℕ) + (3 + (2 + 0)) = 6 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      change (3 : ℕ) + (3 + (3 + 0)) = 6 at hsize
                      omega
                | cons _ _ => simp at hnum

example : padovanClass.jointCount padovanNumParts 7 4 = 0 := by
  unfold CombinatorialClass.jointCount
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  rw [Finset.mem_filter] at hx
  have hsize : x.foldr (fun b acc => step23Class.size b + acc) 0 = 7 := by
    exact (CombinatorialClass.level_mem_iff (C := padovanClass) x).mp hx.1
  have hnum : padovanNumParts x = 4 := hx.2
  change x.length = 4 at hnum
  have hbound := padovanClass_size_ge_two_mul_length x
  omega

example : padovanClass.jointCount padovanNumParts 8 3 = 3 := by
  apply padovanClass_jointCount_padovanNumParts_eq_three_of_unique_triple
    ([padovanPart2, padovanPart3, padovanPart3] : padovanClass.Obj)
    ([padovanPart3, padovanPart2, padovanPart3] : padovanClass.Obj)
    ([padovanPart3, padovanPart3, padovanPart2] : padovanClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · rfl
  · rfl
  · intro h
    injection h with hhead _
    cases hhead
  · intro h
    injection h with hhead _
    cases hhead
  · intro h
    injection h with _ htail
    injection htail with hhead _
    cases hhead
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step23Class.size b + acc) 0 = 8 := by
      exact (CombinatorialClass.level_mem_iff (C := padovanClass) x).mp hx
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
                    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c
                    · cases a
                      cases b
                      cases c
                      change (2 : ℕ) + (2 + (2 + 0)) = 8 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      change (2 : ℕ) + (2 + (3 + 0)) = 8 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      change (2 : ℕ) + (3 + (2 + 0)) = 8 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      left
                      rfl
                    · cases a
                      cases b
                      cases c
                      change (3 : ℕ) + (2 + (2 + 0)) = 8 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      right
                      left
                      rfl
                    · cases a
                      cases b
                      cases c
                      right
                      right
                      rfl
                    · cases a
                      cases b
                      cases c
                      change (3 : ℕ) + (3 + (3 + 0)) = 8 at hsize
                      omega
                | cons _ _ => simp at hnum

example : padovanClass.jointCount padovanNumParts 8 4 = 1 := by
  apply padovanClass_jointCount_padovanNumParts_eq_one_of_unique
    ([padovanPart2, padovanPart2, padovanPart2, padovanPart2] : padovanClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => step23Class.size b + acc) 0 = 8 := by
      exact (CombinatorialClass.level_mem_iff (C := padovanClass) x).mp hx
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
                        have ha := step23Class_size_ge_two a
                        have hb := step23Class_size_ge_two b
                        have hc := step23Class_size_ge_two c
                        have hd := step23Class_size_ge_two d
                        have hsa : step23Class.size a = 2 := by omega
                        have hsb : step23Class.size b = 2 := by omega
                        have hsc : step23Class.size c = 2 := by omega
                        have hsd : step23Class.size d = 2 := by omega
                        rcases a with a | a
                        · rcases b with b | b
                          · rcases c with c | c
                            · rcases d with d | d
                              · cases a
                                cases b
                                cases c
                                cases d
                                rfl
                              · cases d
                                change (3 : ℕ) = 2 at hsd
                                omega
                            · cases c
                              change (3 : ℕ) = 2 at hsc
                              omega
                          · cases b
                            change (3 : ℕ) = 2 at hsb
                            omega
                        · cases a
                          change (3 : ℕ) = 2 at hsa
                          omega
                    | cons _ _ => simp at hnum

example : padovanClass.jointCount padovanNumParts 7 3 = 3 := by
  apply padovanClass_jointCount_padovanNumParts_eq_three_of_unique_triple
    ([padovanPart2, padovanPart2, padovanPart3] : padovanClass.Obj)
    ([padovanPart2, padovanPart3, padovanPart2] : padovanClass.Obj)
    ([padovanPart3, padovanPart2, padovanPart2] : padovanClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · rfl
  · rfl
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
    have hsize : x.foldr (fun b acc => step23Class.size b + acc) 0 = 7 := by
      exact (CombinatorialClass.level_mem_iff (C := padovanClass) x).mp hx
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
                    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c
                    · cases a
                      cases b
                      cases c
                      change (2 : ℕ) + (2 + (2 + 0)) = 7 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      left
                      rfl
                    · cases a
                      cases b
                      cases c
                      right
                      left
                      rfl
                    · cases a
                      cases b
                      cases c
                      change (2 : ℕ) + (3 + (3 + 0)) = 7 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      right
                      right
                      rfl
                    · cases a
                      cases b
                      cases c
                      change (3 : ℕ) + (2 + (3 + 0)) = 7 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      change (3 : ℕ) + (3 + (2 + 0)) = 7 at hsize
                      omega
                    · cases a
                      cases b
                      cases c
                      change (3 : ℕ) + (3 + (3 + 0)) = 7 at hsize
                      omega
                | cons _ _ => simp at hnum
