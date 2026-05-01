/-
  Analytic Combinatorics — Examples
  Fibonacci compositions

  Compositions of n into parts of size 1 or 2, equivalently domino tilings
  of a 1 × n strip by monomers and dimers.
-/
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import AnalyticCombinatorics.PartA.Ch3.Parameters
import Mathlib.Data.Nat.Fib.Basic

open PowerSeries CombinatorialClass Finset

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

/-! Sanity checks: fib(n+1) sequence is 1, 1, 2, 3, 5, 8, 13, 21, 34, 55. -/
example : fibClass.count 0 = 1 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 1 = 1 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 2 = 2 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 3 = 3 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 4 = 5 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 5 = 8 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 6 = 13 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 7 = 21 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 8 = 34 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 9 = 55 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 10 = 89 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 11 = 144 := by rw [fibClass_count_eq_fib]; decide
example : fibClass.count 12 = 233 := by rw [fibClass_count_eq_fib]; decide

/-- Closed form for the OGF of compositions into parts of size 1 or 2:
    `1 / (1 - z - z^2)`. -/
theorem fibClass_ogfZ_mul_one_sub_X_sub_X_sq :
    ogfZ fibClass * (1 - PowerSeries.X - PowerSeries.X ^ 2) = 1 := by
  rw [show ogfZ fibClass * (1 - PowerSeries.X - PowerSeries.X ^ 2) =
      ogfZ fibClass - ogfZ fibClass * PowerSeries.X -
        ogfZ fibClass * PowerSeries.X ^ 2 by ring]
  ext n
  rcases n with _ | m
  · simp only [map_sub]
    rw [show coeff 0 (ogfZ fibClass) = (fibClass.count 0 : ℤ) by
      simp [ogfZ, coeff_ogf]]
    simp [fibClass_count_zero, PowerSeries.coeff_mul_X_pow']
  · have hshiftX : coeff (m + 1) (ogfZ fibClass * PowerSeries.X) =
        (fibClass.count m : ℤ) := by
      rw [PowerSeries.coeff_succ_mul_X]
      simp [ogfZ, coeff_ogf]
    rw [map_sub, map_sub, hshiftX]
    cases m with
    | zero =>
        simp [ogfZ, coeff_ogf, fibClass_count_eq_fib, PowerSeries.coeff_mul_X_pow',
          PowerSeries.coeff_one]
    | succ m =>
        have hshiftX2 :
            coeff (m + 2) (ogfZ fibClass * PowerSeries.X ^ 2) =
              (fibClass.count m : ℤ) := by
          rw [show m + 2 = m + 2 by rfl]
          rw [PowerSeries.coeff_mul_X_pow]
          simp [ogfZ, coeff_ogf]
        rw [hshiftX2]
        rw [show coeff (m + 2) (ogfZ fibClass) = (fibClass.count (m + 2) : ℤ) by
          simp [ogfZ, coeff_ogf]]
        rw [show (fibClass.count (m + 1) : ℤ) = coeff (m + 1) (ogfZ fibClass) by
          simp [ogfZ, coeff_ogf]]
        simp [ogfZ, coeff_ogf, fibClass_count_eq_fib, Nat.fib_add_two]

/-- The OGF of Fibonacci compositions has [zⁿ] = fib(n+1). -/
theorem fibClass_ogfZ_coeff (n : ℕ) :
    PowerSeries.coeff n (ogfZ fibClass) = (Nat.fib (n + 1) : ℤ) := by
  unfold ogfZ
  rw [PowerSeries.coeff_map, coeff_ogf, fibClass_count_eq_fib]
  rfl

/-! ## Parameter: number of parts -/

/-- Number of parts in a fibClass composition. -/
def fibNumParts : Parameter fibClass := List.length

private lemma fibClass_jointCount_fibNumParts_eq_one_of_unique
    {n k : ℕ} (x₀ : fibClass.Obj)
    (hx₀ : x₀ ∈ fibClass.level n)
    (hnum₀ : fibNumParts x₀ = k)
    (huniq : ∀ x : fibClass.Obj,
      x ∈ fibClass.level n → fibNumParts x = k → x = x₀) :
    fibClass.jointCount fibNumParts n k = 1 := by
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

/-- Sanity: small jointCount values. -/
example : fibClass.jointCount fibNumParts 0 0 = 1 := by
  apply fibClass_jointCount_fibNumParts_eq_one_of_unique ([] : fibClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx _hnum
    have hsize : x.foldr (fun b acc => stepClass.size b + acc) 0 = 0 := by
      exact (CombinatorialClass.level_mem_iff (C := fibClass) x).mp hx
    cases x with
    | nil => rfl
    | cons a xs =>
        simp only [List.foldr_cons] at hsize
        rcases a with a | a
        · have hbad : stepClass.size (Sum.inl a) = 0 := by omega
          change (1 : ℕ) = 0 at hbad
          omega
        · have hbad : stepClass.size (Sum.inr a) = 0 := by omega
          change (2 : ℕ) = 0 at hbad
          omega

example : fibClass.jointCount fibNumParts 1 1 = 1 := by
  apply fibClass_jointCount_fibNumParts_eq_one_of_unique
    ([Sum.inl ()] : fibClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => stepClass.size b + acc) 0 = 1 := by
      exact (CombinatorialClass.level_mem_iff (C := fibClass) x).mp hx
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
            · have hbad := hsize
              change (2 : ℕ) = 1 at hbad
              omega
        | cons b xs =>
            simp at hnum

example : fibClass.jointCount fibNumParts 2 1 = 1 := by
  apply fibClass_jointCount_fibNumParts_eq_one_of_unique
    ([Sum.inr ()] : fibClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => stepClass.size b + acc) 0 = 2 := by
      exact (CombinatorialClass.level_mem_iff (C := fibClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            rcases a with a | a
            · have hbad := hsize
              change (1 : ℕ) = 2 at hbad
              omega
            · cases a
              rfl
        | cons b xs =>
            simp at hnum

example : fibClass.jointCount fibNumParts 2 2 = 1 := by
  apply fibClass_jointCount_fibNumParts_eq_one_of_unique
    ([Sum.inl (), Sum.inl ()] : fibClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => stepClass.size b + acc) 0 = 2 := by
      exact (CombinatorialClass.level_mem_iff (C := fibClass) x).mp hx
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
                rcases a with a | a
                · rcases b with b | b
                  · cases a
                    cases b
                    rfl
                  · have hbad := hsize
                    change (1 : ℕ) + 2 = 2 at hbad
                    omega
                · rcases b with _ | _
                  · have hbad := hsize
                    change (2 : ℕ) + 1 = 2 at hbad
                    omega
                  · have hbad := hsize
                    change (2 : ℕ) + 2 = 2 at hbad
                    omega
            | cons c xs =>
                simp at hnum

example (n : ℕ) :
    fibClass.egf.coeff n = (Nat.fib (n + 1) : ℚ) / n.factorial := by
  rw [CombinatorialClass.coeff_egf, fibClass_count_eq_fib]
