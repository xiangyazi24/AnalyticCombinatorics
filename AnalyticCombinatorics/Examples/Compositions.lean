/-
  Analytic Combinatorics — Examples
  Integer compositions

  A composition of n is a sequence of positive integers summing to n.
  Build as SEQ(I), where I is the class of positive integers with size = value.

  OGF: I(z) = z + z² + z³ + … = z/(1 - z),
       COMPOSITION(z) = 1 / (1 - z/(1 - z)) = (1 - z)/(1 - 2z),
       coefficient: [zⁿ] = 2^{n-1} for n ≥ 1, and 1 for n = 0.

  Reference: F&S Example I.7.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Fib.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import AnalyticCombinatorics.PartA.Ch3.Parameters

set_option linter.style.show false
set_option linter.style.multiGoal false

open PowerSeries CombinatorialClass Finset

/-- Positive integers as a combinatorial class: each k ≥ 1 has size k. -/
def posIntClass : CombinatorialClass where
  Obj := {n : ℕ // 1 ≤ n}
  size := fun ⟨n, _⟩ => n
  finite_level n := by
    by_cases h : 1 ≤ n
    · -- level n is the singleton {⟨n, h⟩}
      apply Set.Finite.subset (Set.finite_singleton (⟨n, h⟩ : {k : ℕ // 1 ≤ k}))
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨v, hv⟩ := x
      show (⟨v, hv⟩ : {k : ℕ // 1 ≤ k}) ∈ ({⟨n, h⟩} : Set {k : ℕ // 1 ≤ k})
      have hvn : v = n := hx
      subst hvn
      rfl
    · -- level n is empty (no positive integer has size 0)
      apply Set.Finite.subset Set.finite_empty
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨v, hv⟩ := x
      change v = n at hx
      omega

namespace posIntClass

/-- No positive integer has size 0. -/
lemma count_zero : posIntClass.count 0 = 0 := by
  simp only [count]
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hsz : posIntClass.size x = 0 :=
    (posIntClass.finite_level 0).mem_toFinset.mp hx
  obtain ⟨v, hv⟩ := x
  change v = 0 at hsz
  omega

/-- For each k ≥ 1, exactly one positive integer has size k. -/
lemma count_pos {k : ℕ} (hk : 1 ≤ k) : posIntClass.count k = 1 := by
  show (posIntClass.level k).card = 1
  rw [Finset.card_eq_one]
  refine ⟨⟨k, hk⟩, ?_⟩
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hsz : posIntClass.size x = k :=
      (posIntClass.finite_level k).mem_toFinset.mp hx
    obtain ⟨v, hv⟩ := x
    change v = k at hsz
    subst hsz
    exact Finset.mem_singleton_self _
  · rw [Finset.mem_singleton] at hx
    subst hx
    exact (posIntClass.finite_level k).mem_toFinset.mpr rfl

end posIntClass

/-- The class of integer compositions: sequences of positive integers. -/
noncomputable def compositionClass : CombinatorialClass :=
  seqClass posIntClass posIntClass.count_zero

/-- Empty composition is the unique composition of 0. -/
theorem compositionClass_count_zero : compositionClass.count 0 = 1 := by
  show (seqClass posIntClass _).count 0 = 1
  rw [seqClass.count_zero]

/-- Recurrence: count(n+1) = ∑_{j=0}^{n} count(j). -/
private lemma count_succ_eq_sum (n : ℕ) :
    compositionClass.count (n + 1) =
      ∑ j ∈ Finset.range (n + 1), compositionClass.count j := by
  show (seqClass posIntClass _).count (n + 1) = _
  rw [seqClass.count_succ]
  -- LHS: ∑ p ∈ antidiag (n+1), posIntClass.count p.1 * compositionClass.count p.2
  -- Convert antidiag to range via the bijection k ↦ (k, n+1-k):
  rw [show Finset.antidiagonal (n + 1)
        = (Finset.range (n + 2)).image (fun k => (k, n + 1 - k)) from ?_]
  · rw [Finset.sum_image]
    -- ∑ k ∈ range (n+2), posIntClass.count k * compositionClass.count (n+1-k)
    rw [Finset.sum_range_succ' _ (n + 1),
        posIntClass.count_zero, zero_mul, add_zero,
        ← Finset.sum_range_reflect _ (n + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [posIntClass.count_pos (by omega), one_mul]
    congr 1; omega
    -- Injectivity of (k ↦ (k, n+1-k)) on range (n+2)
    intros a _ b _ heq
    exact (Prod.mk.injEq _ _ _ _).mp heq |>.1
  · ext ⟨k, m⟩
    simp only [Finset.mem_antidiagonal, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    refine ⟨fun h => ⟨k, by omega, by omega, by omega⟩,
            fun ⟨a, _, ha1, ha2⟩ => by omega⟩

/-- Doubling recurrence: count(n+2) = 2 · count(n+1) for n ≥ 0.
    Follows from count_succ_eq_sum at n+1 vs n. -/
private lemma count_succ_succ_eq (n : ℕ) :
    compositionClass.count (n + 2) = 2 * compositionClass.count (n + 1) := by
  rw [count_succ_eq_sum (n + 1), Finset.sum_range_succ, ← count_succ_eq_sum n, two_mul]

/-- The number of compositions of n+1 equals 2ⁿ. -/
theorem compositionClass_count_succ (n : ℕ) :
    compositionClass.count (n + 1) = 2 ^ n := by
  induction n with
  | zero =>
    -- count 1 = sum over range 1 of count = count 0 = 1 = 2^0
    rw [count_succ_eq_sum, Finset.sum_range_one, compositionClass_count_zero, pow_zero]
  | succ m ih =>
    rw [count_succ_succ_eq, ih, pow_succ]; ring

/-- Closed form for the OGF of integer compositions: `(1 - z)/(1 - 2z)`. -/
theorem compositionClass_ogfZ_mul_one_sub_two_X :
    ogfZ compositionClass * (1 - 2 * PowerSeries.X) = 1 - PowerSeries.X := by
  rw [show ogfZ compositionClass * (1 - 2 * PowerSeries.X) =
      ogfZ compositionClass - 2 * (ogfZ compositionClass * PowerSeries.X) by ring]
  ext n
  rcases n with _ | m
  · simp only [map_sub]
    rw [show coeff 0 (ogfZ compositionClass) = (compositionClass.count 0 : ℤ) by
      simp [ogfZ, coeff_ogf]]
    simp [compositionClass_count_zero]
  · have hshift : coeff (m + 1) (2 * (ogfZ compositionClass * PowerSeries.X)) =
        2 * (compositionClass.count m : ℤ) := by
      rw [show (2 : PowerSeries ℤ) = PowerSeries.C (2 : ℤ) by
        ext n
        simp]
      rw [PowerSeries.coeff_C_mul]
      rw [PowerSeries.coeff_succ_mul_X]
      simp [ogfZ, coeff_ogf]
    rw [map_sub, hshift]
    cases m with
    | zero =>
        simp [ogfZ, coeff_ogf, compositionClass_count_succ,
          compositionClass_count_zero, PowerSeries.coeff_X]
    | succ m =>
        simp [ogfZ, coeff_ogf, compositionClass_count_succ, PowerSeries.coeff_X]
        ring

/-! Sanity checks: 1 composition of 0, 1 of 1, 2 of 2, 4 of 3, 8 of 4. -/
example : compositionClass.count 0 = 1 := compositionClass_count_zero
example : compositionClass.count 1 = 1 := compositionClass_count_succ 0
example : compositionClass.count 2 = 2 := compositionClass_count_succ 1
example : compositionClass.count 4 = 8 := compositionClass_count_succ 3
example : compositionClass.count 3 = 4 := compositionClass_count_succ 2
example : compositionClass.count 5 = 16 := compositionClass_count_succ 4
example : compositionClass.count 6 = 32 := compositionClass_count_succ 5
example : compositionClass.count 7 = 64 := compositionClass_count_succ 6

/-- Closed form for n ≥ 1: count of compositions of n equals 2^(n-1). -/
theorem compositionClass_count_eq_pow_pred (n : ℕ) (hn : 1 ≤ n) :
    compositionClass.count n = 2 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [compositionClass_count_succ]
  congr 1

/-- The OGF of compositions has coefficient 2^(n-1) for n ≥ 1 over ℤ. -/
theorem compositionClass_ogfZ_coeff_pos (n : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff n (ogfZ compositionClass) = (2 ^ (n - 1) : ℤ) := by
  unfold ogfZ
  rw [PowerSeries.coeff_map]
  rw [coeff_ogf]
  rw [compositionClass_count_eq_pow_pred n hn]
  push_cast
  rfl

/-- Sum identity: 2 · count(n+1) = count(n+2). Linear recurrence. -/
example (n : ℕ) :
    2 * compositionClass.count (n + 1) = compositionClass.count (n + 2) := by
  rw [compositionClass_count_succ, compositionClass_count_succ, pow_succ]
  ring

/-- EGF coefficient: [zⁿ] compositionClass.egf = compositionClass.count n / n!
    = 2^(n-1) / n! for n ≥ 1, 1 for n = 0. -/
example : compositionClass.egf.coeff 0 = 1 := by
  rw [CombinatorialClass.coeff_egf, compositionClass_count_zero]
  simp

example (n : ℕ) (hn : 1 ≤ n) :
    compositionClass.egf.coeff n = (2 ^ (n - 1) : ℚ) / n.factorial := by
  rw [CombinatorialClass.coeff_egf, compositionClass_count_eq_pow_pred n hn]
  push_cast
  rfl

/-! ## Parameter: number of parts -/

/-- Number of parts of a composition (= list length). -/
def numParts : Parameter compositionClass := List.length

private lemma compositionClass_jointCount_numParts_eq_one_of_unique
    {n k : ℕ} (x₀ : compositionClass.Obj)
    (hx₀ : x₀ ∈ compositionClass.level n)
    (hnum₀ : numParts x₀ = k)
    (huniq : ∀ x : compositionClass.Obj,
      x ∈ compositionClass.level n → numParts x = k → x = x₀) :
    compositionClass.jointCount numParts n k = 1 := by
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

private lemma compositionClass_jointCount_numParts_eq_two_of_unique_pair
    {n k : ℕ} (x₁ x₂ : compositionClass.Obj)
    (hx₁ : x₁ ∈ compositionClass.level n)
    (hx₂ : x₂ ∈ compositionClass.level n)
    (hnum₁ : numParts x₁ = k)
    (hnum₂ : numParts x₂ = k)
    (hne : x₁ ≠ x₂)
    (huniq : ∀ x : compositionClass.Obj,
      x ∈ compositionClass.level n → numParts x = k → x = x₁ ∨ x = x₂) :
    compositionClass.jointCount numParts n k = 2 := by
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

/-- Sanity at small n: count compositions of n with exactly k parts. -/
example : compositionClass.jointCount numParts 0 0 = 1 := by
  apply compositionClass_jointCount_numParts_eq_one_of_unique ([] : compositionClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx _hnum
    have hsize : x.foldr (fun b acc => posIntClass.size b + acc) 0 = 0 := by
      exact (CombinatorialClass.level_mem_iff (C := compositionClass) x).mp hx
    cases x with
    | nil => rfl
    | cons a xs =>
        simp only [List.foldr_cons] at hsize
        obtain ⟨v, hv⟩ := a
        change v + xs.foldr (fun b acc => posIntClass.size b + acc) 0 = 0 at hsize
        omega

example : compositionClass.jointCount numParts 1 1 = 1 := by
  apply compositionClass_jointCount_numParts_eq_one_of_unique
    ([⟨1, by norm_num⟩] : compositionClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => posIntClass.size b + acc) 0 = 1 := by
      exact (CombinatorialClass.level_mem_iff (C := compositionClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            obtain ⟨v, hv⟩ := a
            change v + 0 = 1 at hsize
            have hv1 : v = 1 := by omega
            subst v
            simp
        | cons b xs =>
            simp at hnum

example : compositionClass.jointCount numParts 2 1 = 1 := by
  apply compositionClass_jointCount_numParts_eq_one_of_unique
    ([⟨2, by norm_num⟩] : compositionClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => posIntClass.size b + acc) 0 = 2 := by
      exact (CombinatorialClass.level_mem_iff (C := compositionClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            obtain ⟨v, hv⟩ := a
            change v + 0 = 2 at hsize
            have hv2 : v = 2 := by omega
            subst v
            simp
        | cons b xs =>
            simp at hnum

example : compositionClass.jointCount numParts 2 2 = 1 := by
  apply compositionClass_jointCount_numParts_eq_one_of_unique
    ([⟨1, by norm_num⟩, ⟨1, by norm_num⟩] : compositionClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => posIntClass.size b + acc) 0 = 2 := by
      exact (CombinatorialClass.level_mem_iff (C := compositionClass) x).mp hx
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
                obtain ⟨av, hav⟩ := a
                obtain ⟨bv, hbv⟩ := b
                change av + (bv + 0) = 2 at hsize
                have hav1 : av = 1 := by omega
                have hbv1 : bv = 1 := by omega
                subst av
                subst bv
                simp
            | cons c xs =>
                simp at hnum

example : compositionClass.jointCount numParts 3 1 = 1 := by
  apply compositionClass_jointCount_numParts_eq_one_of_unique
    ([⟨3, by norm_num⟩] : compositionClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => posIntClass.size b + acc) 0 = 3 := by
      exact (CombinatorialClass.level_mem_iff (C := compositionClass) x).mp hx
    change x.length = 1 at hnum
    cases x with
    | nil => simp at hnum
    | cons a xs =>
        cases xs with
        | nil =>
            simp only [List.foldr_cons, List.foldr_nil] at hsize
            obtain ⟨v, hv⟩ := a
            change v + 0 = 3 at hsize
            have hv3 : v = 3 := by omega
            subst v
            simp
        | cons b xs =>
            simp at hnum

example : compositionClass.jointCount numParts 3 2 = 2 := by
  apply compositionClass_jointCount_numParts_eq_two_of_unique_pair
    ([⟨1, by norm_num⟩, ⟨2, by norm_num⟩] : compositionClass.Obj)
    ([⟨2, by norm_num⟩, ⟨1, by norm_num⟩] : compositionClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · rfl
  · intro h
    injection h with hhead _
    norm_num at hhead
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => posIntClass.size b + acc) 0 = 3 := by
      exact (CombinatorialClass.level_mem_iff (C := compositionClass) x).mp hx
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
                obtain ⟨av, hav⟩ := a
                obtain ⟨bv, hbv⟩ := b
                change av + (bv + 0) = 3 at hsize
                have hav_cases : av = 1 ∨ av = 2 := by omega
                rcases hav_cases with hav1 | hav2
                · have hbv2 : bv = 2 := by omega
                  subst av
                  subst bv
                  left
                  simp
                · have hbv1 : bv = 1 := by omega
                  subst av
                  subst bv
                  right
                  simp
            | cons c xs =>
                simp at hnum

example : compositionClass.jointCount numParts 3 3 = 1 := by
  apply compositionClass_jointCount_numParts_eq_one_of_unique
    ([⟨1, by norm_num⟩, ⟨1, by norm_num⟩, ⟨1, by norm_num⟩] : compositionClass.Obj)
  · rw [CombinatorialClass.level_mem_iff]
    rfl
  · rfl
  · intro x hx hnum
    have hsize : x.foldr (fun b acc => posIntClass.size b + acc) 0 = 3 := by
      exact (CombinatorialClass.level_mem_iff (C := compositionClass) x).mp hx
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
                    obtain ⟨av, hav⟩ := a
                    obtain ⟨bv, hbv⟩ := b
                    obtain ⟨cv, hcv⟩ := c
                    change av + (bv + (cv + 0)) = 3 at hsize
                    have hav1 : av = 1 := by omega
                    have hbv1 : bv = 1 := by omega
                    have hcv1 : cv = 1 := by omega
                    subst av
                    subst bv
                    subst cv
                    simp
                | cons d xs =>
                    simp at hnum

example : compositionClass.count 8 = 128 := compositionClass_count_succ 7
example : compositionClass.count 10 = 512 := compositionClass_count_succ 9
example : compositionClass.count 12 = 2048 := compositionClass_count_succ 11

/-! ## Compositions into parts of size at least 2 -/

/-- Positive integers with size ≥ 2: each k ≥ 2 has size k. -/
def posIntGe2Class : CombinatorialClass where
  Obj := {n : ℕ // 2 ≤ n}
  size := fun ⟨n, _⟩ => n
  finite_level n := by
    by_cases h : 2 ≤ n
    · apply Set.Finite.subset (Set.finite_singleton (⟨n, h⟩ : {k : ℕ // 2 ≤ k}))
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨v, hv⟩ := x
      have hvn : v = n := hx
      subst hvn
      rfl
    · apply Set.Finite.subset Set.finite_empty
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨v, hv⟩ := x
      change v = n at hx
      omega

namespace posIntGe2Class

/-- count 0 = 0 (no part of size 0). -/
lemma count_zero : posIntGe2Class.count 0 = 0 := by
  change (posIntGe2Class.level 0).card = 0
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hsz : posIntGe2Class.size x = 0 :=
    (posIntGe2Class.finite_level 0).mem_toFinset.mp hx
  obtain ⟨v, hv⟩ := x
  change v = 0 at hsz
  omega

/-- count 1 = 0 (no part of size 1). -/
lemma count_one : posIntGe2Class.count 1 = 0 := by
  change (posIntGe2Class.level 1).card = 0
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hsz : posIntGe2Class.size x = 1 :=
    (posIntGe2Class.finite_level 1).mem_toFinset.mp hx
  obtain ⟨v, hv⟩ := x
  change v = 1 at hsz
  omega

/-- For each k ≥ 2, exactly one positive integer has size k. -/
lemma count_ge_two {k : ℕ} (hk : 2 ≤ k) : posIntGe2Class.count k = 1 := by
  change (posIntGe2Class.level k).card = 1
  rw [Finset.card_eq_one]
  refine ⟨⟨k, hk⟩, ?_⟩
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hsz : posIntGe2Class.size x = k :=
      (posIntGe2Class.finite_level k).mem_toFinset.mp hx
    obtain ⟨v, hv⟩ := x
    change v = k at hsz
    subst hsz
    exact Finset.mem_singleton_self _
  · rw [Finset.mem_singleton] at hx
    subst hx
    exact (posIntGe2Class.finite_level k).mem_toFinset.mpr rfl

end posIntGe2Class

/-- The class of compositions into parts of size ≥ 2. -/
noncomputable def compositionGe2Class : CombinatorialClass :=
  seqClass posIntGe2Class posIntGe2Class.count_zero

/-- Empty composition is the unique composition of 0. -/
theorem compositionGe2Class_count_zero : compositionGe2Class.count 0 = 1 := by
  change (seqClass posIntGe2Class posIntGe2Class.count_zero).count 0 = 1
  rw [seqClass.count_zero]

/-- There is no composition of 1 into parts of size ≥ 2. -/
theorem compositionGe2Class_count_one : compositionGe2Class.count 1 = 0 := by
  change (compositionGe2Class.level 1).card = 0
  rw [Finset.card_eq_zero]
  ext xs
  simp only [Finset.notMem_empty, iff_false]
  intro hxs
  have hsz : xs.foldr (fun b acc => posIntGe2Class.size b + acc) 0 = 1 :=
    (CombinatorialClass.level_mem_iff (C := compositionGe2Class) xs).mp hxs
  cases xs with
  | nil => simp at hsz
  | cons a xs =>
      obtain ⟨v, hv⟩ := a
      change v + xs.foldr (fun b acc => posIntGe2Class.size b + acc) 0 = 1 at hsz
      omega

/-- Recurrence: count(n+2) is the sum of all previous counts through n. -/
private lemma compositionGe2Class_count_succ_succ_eq_sum (n : ℕ) :
    compositionGe2Class.count (n + 2) =
      ∑ j ∈ Finset.range (n + 1), compositionGe2Class.count j := by
  change (seqClass posIntGe2Class posIntGe2Class.count_zero).count (n + 2) = _
  rw [show n + 2 = (n + 1) + 1 by omega]
  rw [seqClass.count_succ]
  rw [show (n + 1) + 1 = n + 2 by omega]
  rw [show Finset.antidiagonal (n + 2)
        = (Finset.range (n + 3)).image (fun k => (k, n + 2 - k)) from ?_]
  · rw [Finset.sum_image]
    · rw [Finset.sum_range_succ' _ (n + 2),
          posIntGe2Class.count_zero, zero_mul, add_zero]
      rw [Finset.sum_range_succ' _ (n + 1),
          posIntGe2Class.count_one, zero_mul, add_zero]
      rw [← Finset.sum_range_reflect _ (n + 1)]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [posIntGe2Class.count_ge_two (by omega), one_mul]
      congr 1
      omega
    · intros a _ b _ heq
      exact (Prod.mk.injEq _ _ _ _).mp heq |>.1
  · ext ⟨k, m⟩
    simp only [Finset.mem_antidiagonal, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    refine ⟨fun h => ⟨k, by omega, by omega, by omega⟩,
            fun ⟨a, _, ha1, ha2⟩ => by omega⟩

/-- Fibonacci recurrence for compositions into parts of size ≥ 2. -/
private lemma compositionGe2Class_count_add_three (n : ℕ) :
    compositionGe2Class.count (n + 3) =
      compositionGe2Class.count (n + 2) + compositionGe2Class.count (n + 1) := by
  rw [show n + 3 = (n + 1) + 2 by omega]
  rw [compositionGe2Class_count_succ_succ_eq_sum (n + 1)]
  rw [Finset.sum_range_succ]
  rw [← compositionGe2Class_count_succ_succ_eq_sum n]

/-- The number of compositions of n+2 into parts ≥ 2 equals fib(n+1). -/
theorem compositionGe2Class_count_succ_succ (n : ℕ) :
    compositionGe2Class.count (n + 2) = Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [compositionGe2Class_count_succ_succ_eq_sum, Finset.sum_range_one,
        compositionGe2Class_count_zero, Nat.fib_one]
  | one =>
      rw [compositionGe2Class_count_succ_succ_eq_sum, Finset.sum_range_succ,
        Finset.sum_range_one, compositionGe2Class_count_zero, compositionGe2Class_count_one,
        Nat.fib_two]
  | more n ih0 ih1 =>
      rw [show n + 1 + 1 + 2 = n + 4 by omega]
      rw [show n + 4 = (n + 1) + 3 by omega]
      rw [compositionGe2Class_count_add_three, ih0, ih1]
      rw [show n + 1 + 1 + 1 = (n + 1) + 2 by omega]
      rw [show Nat.fib (n + 2) + Nat.fib (n + 1) =
        Nat.fib (n + 1) + Nat.fib (n + 2) by ac_rfl]
      exact (Nat.fib_add_two (n := n + 1)).symm

/-- Closed form for n ≥ 2: count of compositions of n into parts ≥ 2 is fib(n-1). -/
theorem compositionGe2Class_count_eq_fib_pred (n : ℕ) (hn : 2 ≤ n) :
    compositionGe2Class.count n = Nat.fib (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [compositionGe2Class_count_succ_succ]
  congr 1

/-! Sanity checks: counts are 1, 0, 1, 1, 2, 3, 5, 8, ... -/
example : compositionGe2Class.count 0 = 1 := compositionGe2Class_count_zero
example : compositionGe2Class.count 1 = 0 := compositionGe2Class_count_one
example : compositionGe2Class.count 2 = 1 := compositionGe2Class_count_succ_succ 0
example : compositionGe2Class.count 3 = 1 := compositionGe2Class_count_succ_succ 1
example : compositionGe2Class.count 4 = 2 := compositionGe2Class_count_succ_succ 2
example : compositionGe2Class.count 5 = 3 := compositionGe2Class_count_succ_succ 3
example : compositionGe2Class.count 6 = 5 := compositionGe2Class_count_succ_succ 4
example : compositionGe2Class.count 7 = 8 := compositionGe2Class_count_succ_succ 5

/-! Basic identities for the sequence construction. -/

/-- count 0 = 1 (only empty composition has total 0). -/
example : compositionGe2Class.count 0 = 1 := by
  change (seqClass posIntGe2Class posIntGe2Class.count_zero).count 0 = 1
  rw [seqClass.count_zero]

/-- count 1 = 0 (no part of size 1, so no composition of total 1). -/
example : compositionGe2Class.count 1 = 0 := by
  change (seqClass posIntGe2Class posIntGe2Class.count_zero).count (0 + 1) = 0
  rw [seqClass.count_succ]
  rw [Finset.sum_eq_zero]
  intro p hp
  have hp_sum : p.1 + p.2 = 1 := Finset.mem_antidiagonal.mp hp
  rcases p with ⟨k, m⟩
  simp only at hp_sum
  cases k with
  | zero =>
      rw [posIntGe2Class.count_zero, zero_mul]
  | succ k =>
      cases k with
      | zero =>
          rw [posIntGe2Class.count_one, zero_mul]
      | succ k =>
          omega

namespace CombinatorialClass

noncomputable def ogfZ (A : CombinatorialClass) : PowerSeries ℤ :=
  A.ogf.map (algebraMap ℕ ℤ)

end CombinatorialClass

example : PowerSeries.coeff 0 (CombinatorialClass.ogfZ compositionClass) = (1 : ℤ) := by
  unfold CombinatorialClass.ogfZ
  rw [PowerSeries.coeff_map, coeff_ogf, compositionClass_count_zero]
  rfl
