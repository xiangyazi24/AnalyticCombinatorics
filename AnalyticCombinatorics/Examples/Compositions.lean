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
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences

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
