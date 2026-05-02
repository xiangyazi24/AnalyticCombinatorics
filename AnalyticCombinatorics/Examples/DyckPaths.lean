/-
  Analytic Combinatorics — Examples
  Dyck Paths and Catalan Numbers

  A Dyck path of length 2n is represented by Mathlib's `DyckWord`,
  a list of up/down steps with every prefix having at least as many
  up-steps as down-steps and with equal total counts.

  Reference: Flajolet & Sedgewick, Example I.6.
-/
import Mathlib.Combinatorics.Enumerative.DyckWord
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

set_option linter.style.show false
set_option linter.style.nativeDecide false

open CombinatorialClass

/-- Dyck paths, represented by Mathlib's `DyckWord`. -/
abbrev DyckPath := DyckWord

/-- The combinatorial class of Dyck paths, sized by semilength. -/
noncomputable def dyckPathClass : CombinatorialClass where
  Obj := DyckPath
  size p := p.semilength
  finite_level n := by
    classical
    change Set.Finite {p : DyckPath | p.semilength = n}
    let s : Finset DyckPath :=
      (Finset.univ : Finset {p : DyckPath // p.semilength = n}).image Subtype.val
    exact Set.Finite.ofFinset s (by intro p; simp [s])

/-- The number of Dyck paths of semilength `n` is the n-th Catalan number. -/
theorem dyckPathClass_count (n : ℕ) :
    dyckPathClass.count n = _root_.catalan n := by
  classical
  simp only [CombinatorialClass.count]
  have hcard :
      (dyckPathClass.level n).card = Fintype.card {p : DyckPath // p.semilength = n} := by
    rw [← Finset.card_univ]
    let fwd :
        (p : DyckPath) → p ∈ dyckPathClass.level n → {p : DyckPath // p.semilength = n} :=
      fun p hp => ⟨p, (CombinatorialClass.level_mem_iff (C := dyckPathClass) p).mp hp⟩
    apply Finset.card_bij fwd
    · intro p hp
      exact Finset.mem_univ _
    · intro a ha b hb h
      exact Subtype.ext_iff.mp h
    · intro q hq
      refine ⟨q.1, ?_, ?_⟩
      · exact (CombinatorialClass.level_mem_iff (C := dyckPathClass) q.1).mpr q.2
      · rfl
  rw [hcard]
  exact DyckWord.card_dyckWord_semilength_eq_catalan n

/-! Sanity checks:
    C₀=1, C₁=1, C₂=2, C₃=5, C₄=14, C₅=42,
    C₆=132, C₇=429, C₈=1430, C₉=4862, C₁₀=16796,
    C₁₁=58786, C₁₂=208012, C₁₃=742900, C₁₄=2674440,
    C₁₅=9694845, C₁₆=35357670, C₁₇=129644790, C₁₈=477638700,
    C₁₉=1767263190, C₂₀=6564120420, C₂₁=24466267020,
    C₂₂=91482563640, C₂₃=343059613650, C₂₄=1289904147324. -/

example : dyckPathClass.count 0 = 1 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 1 = 1 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 2 = 2 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 3 = 5 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 4 = 14 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 5 = 42 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 6 = 132 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 7 = 429 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 8 = 1430 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 9 = 4862 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 10 = 16796 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 11 = 58786 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 12 = 208012 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 13 = 742900 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 14 = 2674440 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 15 = 9694845 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 16 = 35357670 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 17 = 129644790 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 18 = 477638700 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 19 = 1767263190 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 20 = 6564120420 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 21 = 24466267020 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 22 = 91482563640 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 23 = 343059613650 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide
example : dyckPathClass.count 24 = 1289904147324 := by
  rw [dyckPathClass_count]
  rw [_root_.catalan_eq_centralBinom_div]
  native_decide

-- TODO: prove the OGF quadratic equation `D(z) = 1 + z * D(z)^2`.
