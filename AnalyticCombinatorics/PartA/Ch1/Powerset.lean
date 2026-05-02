/-
  Chapter I § I.2 — Powersets (PSET construction)

  PSET(B) is the class of finite subsets of objects from B. Each object may
  occur at most once, and the size of a subset is the sum of the sizes of its
  elements.

  Reference: F&S Proposition I.2.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

set_option linter.style.show false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

open PowerSeries

namespace CombinatorialClass

/-- PSET(B): finite subsets of objects from B, with size given by the sum of
the sizes of the selected objects. The hypothesis `B.count 0 = 0` is the
standard admissibility condition for PSET in the ordinary symbolic method. -/
noncomputable def psetClass (B : CombinatorialClass) (hB : B.count 0 = 0)
    [DecidableEq B.Obj] : CombinatorialClass where
  Obj := Finset B.Obj
  size := fun s => ∑ b ∈ s, B.size b
  finite_level n := by
    let S : Set B.Obj := ⋃ k : Fin (n + 1), ↑(B.level k.val)
    have hSfin : S.Finite := Set.finite_iUnion (fun k => (B.level k.val).finite_toSet)
    apply Set.Finite.subset ((hSfin.toFinset).powerset.finite_toSet)
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    simp only [Finset.mem_coe, Finset.mem_powerset]
    intro b hb
    rw [Set.Finite.mem_toFinset]
    simp only [S, Set.mem_iUnion, Finset.mem_coe]
    have hle : B.size b ≤ ∑ a ∈ s, B.size a :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb
    exact ⟨⟨B.size b, by omega⟩, (level_mem_iff (C := B) b).mpr rfl⟩

namespace psetClass

private lemma size_pos {B : CombinatorialClass} (h : B.count 0 = 0) (b : B.Obj) :
    1 ≤ B.size b := by
  rcases Nat.eq_zero_or_pos (B.size b) with h0 | hp
  · exfalso
    have hmem : b ∈ B.level 0 := (level_mem_iff (C := B) b).mpr h0
    have hcard_pos : 0 < (B.level 0).card := Finset.card_pos.mpr ⟨b, hmem⟩
    simp only [count] at h
    omega
  · omega

private lemma card_le_size_sum {B : CombinatorialClass} (h : B.count 0 = 0)
    [DecidableEq B.Obj] (s : Finset B.Obj) :
    s.card ≤ ∑ b ∈ s, B.size b := by
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun b _ => size_pos h b

end psetClass

/-- The empty subset is the unique PSET object of size `0`. -/
theorem psetClass_count_zero (B : CombinatorialClass) (h : B.count 0 = 0)
    [DecidableEq B.Obj] :
    (psetClass B h).count 0 = 1 := by
  simp only [count]
  rw [Finset.card_eq_one]
  refine ⟨(∅ : Finset B.Obj), ?_⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · apply (level_mem_iff (C := psetClass B h) (n := 0) (∅ : Finset B.Obj)).mpr
    change (∑ b ∈ (∅ : Finset B.Obj), B.size b) = 0
    simp
  · intro s hs
    have hsum : (∑ b ∈ s, B.size b) = 0 :=
      (level_mem_iff (C := psetClass B h) (n := 0) s).mp hs
    apply Finset.eq_empty_of_forall_notMem
    intro b hb
    have hle : B.size b ≤ ∑ a ∈ s, B.size a :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb
    have hpos := psetClass.size_pos h b
    omega

/-- PSET objects of size `1` are exactly singleton subsets of size-`1` objects
from the base class. -/
theorem psetClass_count_one (B : CombinatorialClass) (h : B.count 0 = 0)
    [DecidableEq B.Obj] :
    (psetClass B h).count 1 = B.count 1 := by
  simp only [count]
  symm
  apply Finset.card_bij (fun b _ => ({b} : Finset B.Obj))
  · intro b hb
    apply (level_mem_iff (C := psetClass B h) (n := 1) ({b} : Finset B.Obj)).mpr
    have hbsize : B.size b = 1 := (level_mem_iff (C := B) (n := 1) b).mp hb
    simpa [hbsize]
  · intro b₁ _ b₂ _ hsingle
    exact Finset.singleton_inj.mp hsingle
  · intro s hs
    have hsum : (∑ b ∈ s, B.size b) = 1 :=
      (level_mem_iff (C := psetClass B h) (n := 1) s).mp hs
    have hcard_le : s.card ≤ 1 := by
      have hle := psetClass.card_le_size_sum h s
      omega
    have hne : s.Nonempty := by
      by_contra hnot
      rw [Finset.not_nonempty_iff_eq_empty] at hnot
      subst s
      simp at hsum
    have hcard : s.card = 1 := by
      have hpos : 0 < s.card := Finset.card_pos.mpr hne
      omega
    obtain ⟨b, hs_single⟩ := Finset.card_eq_one.mp hcard
    have hbsize : B.size b = 1 := by
      simpa [hs_single] using hsum
    refine ⟨b, (level_mem_iff (C := B) (n := 1) b).mpr hbsize, ?_⟩
    exact hs_single.symm

private lemma Atom_count_zero : Atom.count 0 = 0 := by
  simp only [count]
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  have hsize : Atom.size x = 0 := (level_mem_iff (C := Atom) (n := 0) x).mp hx
  change (1 : ℕ) = 0 at hsize
  omega

private instance Atom_subsingleton : Subsingleton Atom.Obj :=
  inferInstanceAs (Subsingleton Unit)

private lemma Atom_count_one : Atom.count 1 = 1 := by
  simp only [count]
  rw [Finset.card_eq_one]
  refine ⟨(), ?_⟩
  ext x
  simp only [Finset.mem_singleton]
  rw [level_mem_iff (C := Atom) (n := 1) x]
  change (1 : ℕ) = 1 ↔ x = ()
  constructor
  · intro _
    exact Subsingleton.elim x ()
  · intro _
    rfl

private instance Atom_decidableEq : DecidableEq Atom.Obj :=
  inferInstanceAs (DecidableEq Unit)

/-- PSET(Atom) has one object of size `0`: the empty subset. -/
theorem psetClass_Atom_count_zero :
    (psetClass Atom Atom_count_zero).count 0 = 1 :=
  psetClass_count_zero Atom Atom_count_zero

/-- PSET(Atom) has one object of size `1`: the singleton atom subset. -/
theorem psetClass_Atom_count_one :
    (psetClass Atom Atom_count_zero).count 1 = 1 := by
  rw [psetClass_count_one Atom Atom_count_zero, Atom_count_one]

/-- PSET(Atom) has no object of size `2`, since the unique atom can be used
at most once. -/
theorem psetClass_Atom_count_two :
    (psetClass Atom Atom_count_zero).count 2 = 0 := by
  simp only [count]
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro s hs
  have hsum : (∑ b ∈ s, Atom.size b) = 2 :=
    (level_mem_iff (C := psetClass Atom Atom_count_zero) (n := 2) s).mp hs
  have hsum_card : (∑ b ∈ s, Atom.size b) = s.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro b _
    change (1 : ℕ) = 1
    rfl
  have hcard_le : s.card ≤ 1 := Finset.card_le_one_of_subsingleton s
  omega

/-- A base class with two distinct atoms of size `1`. -/
def twoAtoms : CombinatorialClass where
  Obj := Bool
  size _ := 1
  finite_level _ := Set.finite_univ.subset (Set.subset_univ _)

private instance twoAtoms_decidableEq : DecidableEq twoAtoms.Obj :=
  inferInstanceAs (DecidableEq Bool)

private instance twoAtoms_fintype : Fintype twoAtoms.Obj :=
  inferInstanceAs (Fintype Bool)

private lemma twoAtoms_count_zero : twoAtoms.count 0 = 0 := by
  simp only [count]
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  have hsize : twoAtoms.size x = 0 :=
    (level_mem_iff (C := twoAtoms) (n := 0) x).mp hx
  change (1 : ℕ) = 0 at hsize
  omega

private lemma twoAtoms_count_one : twoAtoms.count 1 = 2 := by
  simp only [count]
  have hlevel : twoAtoms.level 1 = Finset.univ := by
    ext x
    rw [level_mem_iff (C := twoAtoms) (n := 1) x]
    change (1 : ℕ) = 1 ↔ x ∈ (Finset.univ : Finset twoAtoms.Obj)
    simp
  rw [hlevel]
  change (Finset.univ : Finset Bool).card = 2
  simp

/-- PSET(twoAtoms) has one object of size `0`: the empty subset. -/
theorem psetClass_twoAtoms_count_zero :
    (psetClass twoAtoms twoAtoms_count_zero).count 0 = 1 :=
  psetClass_count_zero twoAtoms twoAtoms_count_zero

/-- PSET(twoAtoms) has two objects of size `1`: either singleton atom subset. -/
theorem psetClass_twoAtoms_count_one :
    (psetClass twoAtoms twoAtoms_count_zero).count 1 = 2 := by
  rw [psetClass_count_one twoAtoms twoAtoms_count_zero, twoAtoms_count_one]

/-- PSET(twoAtoms) has one object of size `2`: the subset containing both atoms. -/
theorem psetClass_twoAtoms_count_two :
    (psetClass twoAtoms twoAtoms_count_zero).count 2 = 1 := by
  simp only [count]
  rw [Finset.card_eq_one]
  refine ⟨(Finset.univ : Finset twoAtoms.Obj), ?_⟩
  ext s
  simp only [Finset.mem_singleton]
  rw [level_mem_iff (C := psetClass twoAtoms twoAtoms_count_zero) (n := 2) s]
  show (∑ b ∈ s, twoAtoms.size b) = 2 ↔ s = (Finset.univ : Finset twoAtoms.Obj)
  constructor
  · intro hsum
    have hsum_card : (∑ b ∈ s, twoAtoms.size b) = s.card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro b _
      change (1 : ℕ) = 1
      rfl
    have hcard : s.card = Fintype.card twoAtoms.Obj := by
      have htwo : Fintype.card twoAtoms.Obj = 2 := by
        change Fintype.card Bool = 2
        simp
      simp [hsum_card] at hsum
      omega
    exact (Finset.card_eq_iff_eq_univ s).mp hcard
  · rintro rfl
    change (∑ b ∈ (Finset.univ : Finset Bool), (1 : ℕ)) = 2
    simp

end CombinatorialClass
