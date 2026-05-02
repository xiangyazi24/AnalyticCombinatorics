/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I §3: Lattice paths and Catalan numbers.

  Dyck paths are represented by lists of up/down steps, with the usual
  prefix nonnegativity constraint and final height zero.  The class below is
  sized by semilength.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Trees

set_option linter.style.show false
set_option linter.style.nativeDecide false

open PowerSeries CombinatorialClass

/-! ## Dyck paths -/

/-- Up and down steps in a Dyck path. -/
inductive Step where
  | U
  | D
deriving DecidableEq, Repr

namespace Step

/-- All words of length `n` over the alphabet `{U, D}`. -/
def words : ℕ → Finset (List Step)
  | 0 => {[]}
  | n + 1 =>
      (words n).image (fun xs => Step.U :: xs) ∪
        (words n).image (fun xs => Step.D :: xs)

theorem mem_words_iff {xs : List Step} {n : ℕ} :
    xs ∈ words n ↔ xs.length = n := by
  revert xs
  induction n with
  | zero =>
      intro xs
      cases xs <;> simp [words]
  | succ n ih =>
      intro xs
      cases xs with
      | nil =>
          simp [words]
      | cons s xs =>
          cases s <;> simp [words, ih]

end Step

/-- Final height after starting at height `h`; down steps at height zero saturate. -/
def finalHeightFrom : ℕ → List Step → ℕ
  | h, [] => h
  | h, Step.U :: xs => finalHeightFrom (h + 1) xs
  | h, Step.D :: xs => finalHeightFrom (h - 1) xs

/-- Prefix nonnegativity, starting at height `h`, as a computable check. -/
def prefixesNonnegativeFrom : ℕ → List Step → Bool
  | _, [] => true
  | h, s :: xs =>
      match s with
      | Step.U => prefixesNonnegativeFrom (h + 1) xs
      | Step.D =>
          match h with
          | 0 => false
          | h' + 1 => prefixesNonnegativeFrom h' xs

/-- A Dyck path never goes below the axis and ends at height zero. -/
def isDyckPath (xs : List Step) : Prop :=
  prefixesNonnegativeFrom 0 xs = true ∧ finalHeightFrom 0 xs = 0

instance (xs : List Step) : Decidable (isDyckPath xs) := by
  unfold isDyckPath
  infer_instance

/-- Dyck paths bundled with their semilength. -/
structure DyckPath where
  semilength : ℕ
  steps : List Step
  is_dyck : isDyckPath steps
  length_steps : steps.length = 2 * semilength

namespace DyckPath

instance : DecidableEq DyckPath := by
  intro a b
  cases a with
  | mk an axs ady alen =>
  cases b with
  | mk bn bxs bdy blen =>
      by_cases hn : an = bn
      · by_cases hs : axs = bxs
        · subst bn
          subst bxs
          exact isTrue (by
            have hdy : ady = bdy := Subsingleton.elim _ _
            have hlen : alen = blen := Subsingleton.elim _ _
            subst hdy
            subst hlen
            rfl)
        · exact isFalse (by
            intro h
            exact hs (congrArg DyckPath.steps h))
      · exact isFalse (by
          intro h
          exact hn (congrArg DyckPath.semilength h))

/-- Explicit finite enumeration of Dyck paths of semilength `n`. -/
def ofSize (n : ℕ) : Finset DyckPath :=
  ((Step.words (2 * n)).filter isDyckPath).attach.image fun x =>
    { semilength := n
      steps := x.1
      is_dyck := (Finset.mem_filter.mp x.2).2
      length_steps := Step.mem_words_iff.mp (Finset.mem_filter.mp x.2).1 }

theorem mem_ofSize_iff {p : DyckPath} {n : ℕ} :
    p ∈ ofSize n ↔ p.semilength = n := by
  constructor
  · intro hp
    simp only [ofSize, Finset.mem_image, Finset.mem_attach] at hp
    obtain ⟨x, _, hp_eq⟩ := hp
    rw [← hp_eq]
  · intro hn
    simp only [ofSize, Finset.mem_image, Finset.mem_attach, true_and]
    have hmem : p.steps ∈ (Step.words (2 * n)).filter isDyckPath := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Step.mem_words_iff.mpr
        rw [p.length_steps, hn]
      · exact p.is_dyck
    refine ⟨⟨p.steps, hmem⟩, ?_⟩
    cases p with
    | mk sem steps hdy hlen =>
        simp only at hn
        subst sem
        simp

end DyckPath

/-- Dyck paths as a combinatorial class, counted by semilength. -/
def dyckPathClass : CombinatorialClass where
  Obj := DyckPath
  size := DyckPath.semilength
  finite_level n := by
    exact Set.Finite.ofFinset (DyckPath.ofSize n) fun p => by
      change p ∈ DyckPath.ofSize n ↔ p.semilength = n
      exact DyckPath.mem_ofSize_iff

/-- The abstract level set agrees with the explicit finite enumeration. -/
theorem dyckPathClass_level_eq (n : ℕ) :
    dyckPathClass.level n = DyckPath.ofSize n := by
  ext p
  rw [CombinatorialClass.level_mem_iff]
  exact DyckPath.mem_ofSize_iff.symm

/-- Counts can be computed from the explicit finite enumeration. -/
theorem dyckPathClass_count_eq_card (n : ℕ) :
    dyckPathClass.count n = (DyckPath.ofSize n).card := by
  rw [CombinatorialClass.count, dyckPathClass_level_eq]
  rfl

/-! ## Sanity checks -/

theorem dyckPath_count_zero : dyckPathClass.count 0 = 1 := by
  rw [dyckPathClass_count_eq_card]
  native_decide

theorem dyckPath_count_one : dyckPathClass.count 1 = 1 := by
  rw [dyckPathClass_count_eq_card]
  native_decide

theorem dyckPath_count_two : dyckPathClass.count 2 = 2 := by
  rw [dyckPathClass_count_eq_card]
  native_decide

theorem dyckPath_count_three : dyckPathClass.count 3 = 5 := by
  rw [dyckPathClass_count_eq_card]
  native_decide

theorem dyckPath_count_four : dyckPathClass.count 4 = 14 := by
  rw [dyckPathClass_count_eq_card]
  native_decide

/-! ## Initial Catalan values -/

theorem dyckPath_count_catalan_zero :
    dyckPathClass.count 0 = Nat.centralBinom 0 / (0 + 1) := by
  rw [dyckPath_count_zero]
  native_decide

theorem dyckPath_count_catalan_one :
    dyckPathClass.count 1 = Nat.centralBinom 1 / (1 + 1) := by
  rw [dyckPath_count_one]
  native_decide

theorem dyckPath_count_catalan_two :
    dyckPathClass.count 2 = Nat.centralBinom 2 / (2 + 1) := by
  rw [dyckPath_count_two]
  native_decide

theorem dyckPath_count_catalan_three :
    dyckPathClass.count 3 = Nat.centralBinom 3 / (3 + 1) := by
  rw [dyckPath_count_three]
  native_decide

theorem dyckPath_count_catalan_four :
    dyckPathClass.count 4 = Nat.centralBinom 4 / (4 + 1) := by
  rw [dyckPath_count_four]
  native_decide

/-! ## Agreement with binary trees for the initial Catalan values -/

theorem dyckPath_count_eq_binaryTree_zero :
    dyckPathClass.count 0 = binaryTreeClass.count 0 := by
  rw [dyckPath_count_zero, binaryTree_count_zero]

theorem dyckPath_count_eq_binaryTree_one :
    dyckPathClass.count 1 = binaryTreeClass.count 1 := by
  rw [dyckPath_count_one, binaryTree_count_one]

theorem dyckPath_count_eq_binaryTree_two :
    dyckPathClass.count 2 = binaryTreeClass.count 2 := by
  rw [dyckPath_count_two, binaryTree_count_two]

theorem dyckPath_count_eq_binaryTree_three :
    dyckPathClass.count 3 = binaryTreeClass.count 3 := by
  rw [dyckPath_count_three, binaryTree_count_three]

theorem dyckPath_count_eq_binaryTree_four :
    dyckPathClass.count 4 = binaryTreeClass.count 4 := by
  rw [dyckPath_count_four, binaryTree_count_four]

/--
The intended general counting theorem is
`∀ n, dyckPathClass.count n = binaryTreeClass.count n`.
This file proves the finite checks above without assuming the reflection
principle or a full first-return bijection.
-/
def dyckPath_count_eq_binaryTree_statement (n : ℕ) : Prop :=
  dyckPathClass.count n = binaryTreeClass.count n

/--
The intended closed form is
`∀ n, dyckPathClass.count n = Nat.centralBinom n / (n + 1)`.
The initial Catalan values `n = 0, 1, 2, 3, 4` are proved above.
-/
def dyckPath_count_eq_catalan_statement (n : ℕ) : Prop :=
  dyckPathClass.count n = Nat.centralBinom n / (n + 1)
