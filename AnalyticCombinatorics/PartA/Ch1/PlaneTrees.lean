/-
  Chapter I § I.3 — Plane trees.

  A plane tree is a rooted tree whose children are linearly ordered.  The
  symbolic specification is

      T = Z × SEQ(T),

  hence its ordinary generating function satisfies T(z) = z/(1 - T(z)), or
  equivalently T(z) = z + T(z)^2.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences

set_option linter.style.show false

open PowerSeries CombinatorialClass

/-- Plane, or ordered, rooted trees. -/
inductive PlaneTree where
  | node : List PlaneTree → PlaneTree
deriving Repr

namespace PlaneTree

mutual
  /-- Size of a plane tree: every node contributes one. -/
  def size : PlaneTree → ℕ
    | node children => 1 + childrenSize children

  /-- Total size of a list of subtrees. -/
  def childrenSize : List PlaneTree → ℕ
    | [] => 0
    | t :: ts => size t + childrenSize ts
end

@[simp] theorem size_node (children : List PlaneTree) :
    size (node children) = 1 + childrenSize children := rfl

@[simp] theorem childrenSize_nil : childrenSize [] = 0 := rfl

@[simp] theorem childrenSize_cons (t : PlaneTree) (ts : List PlaneTree) :
    childrenSize (t :: ts) = size t + childrenSize ts := rfl

/-- Every plane tree has positive size. -/
theorem size_pos (t : PlaneTree) : 1 ≤ size t := by
  cases t
  simp

/-- A child contributes at most the total size of the child list. -/
theorem child_size_le_childrenSize {children : List PlaneTree} {t : PlaneTree}
    (ht : t ∈ children) : size t ≤ childrenSize children := by
  induction children with
  | nil => simp at ht
  | cons a rest ih =>
      simp only [List.mem_cons] at ht
      simp only [childrenSize_cons]
      rcases ht with rfl | ht
      · omega
      · have hle := ih ht
        omega

/-- Since every tree has positive size, list length is bounded by total size. -/
theorem length_le_childrenSize (children : List PlaneTree) :
    children.length ≤ childrenSize children := by
  induction children with
  | nil => simp
  | cons a rest ih =>
      simp only [List.length_cons, childrenSize_cons]
      have hpos := size_pos a
      omega

theorem childrenSize_eq_foldr (children : List PlaneTree) :
    childrenSize children =
      children.foldr (fun b acc => size b + acc) 0 := by
  induction children with
  | nil => rfl
  | cons a rest ih =>
      simp only [childrenSize_cons, List.foldr_cons, ih]

/-- The ordered list of children of a plane tree. -/
def children : PlaneTree → List PlaneTree
  | node children => children

@[simp] theorem children_node (children : List PlaneTree) :
    (node children).children = children := rfl

@[simp] theorem node_children (t : PlaneTree) :
    node t.children = t := by
  cases t
  rfl

/-- Level sets of plane trees are finite. -/
theorem finite_size_eq (n : ℕ) : Set.Finite {t : PlaneTree | size t = n} := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          exact Set.finite_empty.subset fun t ht => by
            have hpos := size_pos t
            simp only [Set.mem_setOf_eq] at ht
            omega
      | succ n =>
          let S : Set PlaneTree := ⋃ k : Fin (n + 1), {t : PlaneTree | size t = k.val}
          have hSfin : S.Finite := by
            apply Set.finite_iUnion
            intro k
            exact ih k.val k.isLt
          have hmemS : ∀ children : List PlaneTree,
              childrenSize children = n → ∀ t ∈ children, t ∈ S := by
            intro children hchildren t ht
            simp only [S, Set.mem_iUnion, Set.mem_setOf_eq]
            have hle := child_size_le_childrenSize ht
            refine ⟨⟨size t, by omega⟩, rfl⟩
          haveI : Finite {t : PlaneTree // t ∈ S} := hSfin.to_subtype
          apply Set.Finite.subset
            ((List.finite_length_le {t : PlaneTree // t ∈ S} n).image
              (fun children => node (children.map Subtype.val)))
          intro t ht
          simp only [Set.mem_image, Set.mem_setOf_eq]
          cases t with
          | node children =>
              change 1 + childrenSize children = n + 1 at ht
              have hchildren : childrenSize children = n := by omega
              refine ⟨children.attachWith (· ∈ S) (hmemS children hchildren), ?_, ?_⟩
              · rw [List.length_attachWith]
                have hlen := length_le_childrenSize children
                omega
              · rw [List.attachWith_map_subtype_val]

end PlaneTree

/-- Plane trees as a combinatorial class, counted by nodes. -/
def planeTreeClass : CombinatorialClass where
  Obj := PlaneTree
  size := PlaneTree.size
  finite_level n := PlaneTree.finite_size_eq n

/-- There are no plane trees of size zero. -/
theorem planeTree_count_zero : planeTreeClass.count 0 = 0 := by
  simp only [CombinatorialClass.count]
  rw [Finset.card_eq_zero]
  exact Finset.eq_empty_of_forall_notMem fun t ht => by
    have hsz : PlaneTree.size t = 0 :=
      (CombinatorialClass.level_mem_iff (C := planeTreeClass) t).mp ht
    have hpos := PlaneTree.size_pos t
    omega

/-- A tree of size `n + 1` is a root followed by a sequence of subtrees of
total size `n`. -/
theorem planeTree_count_succ_seq (n : ℕ) :
    planeTreeClass.count (n + 1) =
      (seqClass planeTreeClass planeTree_count_zero).count n := by
  simp only [CombinatorialClass.count]
  let S := seqClass planeTreeClass planeTree_count_zero
  have hcard : (planeTreeClass.level (n + 1)).card = (S.level n).card := by
    apply Finset.card_bij'
        (fun t _ => PlaneTree.children t)
        (fun children _ => PlaneTree.node children)
    · intro t ht
      have hsz : PlaneTree.size t = n + 1 :=
        (CombinatorialClass.level_mem_iff (C := planeTreeClass) t).mp ht
      apply (CombinatorialClass.level_mem_iff (C := S) (PlaneTree.children t)).mpr
      cases t with
      | node children =>
          simp only [PlaneTree.children_node]
          change children.foldr (fun b acc => PlaneTree.size b + acc) 0 = n
          rw [← PlaneTree.childrenSize_eq_foldr]
          change 1 + PlaneTree.childrenSize children = n + 1 at hsz
          omega
    · intro children hchildren
      have hsz : children.foldr (fun b acc => PlaneTree.size b + acc) 0 = n :=
        (CombinatorialClass.level_mem_iff (C := S) children).mp hchildren
      apply (CombinatorialClass.level_mem_iff (C := planeTreeClass)
        (PlaneTree.node children)).mpr
      change 1 + PlaneTree.childrenSize children = n + 1
      rw [PlaneTree.childrenSize_eq_foldr]
      omega
    · intro t _
      simp
    · intro children _
      simp
  exact hcard

/-- The fundamental OGF equation from the symbolic specification
`T = Z × SEQ(T)`. -/
theorem planeTree_ogf_satisfies :
    planeTreeClass.ogf =
      PowerSeries.X * (seqClass planeTreeClass planeTree_count_zero).ogf := by
  ext n
  cases n with
  | zero =>
      rw [CombinatorialClass.coeff_ogf, planeTree_count_zero]
      simp
  | succ n =>
      rw [CombinatorialClass.coeff_ogf, planeTree_count_succ_seq n]
      simp only [PowerSeries.coeff_succ_X_mul, CombinatorialClass.coeff_ogf]

/-- Quadratic form of the plane-tree OGF: `T = X + T^2`. -/
theorem planeTree_ogf_quadratic :
    planeTreeClass.ogf = PowerSeries.X + planeTreeClass.ogf ^ 2 := by
  let S := (seqClass planeTreeClass planeTree_count_zero).ogf
  have hSeq := seqClass_ogf_recursion planeTreeClass planeTree_count_zero
  have hSeqS : S = 1 + planeTreeClass.ogf * S := by
    simpa [S] using hSeq
  have hT : planeTreeClass.ogf = PowerSeries.X * S := by
    simpa [S] using planeTree_ogf_satisfies
  calc
    planeTreeClass.ogf = PowerSeries.X * S := hT
    _ = PowerSeries.X * (1 + planeTreeClass.ogf * S) :=
        congrArg (fun u => PowerSeries.X * u) hSeqS
    _ = PowerSeries.X + planeTreeClass.ogf * (PowerSeries.X * S) := by ring
    _ = PowerSeries.X + planeTreeClass.ogf * planeTreeClass.ogf := by rw [← hT]
    _ = PowerSeries.X + planeTreeClass.ogf ^ 2 := by rw [pow_two]

/-- Catalan convolution for plane trees. -/
theorem planeTree_count_recursion (n : ℕ) :
    planeTreeClass.count (n + 2) =
      ∑ p ∈ Finset.antidiagonal (n + 2),
        planeTreeClass.count p.1 * planeTreeClass.count p.2 := by
  have h := congrArg (PowerSeries.coeff (n + 2)) planeTree_ogf_quadratic
  simpa [PowerSeries.coeff_X, CombinatorialClass.coeff_ogf, pow_two, coeff_mul] using h

/-- The same OGF equation over `ℤ[[z]]`, where subtraction is available:
`(1 - T)T = X`. -/
theorem planeTree_ogf_eq :
    (1 - ogfZ planeTreeClass) * ogfZ planeTreeClass = PowerSeries.X := by
  have hq : ogfZ planeTreeClass =
      PowerSeries.X + ogfZ planeTreeClass ^ 2 := by
    unfold ogfZ
    have := congrArg (PowerSeries.map (algebraMap ℕ ℤ)) planeTree_ogf_quadratic
    simpa using this
  have hsub : ogfZ planeTreeClass - ogfZ planeTreeClass ^ 2 = PowerSeries.X := by
    calc
      ogfZ planeTreeClass - ogfZ planeTreeClass ^ 2 =
          (PowerSeries.X + ogfZ planeTreeClass ^ 2) - ogfZ planeTreeClass ^ 2 :=
        congrArg (fun u => u - ogfZ planeTreeClass ^ 2) hq
      _ = PowerSeries.X := by ring
  calc
    (1 - ogfZ planeTreeClass) * ogfZ planeTreeClass =
        ogfZ planeTreeClass - ogfZ planeTreeClass ^ 2 := by ring
    _ = PowerSeries.X := hsub

/-! ## Initial Catalan values, shifted by one. -/

theorem planeTree_count_one : planeTreeClass.count 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 by rfl, planeTree_count_succ_seq]
  exact seqClass.count_zero planeTreeClass planeTree_count_zero

theorem planeTree_count_two : planeTreeClass.count 2 = 1 := by
  rw [show (2 : ℕ) = 0 + 2 by rfl, planeTree_count_recursion]
  norm_num [Finset.antidiagonal, planeTree_count_zero, planeTree_count_one]

theorem planeTree_count_three : planeTreeClass.count 3 = 2 := by
  rw [show (3 : ℕ) = 1 + 2 by rfl, planeTree_count_recursion]
  norm_num [Finset.antidiagonal, planeTree_count_zero, planeTree_count_one, planeTree_count_two]

theorem planeTree_count_four : planeTreeClass.count 4 = 5 := by
  rw [show (4 : ℕ) = 2 + 2 by rfl, planeTree_count_recursion]
  norm_num [Finset.antidiagonal, planeTree_count_zero, planeTree_count_one, planeTree_count_two,
    planeTree_count_three]

theorem planeTree_count_five : planeTreeClass.count 5 = 14 := by
  rw [show (5 : ℕ) = 3 + 2 by rfl, planeTree_count_recursion]
  norm_num [Finset.antidiagonal, planeTree_count_zero, planeTree_count_one, planeTree_count_two,
    planeTree_count_three, planeTree_count_four]
