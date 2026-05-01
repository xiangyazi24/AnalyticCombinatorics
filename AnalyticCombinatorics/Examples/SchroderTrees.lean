import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass

open CombinatorialClass

/-- Raw plane tree syntax used for Schröder trees.

The actual Schröder class filters this syntax by `WellFormed`, requiring every
internal node to have at least two children. -/
inductive SchroderTree : Type
  | leaf : SchroderTree
  | node : List SchroderTree → SchroderTree

namespace SchroderTree

/-- Predicate selecting Schröder trees: every internal node has at least two children. -/
def WellFormed : SchroderTree → Prop
  | leaf => True
  | node children => 2 ≤ children.length ∧ ∀ child ∈ children, WellFormed child

/-- Size = number of leaves minus one. -/
def size : SchroderTree → ℕ
  | leaf => 0
  | node children => children.length - 1 + (children.map size).sum

private lemma size_leaf_eq : SchroderTree.leaf.size = 0 := by
  simp [size]

private lemma size_node_eq (children : List SchroderTree) :
    (SchroderTree.node children).size =
      children.length - 1 + (children.map size).sum := by
  simp [size]

private lemma size_le_sum_of_mem {t : SchroderTree} :
    ∀ {children : List SchroderTree}, t ∈ children → t.size ≤ (children.map size).sum
  | [], ht => by simp at ht
  | u :: us, ht => by
      simp only [List.mem_cons, List.map_cons, List.sum_cons] at *
      rcases ht with rfl | ht
      · omega
      · have hle := size_le_sum_of_mem (t := t) ht
        omega

private def leafObj : {t : SchroderTree // WellFormed t} :=
  ⟨SchroderTree.leaf, by simp [WellFormed]⟩

private def nodeObj (xs : List {t : SchroderTree // WellFormed t}) (h : 2 ≤ xs.length) :
    {t : SchroderTree // WellFormed t} :=
  ⟨SchroderTree.node (xs.map Subtype.val), by
    simp only [WellFormed, List.length_map, h, true_and]
    intro child hchild
    rcases List.mem_map.mp hchild with ⟨x, hx, rfl⟩
    exact x.property⟩

private lemma val_nodeObj (xs : List {t : SchroderTree // WellFormed t}) (h : 2 ≤ xs.length) :
    (nodeObj xs h).val = SchroderTree.node (xs.map Subtype.val) := rfl

/-- The combinatorial class of Schröder trees, indexed by leaves minus one.

The uncolored class has the little Schröder numbers as coefficients.  The large
Schröder sequence is obtained below by doubling the positive coefficients. -/
noncomputable def asClass : CombinatorialClass where
  Obj := {t : SchroderTree // WellFormed t}
  size := fun t => t.val.size
  finite_level n := by
    induction n using Nat.strong_induction_on
    rename_i m ih
    let S : Set {t : SchroderTree // WellFormed t} :=
      ⋃ k : Fin m, {t : {t : SchroderTree // WellFormed t} | t.val.size = k.val}
    have hSfin : S.Finite := Set.finite_iUnion (fun k => ih k.val k.isLt)
    haveI : Finite {t : {t : SchroderTree // WellFormed t} // t ∈ S} := hSfin.to_subtype
    apply Set.Finite.subset
      ((Set.finite_singleton leafObj).union
        ((List.finite_length_le {t : {t : SchroderTree // WellFormed t} // t ∈ S} (m + 1)).image
          (fun xs =>
            let children : List {t : SchroderTree // WellFormed t} := xs.map Subtype.val
            if h : 2 ≤ children.length then nodeObj children h else leafObj)))
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    cases hval : t.val with
    | leaf =>
        simp only [Set.mem_union, Set.mem_singleton_iff]
        left
        exact Subtype.ext hval
    | node children =>
        have hwell : WellFormed (SchroderTree.node children) := by
          simpa [hval] using t.property
        have hwell' : 2 ≤ children.length ∧ ∀ child ∈ children, WellFormed child := by
          simpa [WellFormed] using hwell
        have hchildren : 2 ≤ children.length := hwell'.1
        have hchild_wf : ∀ child ∈ children, WellFormed child := hwell'.2
        have hlen_le : children.length ≤ m + 1 := by
          simp only [hval, size_node_eq] at ht
          omega
        let childrenWF : List {t : SchroderTree // WellFormed t} :=
          children.attachWith WellFormed hchild_wf
        have hmemS : ∀ child ∈ childrenWF, child ∈ S := by
          intro child hchild
          simp only [S, Set.mem_iUnion, Set.mem_setOf_eq]
          have hchild_raw : child.val ∈ children := by
            exact (List.mem_attachWith hchild_wf child).mp hchild
          have hle_sum := size_le_sum_of_mem (t := child.val) hchild_raw
          simp only [hval, size_node_eq] at ht
          have hlt : child.val.size < m := by omega
          exact ⟨⟨child.val.size, hlt⟩, rfl⟩
        let boundedChildren : List {t : {t : SchroderTree // WellFormed t} // t ∈ S} :=
          childrenWF.attachWith (· ∈ S) hmemS
        simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
        right
        refine ⟨boundedChildren, ?_, ?_⟩
        · rw [List.length_attachWith, List.length_attachWith]
          exact hlen_le
        · have hlen_bounded : 2 ≤ (boundedChildren.map Subtype.val).length := by
            simp [boundedChildren, childrenWF, hchildren]
          simp only [hlen_bounded, ↓reduceDIte]
          apply Subtype.ext
          rw [val_nodeObj]
          change SchroderTree.node ((boundedChildren.map Subtype.val).map Subtype.val) = t.val
          rw [hval]
          congr
          change (boundedChildren.map Subtype.val).map Subtype.val = children
          rw [List.attachWith_map_subtype_val hmemS]
          exact List.attachWith_map_subtype_val hchild_wf

/-- The number of uncolored Schröder trees of size `n`. -/
noncomputable def count (n : ℕ) : ℕ := asClass.count n

private lemma mem_level_iff (m : ℕ) (t : asClass.Obj) :
    t ∈ asClass.level m ↔ asClass.size t = m := by
  change t ∈ (asClass.finite_level m).toFinset ↔ asClass.size t = m
  exact (asClass.finite_level m).mem_toFinset.trans (by simp)

lemma count_zero : asClass.count 0 = 1 := by
  simp only [CombinatorialClass.count]
  rw [Finset.card_eq_one]
  refine ⟨leafObj, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact (mem_level_iff 0 leafObj).mpr (by simp [leafObj, asClass, size])
  · intro t ht
    have hsz : asClass.size t = 0 := (mem_level_iff 0 t).mp ht
    cases hval : t.val with
    | leaf => exact Subtype.ext hval
    | node children =>
        have hwell : WellFormed (SchroderTree.node children) := by
          simpa [hval] using t.property
        have hwell' : 2 ≤ children.length ∧ ∀ child ∈ children, WellFormed child := by
          simpa [WellFormed] using hwell
        change t.val.size = 0 at hsz
        rw [hval, size_node_eq] at hsz
        omega

/-- Prefix table for the large Schröder numbers, with
`a₀ = 1` and `aₙ₊₁ = aₙ + ∑_{i+j=n} aᵢ aⱼ`. -/
def largeSchroderNumbers : ℕ → List ℕ
  | 0 => [1]
  | n + 1 =>
      let xs := largeSchroderNumbers n
      let next := xs.getD n 0 +
        ∑ p ∈ Finset.antidiagonal n, xs.getD p.1 0 * xs.getD p.2 0
      xs ++ [next]

/-- The large Schröder number `aₙ`. -/
def largeSchroderNumber (n : ℕ) : ℕ :=
  (largeSchroderNumbers n).getD n 0

example : largeSchroderNumber 0 = 1 := by decide
example : largeSchroderNumber 1 = 2 := by decide
example : largeSchroderNumber 2 = 6 := by decide
example : largeSchroderNumber 3 = 22 := by decide
example : largeSchroderNumber 4 = 90 := by decide
example : largeSchroderNumber 5 = 394 := by decide
example : largeSchroderNumber 6 = 1806 := by decide
example : largeSchroderNumber 7 = 8558 := by decide
example : largeSchroderNumber 8 = 41586 := by decide
example : largeSchroderNumber 9 = 206098 := by decide
example : largeSchroderNumber 10 = 1037718 := by decide

example (n : ℕ) :
    SchroderTree.asClass.ogf.coeff n = SchroderTree.asClass.count n := by
  rw [coeff_ogf]

end SchroderTree
