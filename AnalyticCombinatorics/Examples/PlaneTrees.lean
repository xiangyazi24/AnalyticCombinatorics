import AnalyticCombinatorics.Examples.BinaryTrees

open CombinatorialClass

/-- Plane tree: a rooted tree with an ordered sequence of children at each node.
    Equivalent to a list of subtrees. -/
inductive PlaneTree : Type
  | mk : List PlaneTree → PlaneTree
  deriving Inhabited

namespace PlaneTree

/-- Number of nodes in a plane tree. -/
def numNodes : PlaneTree → ℕ
  | mk children => 1 + (children.map numNodes).sum

lemma numNodes_pos (t : PlaneTree) : 0 < t.numNodes := by
  cases t
  simp [numNodes]

mutual
  /-- Encode the children of the plane root as a binary tree. -/
  def toBin : PlaneTree → BinTree
    | mk children => childrenToBin children

  /-- Left-child/right-sibling encoding of an ordered forest. -/
  def childrenToBin : List PlaneTree → BinTree
    | [] => BinTree.leaf
    | child :: siblings => BinTree.node (toBin child) (childrenToBin siblings)
end

/-- Decode a binary tree as an ordered forest. -/
def childrenFromBin : BinTree → List PlaneTree
  | BinTree.leaf => []
  | BinTree.node l r => PlaneTree.mk (childrenFromBin l) :: childrenFromBin r

/-- Decode a binary tree as a plane tree whose root owns the decoded forest. -/
def fromBin (b : BinTree) : PlaneTree :=
  PlaneTree.mk (childrenFromBin b)

theorem childrenToBin_childrenFromBin (b : BinTree) :
    childrenToBin (childrenFromBin b) = b := by
  induction b with
  | leaf =>
    simp [childrenFromBin, childrenToBin]
  | node l r ihl ihr =>
    simp [childrenFromBin, childrenToBin, toBin, ihl, ihr]

theorem toBin_fromBin (b : BinTree) : toBin (fromBin b) = b := by
  simp [fromBin, toBin, childrenToBin_childrenFromBin]

theorem fromBin_toBin (t : PlaneTree) : fromBin (toBin t) = t :=
  PlaneTree.rec
    (motive_1 := fun t => fromBin (toBin t) = t)
    (motive_2 := fun children => childrenFromBin (childrenToBin children) = children)
    (mk := by
      intro children ih
      simp [fromBin, toBin, ih])
    (nil := by
      simp [childrenToBin, childrenFromBin])
    (cons := by
      intro child siblings ihChild ihSiblings
      change fromBin (toBin child) ::
          childrenFromBin (childrenToBin siblings) = child :: siblings
      rw [ihChild, ihSiblings])
    t

theorem childrenFromBin_childrenToBin (children : List PlaneTree) :
    childrenFromBin (childrenToBin children) = children :=
  PlaneTree.rec_1
    (motive_1 := fun t => fromBin (toBin t) = t)
    (motive_2 := fun children => childrenFromBin (childrenToBin children) = children)
    (mk := by
      intro children ih
      simp [fromBin, toBin, ih])
    (nil := by
      simp [childrenToBin, childrenFromBin])
    (cons := by
      intro child siblings ihChild ihSiblings
      change fromBin (toBin child) ::
          childrenFromBin (childrenToBin siblings) = child :: siblings
      rw [ihChild, ihSiblings])
    children

theorem childrenFromBin_numNodes_sum (b : BinTree) :
    ((childrenFromBin b).map numNodes).sum = b.size := by
  induction b with
  | leaf =>
    simp [childrenFromBin, BinTree.size]
  | node l r ihl ihr =>
    simp [childrenFromBin, numNodes, ihl, ihr, BinTree.size]

theorem fromBin_numNodes_sub_one (b : BinTree) :
    (fromBin b).numNodes - 1 = b.size := by
  simp [fromBin, numNodes, childrenFromBin_numNodes_sum]

theorem toBin_size (t : PlaneTree) : (toBin t).size = t.numNodes - 1 := by
  have h := fromBin_numNodes_sub_one (toBin t)
  rw [fromBin_toBin] at h
  exact h.symm

end PlaneTree

/-- The combinatorial class of plane trees with n+1 nodes (size = n means n+1 actual nodes,
    indexed so that the one-node plane tree has size 0). -/
noncomputable def planeTreeClass : CombinatorialClass where
  Obj := PlaneTree
  size t := t.numNodes - 1
  finite_level n := by
    apply Set.Finite.subset ((BinTree.asClass.finite_level n).image PlaneTree.fromBin)
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    simp only [Set.mem_image]
    refine ⟨PlaneTree.toBin t, ?_, ?_⟩
    · change BinTree.size (PlaneTree.toBin t) = n
      rw [PlaneTree.toBin_size, ht]
    · exact PlaneTree.fromBin_toBin t

/-- Plane trees and binary trees are equinumerous by the standard
    left-child/right-sibling (rotation) correspondence. -/
theorem planeTreeClass_count_eq_binTree_count (n : ℕ) :
    planeTreeClass.count n = BinTree.asClass.count n := by
  simp only [CombinatorialClass.count]
  let fwd : (t : PlaneTree) → t ∈ planeTreeClass.level n → BinTree :=
    fun t _ => PlaneTree.toBin t
  have hcard : (planeTreeClass.level n).card = (BinTree.asClass.level n).card := by
    apply Finset.card_bij fwd
    · intro t ht
      apply (CombinatorialClass.level_mem_iff (C := BinTree.asClass) (PlaneTree.toBin t)).mpr
      have hsize := (CombinatorialClass.level_mem_iff (C := planeTreeClass) t).mp ht
      change t.numNodes - 1 = n at hsize
      change BinTree.size (PlaneTree.toBin t) = n
      rw [PlaneTree.toBin_size, hsize]
    · intro t₁ _ t₂ _ heq
      change PlaneTree.toBin t₁ = PlaneTree.toBin t₂ at heq
      calc
        t₁ = PlaneTree.fromBin (PlaneTree.toBin t₁) := (PlaneTree.fromBin_toBin t₁).symm
        _ = PlaneTree.fromBin (PlaneTree.toBin t₂) := by rw [heq]
        _ = t₂ := PlaneTree.fromBin_toBin t₂
    · intro b hb
      refine ⟨PlaneTree.fromBin b, ?_, ?_⟩
      · apply (CombinatorialClass.level_mem_iff (C := planeTreeClass) (PlaneTree.fromBin b)).mpr
        have hbsize := (CombinatorialClass.level_mem_iff (C := BinTree.asClass) b).mp hb
        change (PlaneTree.fromBin b).numNodes - 1 = n
        have h : BinTree.size (PlaneTree.toBin (PlaneTree.fromBin b)) = n := by
          rw [PlaneTree.toBin_fromBin]
          exact hbsize
        rw [PlaneTree.toBin_size] at h
        exact h
      · exact PlaneTree.toBin_fromBin b
  exact hcard

/-- Count of plane trees with `n + 1` nodes: the n-th Catalan number. -/
theorem planeTreeClass_count (n : ℕ) :
    planeTreeClass.count n = _root_.catalan n := by
  rw [planeTreeClass_count_eq_binTree_count]
  change BinTree.catalan n = _root_.catalan n
  exact BinTree.catalan_eq_nat_catalan n

example : planeTreeClass.count 0 = 1 := by rw [planeTreeClass_count, catalan_zero]
example : planeTreeClass.count 1 = 1 := by rw [planeTreeClass_count, catalan_one]
example : planeTreeClass.count 2 = 2 := by rw [planeTreeClass_count, catalan_two]
example : planeTreeClass.count 3 = 5 := by rw [planeTreeClass_count, catalan_three]
example : planeTreeClass.count 4 = 14 := by
  rw [planeTreeClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : planeTreeClass.count 5 = 42 := by
  rw [planeTreeClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : planeTreeClass.count 6 = 132 := by
  rw [planeTreeClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : planeTreeClass.count 7 = 429 := by
  rw [planeTreeClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : planeTreeClass.count 8 = 1430 := by
  rw [planeTreeClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : planeTreeClass.count 9 = 4862 := by
  rw [planeTreeClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : planeTreeClass.count 10 = 16796 := by
  rw [planeTreeClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : planeTreeClass.count 11 = 58786 := by
  rw [planeTreeClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : planeTreeClass.count 12 = 208012 := by
  rw [planeTreeClass_count]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

section
set_option linter.style.nativeDecide false

example : planeTreeClass.count 13 = 742900 := by
  rw [planeTreeClass_count]
  native_decide
example : planeTreeClass.count 14 = 2674440 := by
  rw [planeTreeClass_count]
  native_decide
example : planeTreeClass.count 15 = 9694845 := by
  rw [planeTreeClass_count]
  native_decide
example : planeTreeClass.count 16 = 35357670 := by
  rw [planeTreeClass_count]
  native_decide
example : planeTreeClass.count 17 = 129644790 := by
  rw [planeTreeClass_count]
  native_decide
example : planeTreeClass.count 18 = 477638700 := by
  rw [planeTreeClass_count]
  native_decide
example : planeTreeClass.count 19 = 1767263190 := by
  rw [planeTreeClass_count]
  native_decide
example : planeTreeClass.count 20 = 6564120420 := by
  rw [planeTreeClass_count]
  native_decide
example : planeTreeClass.count 21 = 24466267020 := by
  rw [planeTreeClass_count]
  native_decide

end

example (n : ℕ) :
    PowerSeries.coeff n planeTreeClass.ogf = _root_.catalan n := by
  rw [coeff_ogf]
  exact planeTreeClass_count n

example (n : ℕ) :
    planeTreeClass.egf.coeff n = (_root_.catalan n : ℚ) / n.factorial := by
  rw [CombinatorialClass.coeff_egf, planeTreeClass_count]
