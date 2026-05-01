/-
  Analytic Combinatorics — Examples
  Binary Trees and Catalan Numbers

  A binary tree is either a leaf (size 0) or an internal node with two subtrees.
  The counting sequence satisfies C(z) = 1 + z · C(z)², giving
    Cₙ = 1/(n+1) · C(2n, n)  (the Catalan numbers)
  and the dominant singularity at z = 1/4 yields
    Cₙ ~ 4ⁿ / (n^{3/2} · √π)  as n → ∞.

  Reference: Flajolet & Sedgewick, Example I.5 and VII.2.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Tactic.LinearCombination
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import AnalyticCombinatorics.PartA.Ch3.Parameters

set_option linter.style.show false
set_option linter.style.nativeDecide false

open PowerSeries CombinatorialClass

/-- Binary trees: leaf or node with two subtrees. -/
inductive BinTree : Type
  | leaf : BinTree
  | node : BinTree → BinTree → BinTree

namespace BinTree

/-- Size of a binary tree = number of internal nodes. -/
def size : BinTree → ℕ
  | leaf       => 0
  | node l r   => 1 + size l + size r

private lemma size_leaf_eq : BinTree.leaf.size = 0 := rfl
private lemma size_node_eq (l r : BinTree) : (BinTree.node l r).size = 1 + l.size + r.size := rfl

/-- The combinatorial class of binary trees. -/
def asClass : CombinatorialClass where
  Obj   := BinTree
  size  := BinTree.size
  finite_level n := by
    induction n using Nat.strong_induction_on
    rename_i m ih
    cases m with
    | zero =>
      -- Only leaf has size 0
      apply Set.Finite.subset (Set.finite_singleton BinTree.leaf)
      intro t ht
      simp only [Set.mem_setOf_eq] at ht
      simp only [Set.mem_singleton_iff]
      cases t with
      | leaf => rfl
      | node l r =>
        simp only [size_node_eq] at ht
        omega
    | succ m =>
      -- t = node l r with l.size + r.size = m
      apply Set.Finite.subset
        (Set.finite_iUnion (fun k : Fin (m + 1) =>
          ((ih k.val k.isLt).prod
            (ih (m - k.val) (Nat.lt_succ_of_le (Nat.sub_le m k.val)))).image
          (fun p => BinTree.node p.1 p.2)))
      intro t ht
      simp only [Set.mem_setOf_eq] at ht
      cases t with
      | leaf =>
        simp only [size_leaf_eq] at ht
        omega
      | node l r =>
        simp only [size_node_eq] at ht
        have hr : BinTree.size r = m - BinTree.size l := by omega
        simp only [Set.mem_iUnion, Set.mem_image, Set.mem_prod, Set.mem_setOf_eq]
        exact ⟨⟨l.size, by omega⟩, (l, r), ⟨rfl, hr⟩, rfl⟩

/-- The Catalan number Cₙ counts binary trees with n internal nodes. -/
noncomputable def catalan (n : ℕ) : ℕ := asClass.count n

private lemma mem_level_iff'' (m : ℕ) (t : BinTree) :
    t ∈ asClass.level m ↔ asClass.size t = m := by
  change t ∈ (asClass.finite_level m).toFinset ↔ asClass.size t = m
  exact (asClass.finite_level m).mem_toFinset.trans (by simp)

/-- Only `leaf` has size 0. -/
lemma count_zero : asClass.count 0 = 1 := by
  simp only [count]
  rw [Finset.card_eq_one]
  refine ⟨BinTree.leaf, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact (mem_level_iff'' 0 BinTree.leaf).mpr rfl
  · intro t ht
    have hsz : t.size = 0 := (mem_level_iff'' 0 t).mp ht
    cases t with
    | leaf => rfl
    | node l r => simp only [BinTree.size_node_eq] at hsz; omega

/-- Recursion on counts: a tree of size n+1 = node l r decomposes uniquely as (l, r)
    with l.size + r.size = n. -/
lemma count_succ (n : ℕ) :
    asClass.count (n + 1) =
      ∑ p ∈ Finset.antidiagonal n, asClass.count p.1 * asClass.count p.2 := by
  let rhsFs : Finset (Σ _ : ℕ × ℕ, BinTree × BinTree) :=
    (Finset.antidiagonal n).sigma (fun p => asClass.level p.1 ×ˢ asClass.level p.2)
  let fwd : (y : Σ _ : ℕ × ℕ, BinTree × BinTree) → y ∈ rhsFs → BinTree :=
    fun y _ => BinTree.node y.2.1 y.2.2
  have extract : ∀ y : Σ _ : ℕ × ℕ, BinTree × BinTree, y ∈ rhsFs →
      y.1 ∈ Finset.antidiagonal n ∧
      y.2.1 ∈ asClass.level y.1.1 ∧
      y.2.2 ∈ asClass.level y.1.2 := by
    intro y hy
    refine ⟨(Finset.mem_sigma.mp hy).1,
            (Finset.mem_product.mp (Finset.mem_sigma.mp hy).2).1,
            (Finset.mem_product.mp (Finset.mem_sigma.mp hy).2).2⟩
  have hcard : rhsFs.card = (asClass.level (n + 1)).card := by
    apply Finset.card_bij fwd
    · -- maps to asClass.level (n+1)
      intro y hy
      obtain ⟨h1, h2, h3⟩ := extract y hy
      have hkm : y.1.1 + y.1.2 = n := Finset.mem_antidiagonal.mp h1
      have hl : y.2.1.size = y.1.1 := (mem_level_iff'' _ _).mp h2
      have hr : y.2.2.size = y.1.2 := (mem_level_iff'' _ _).mp h3
      apply (mem_level_iff'' (n + 1) (BinTree.node y.2.1 y.2.2)).mpr
      change 1 + y.2.1.size + y.2.2.size = n + 1
      omega
    · -- injective
      intro y1 hy1 y2 hy2 heq
      obtain ⟨h11, h12, h13⟩ := extract y1 hy1
      obtain ⟨h21, h22, h23⟩ := extract y2 hy2
      have hl1 : y1.2.1.size = y1.1.1 := (mem_level_iff'' _ _).mp h12
      have hl2 : y2.2.1.size = y2.1.1 := (mem_level_iff'' _ _).mp h22
      have hr1 : y1.2.2.size = y1.1.2 := (mem_level_iff'' _ _).mp h13
      have hr2 : y2.2.2.size = y2.1.2 := (mem_level_iff'' _ _).mp h23
      change BinTree.node y1.2.1 y1.2.2 = BinTree.node y2.2.1 y2.2.2 at heq
      have hl : y1.2.1 = y2.2.1 := (BinTree.node.injEq _ _ _ _).mp heq |>.1
      have hr : y1.2.2 = y2.2.2 := (BinTree.node.injEq _ _ _ _).mp heq |>.2
      have hk : y1.1.1 = y2.1.1 := by rw [← hl1, hl, hl2]
      have hm : y1.1.2 = y2.1.2 := by rw [← hr1, hr, hr2]
      obtain ⟨⟨k1, m1⟩, l1, r1⟩ := y1
      obtain ⟨⟨k2, m2⟩, l2, r2⟩ := y2
      simp_all
    · -- surjective
      intro t ht
      have hsz : t.size = n + 1 := (mem_level_iff'' _ _).mp ht
      cases t with
      | leaf =>
        exfalso
        simp only [BinTree.size] at hsz
        omega
      | node l r =>
        simp only [BinTree.size_node_eq] at hsz
        refine ⟨⟨(l.size, r.size), (l, r)⟩, ?_, rfl⟩
        apply Finset.mem_sigma.mpr
        refine ⟨?_, ?_⟩
        · apply Finset.mem_antidiagonal.mpr
          show l.size + r.size = n
          omega
        · apply Finset.mem_product.mpr
          exact ⟨(mem_level_iff'' _ _).mpr rfl, (mem_level_iff'' _ _).mpr rfl⟩
  rw [show asClass.count (n + 1) = (asClass.level (n + 1)).card from rfl, ← hcard,
      Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro p _
  exact Finset.card_product _ _

/-- The OGF C(z) satisfies the quadratic equation C = 1 + z·C². -/
theorem ogf_functional_equation :
    asClass.ogf = 1 + PowerSeries.X * asClass.ogf ^ 2 := by
  ext n
  rw [map_add, coeff_one, coeff_ogf]
  rcases n with _ | m
  · -- n = 0
    rw [count_zero]
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
        PowerSeries.constantCoeff_X, zero_mul, add_zero]
    rfl
  · -- n = m + 1
    rw [PowerSeries.coeff_succ_X_mul, sq, coeff_mul, count_succ m]
    simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
    apply Finset.sum_congr rfl
    intro p _
    rw [coeff_ogf, coeff_ogf]

/-- The number of binary trees with n internal nodes equals the n-th Catalan number
    (Mathlib's `_root_.catalan`). Hence by `Nat.succ_mul_catalan_eq_centralBinom`,
    (n+1) · catalan n = C(2n, n), the standard closed form. -/
theorem catalan_eq_nat_catalan : ∀ n : ℕ, BinTree.catalan n = _root_.catalan n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · show asClass.count 0 = _root_.catalan 0
      rw [count_zero, _root_.catalan_zero]
    · show asClass.count (m + 1) = _root_.catalan (m + 1)
      rw [count_succ m, _root_.catalan_succ']
      apply Finset.sum_congr rfl
      intro p hp
      have hp_sum : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
      have hp1 : p.1 < m + 1 := by omega
      have hp2 : p.2 < m + 1 := by omega
      change asClass.count p.1 * asClass.count p.2 = _root_.catalan p.1 * _root_.catalan p.2
      rw [show asClass.count p.1 = BinTree.catalan p.1 from rfl,
          show asClass.count p.2 = BinTree.catalan p.2 from rfl,
          ih p.1 hp1, ih p.2 hp2]

/-- (n + 1) · (number of binary trees of size n) = C(2n, n).
    Closed-form Catalan identity, derived via `Nat.succ_mul_catalan_eq_centralBinom`. -/
theorem succ_mul_catalan_eq_centralBinom (n : ℕ) :
    (n + 1) * BinTree.catalan n = n.centralBinom := by
  rw [catalan_eq_nat_catalan, _root_.succ_mul_catalan_eq_centralBinom]

/-- The number of binary trees of size n equals C(2n, n) / (n + 1).
    Standard closed form for Catalan numbers, lifted from `_root_.catalan_eq_centralBinom_div`. -/
theorem catalan_eq_centralBinom_div (n : ℕ) :
    BinTree.catalan n = n.centralBinom / (n + 1) := by
  rw [catalan_eq_nat_catalan, _root_.catalan_eq_centralBinom_div]

example (n : ℕ) :
    PowerSeries.coeff n (BinTree.asClass.ogf) = _root_.catalan n := by
  rw [coeff_ogf]
  exact BinTree.catalan_eq_nat_catalan n

/-! Sanity checks on initial values:
    C₀=1, C₁=1, C₂=2, C₃=5, C₄=14, C₅=42, C₆=132, C₇=429, C₈=1430. -/

example : BinTree.catalan 0 = 1 := by rw [catalan_eq_nat_catalan, catalan_zero]
example : BinTree.catalan 1 = 1 := by rw [catalan_eq_nat_catalan, catalan_one]
example : BinTree.catalan 2 = 2 := by rw [catalan_eq_nat_catalan, catalan_two]
example : BinTree.catalan 3 = 5 := by rw [catalan_eq_nat_catalan, catalan_three]
example : BinTree.catalan 4 = 14 := by
  rw [catalan_eq_nat_catalan]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : BinTree.catalan 5 = 42 := by
  rw [catalan_eq_nat_catalan]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : BinTree.catalan 6 = 132 := by
  rw [catalan_eq_nat_catalan]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : BinTree.catalan 7 = 429 := by
  rw [catalan_eq_nat_catalan]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
example : BinTree.catalan 8 = 1430 := by
  rw [catalan_eq_nat_catalan]
  norm_num [_root_.catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

/-- The dominant root of the Catalan generating function quadratic
    1 + z·C² - C = 0 satisfies C(0) = 1. -/
example : asClass.ogf.coeff 0 = 1 := by
  rw [coeff_ogf]
  show asClass.count 0 = 1
  exact count_zero

/-- Lift the functional equation to ℤ[[z]] via ogfZ. -/
theorem ogfZ_functional_equation :
    ogfZ asClass = 1 + PowerSeries.X * (ogfZ asClass) ^ 2 := by
  unfold ogfZ
  have := congrArg (PowerSeries.map (algebraMap ℕ ℤ)) ogf_functional_equation
  simpa [PowerSeries.map_X] using this

/-- Quadratic form: X · C² - C + 1 = 0 in ℤ[[z]]. -/
theorem ogfZ_quadratic :
    PowerSeries.X * (ogfZ asClass) ^ 2 - ogfZ asClass + 1 = 0 := by
  have h := ogfZ_functional_equation
  linear_combination -h

end BinTree

example : BinTree.asClass.egf.coeff 0 = 1 := by
  rw [CombinatorialClass.coeff_egf]
  rw [show (BinTree.asClass.count 0 : ℕ) = 1 from BinTree.count_zero]
  simp

example : BinTree.asClass.egf.coeff 2 = (2 : ℚ) / 2 := by
  rw [CombinatorialClass.coeff_egf]
  rw [show (BinTree.asClass.count 2 : ℕ) = BinTree.catalan 2 from rfl]
  rw [show BinTree.catalan 2 = 2 from by
        rw [BinTree.catalan_eq_nat_catalan, _root_.catalan_two]]
  simp [Nat.factorial]

/-- Rational EGF coefficient: [zⁿ] BinTree.asClass.egf = catalan n / n!. -/
example (n : ℕ) :
    BinTree.asClass.egf.coeff n = (_root_.catalan n : ℚ) / n.factorial := by
  rw [CombinatorialClass.coeff_egf]
  show (BinTree.asClass.count n : ℚ) / n.factorial = (_root_.catalan n : ℚ) / n.factorial
  rw [show BinTree.asClass.count n = _root_.catalan n from
        BinTree.catalan_eq_nat_catalan n]

/-- The cartesian product of two BinTree classes counts pairs of binary trees;
    the count is a Catalan convolution: ∑ p ∈ antidiag n, catalan p.1 · catalan p.2. -/
theorem BinTree_asClass_cartProd_count (n : ℕ) :
    (BinTree.asClass.cartProd BinTree.asClass).count n =
      ∑ p ∈ Finset.antidiagonal n, _root_.catalan p.1 * _root_.catalan p.2 := by
  rw [CombinatorialClass.cartProd_count]
  apply Finset.sum_congr rfl
  intro p _
  rw [show BinTree.asClass.count p.1 = _root_.catalan p.1 from
        BinTree.catalan_eq_nat_catalan p.1]
  rw [show BinTree.asClass.count p.2 = _root_.catalan p.2 from
        BinTree.catalan_eq_nat_catalan p.2]

/-- The Catalan convolution for two binary-tree classes gives the next Catalan number. -/
theorem BinTree_asClass_cartProd_count_eq_catalan_succ (n : ℕ) :
    (BinTree.asClass.cartProd BinTree.asClass).count n = _root_.catalan (n + 1) := by
  rw [BinTree_asClass_cartProd_count, _root_.catalan_succ']

example : (BinTree.asClass.cartProd BinTree.asClass).count 0 = 1 := by
  rw [BinTree_asClass_cartProd_count]
  native_decide

example : (BinTree.asClass.cartProd BinTree.asClass).count 2 = 5 := by
  rw [BinTree_asClass_cartProd_count]
  native_decide

example : (BinTree.asClass.cartProd BinTree.asClass).count 0 = 1 := by
  rw [BinTree_asClass_cartProd_count_eq_catalan_succ]
  native_decide

example : (BinTree.asClass.cartProd BinTree.asClass).count 1 = 2 := by
  rw [BinTree_asClass_cartProd_count_eq_catalan_succ]
  native_decide

example : (BinTree.asClass.cartProd BinTree.asClass).count 2 = 5 := by
  rw [BinTree_asClass_cartProd_count_eq_catalan_succ]
  native_decide

example : (BinTree.asClass.cartProd BinTree.asClass).count 3 = 14 := by
  rw [BinTree_asClass_cartProd_count_eq_catalan_succ]
  native_decide

/-- The OGF of `BinTree × BinTree` is the square of `BinTree.asClass.ogf`. -/
example : (BinTree.asClass.cartProd BinTree.asClass).ogf = BinTree.asClass.ogf ^ 2 := by
  rw [CombinatorialClass.cartProd_ogf, sq]

namespace BinTree

/-- Number of leaves of a binary tree. -/
def numLeaves : BinTree → ℕ
  | leaf => 1
  | node l r => l.numLeaves + r.numLeaves

/-- `numLeaves t = size t + 1` for any binary tree. -/
theorem numLeaves_eq_size_add_one (t : BinTree) :
    t.numLeaves = t.size + 1 := by
  induction t with
  | leaf => rfl
  | node l r ih_l ih_r =>
      simp [numLeaves, size, ih_l, ih_r]
      omega

/-- As a Parameter on asClass: numLeaves a = a.size + 1. -/
def numLeavesParam : Parameter asClass := numLeaves

/-- jointCount of (size, leaves) is just count when k = n+1. -/
example (n : ℕ) :
    asClass.jointCount numLeavesParam n (n + 1) = asClass.count n := by
  unfold CombinatorialClass.jointCount CombinatorialClass.count
  rw [Finset.filter_eq_self.mpr]
  intro a ha
  have hsize : BinTree.size a = n := by
    exact (CombinatorialClass.level_mem_iff (C := asClass) a).mp ha
  change numLeaves a = n + 1
  rw [numLeaves_eq_size_add_one a]
  rw [hsize]

end BinTree

example : ((BinTree.asClass.cartProd BinTree.asClass).cartProd BinTree.asClass).count 0 = 1 := by
  rw [CombinatorialClass.cartProd_count]
  simp [BinTree_asClass_cartProd_count_eq_catalan_succ, BinTree.count_zero]

example : ((BinTree.asClass.cartProd BinTree.asClass).cartProd BinTree.asClass).count 1 = 3 := by
  rw [CombinatorialClass.cartProd_count]
  have h1 : BinTree.asClass.count 1 = 1 := by
    rw [show BinTree.asClass.count 1 = BinTree.catalan 1 from rfl,
        BinTree.catalan_eq_nat_catalan, _root_.catalan_one]
  norm_num [Finset.antidiagonal, BinTree_asClass_cartProd_count_eq_catalan_succ,
    BinTree.count_zero, h1, _root_.catalan_two]
