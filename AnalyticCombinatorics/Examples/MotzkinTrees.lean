import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.Sequences

open PowerSeries CombinatorialClass

/-- Unary-binary trees: leaf, unary node, or binary node. -/
inductive MotzTree : Type
  | leaf : MotzTree
  | unary : MotzTree → MotzTree
  | binary : MotzTree → MotzTree → MotzTree

namespace MotzTree

/-- Size = number of edges. -/
def size : MotzTree → ℕ
  | leaf => 0
  | unary t => 1 + t.size
  | binary l r => 2 + l.size + r.size

private lemma size_leaf_eq : MotzTree.leaf.size = 0 := rfl
private lemma size_unary_eq (t : MotzTree) : (MotzTree.unary t).size = 1 + t.size := rfl
private lemma size_binary_eq (l r : MotzTree) :
    (MotzTree.binary l r).size = 2 + l.size + r.size := rfl

/-- The combinatorial class of Motzkin trees. -/
noncomputable def asClass : CombinatorialClass where
  Obj := MotzTree
  size := MotzTree.size
  finite_level n := by
    induction n using Nat.strong_induction_on
    rename_i m ih
    cases m with
    | zero =>
      apply Set.Finite.subset (Set.finite_singleton MotzTree.leaf)
      intro t ht
      simp only [Set.mem_setOf_eq] at ht
      simp only [Set.mem_singleton_iff]
      cases t with
      | leaf => rfl
      | unary u =>
        simp only [size_unary_eq] at ht
        omega
      | binary l r =>
        simp only [size_binary_eq] at ht
        omega
    | succ k =>
      apply Set.Finite.subset
        (((ih k (Nat.lt_succ_self k)).image MotzTree.unary).union
          (Set.finite_iUnion (fun i : Fin (k + 1) =>
            ((ih i.val i.isLt).prod
              (ih (k - 1 - i.val) (by omega))).image
                (fun p => MotzTree.binary p.1 p.2))))
      intro t ht
      simp only [Set.mem_setOf_eq] at ht
      cases t with
      | leaf =>
        simp only [size_leaf_eq] at ht
        omega
      | unary u =>
        simp only [size_unary_eq] at ht
        simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
        left
        exact ⟨u, by omega, rfl⟩
      | binary l r =>
        simp only [size_binary_eq] at ht
        have hr : MotzTree.size r = k - 1 - MotzTree.size l := by omega
        simp only [Set.mem_union, Set.mem_iUnion, Set.mem_image, Set.mem_prod, Set.mem_setOf_eq]
        right
        exact ⟨⟨l.size, by omega⟩, (l, r), ⟨rfl, hr⟩, rfl⟩

/-- The number of Motzkin trees with `n` edges. -/
noncomputable def count (n : ℕ) : ℕ := asClass.count n

private lemma mem_level_iff (m : ℕ) (t : MotzTree) :
    t ∈ asClass.level m ↔ asClass.size t = m := by
  change t ∈ (asClass.finite_level m).toFinset ↔ asClass.size t = m
  exact (asClass.finite_level m).mem_toFinset.trans (by simp)

/-- Only `leaf` has size zero. -/
lemma count_zero : asClass.count 0 = 1 := by
  simp only [CombinatorialClass.count]
  rw [Finset.card_eq_one]
  refine ⟨MotzTree.leaf, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact (mem_level_iff 0 MotzTree.leaf).mpr rfl
  · intro t ht
    have hsz : t.size = 0 := (mem_level_iff 0 t).mp ht
    cases t with
    | leaf => rfl
    | unary u =>
      simp only [MotzTree.size_unary_eq] at hsz
      omega
    | binary l r =>
      simp only [MotzTree.size_binary_eq] at hsz
      omega

/-- Only `unary leaf` has size one. -/
lemma count_one : asClass.count 1 = 1 := by
  simp only [CombinatorialClass.count]
  rw [Finset.card_eq_one]
  refine ⟨MotzTree.unary MotzTree.leaf, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact (mem_level_iff 1 (MotzTree.unary MotzTree.leaf)).mpr rfl
  · intro t ht
    have hsz : t.size = 1 := (mem_level_iff 1 t).mp ht
    cases t with
    | leaf =>
      simp only [MotzTree.size_leaf_eq] at hsz
      omega
    | unary u =>
      simp only [MotzTree.size_unary_eq] at hsz
      cases u with
      | leaf => rfl
      | unary v =>
        simp only [MotzTree.size_unary_eq] at hsz
        omega
      | binary l r =>
        simp only [MotzTree.size_binary_eq] at hsz
        omega
    | binary l r =>
      simp only [MotzTree.size_binary_eq] at hsz
      omega

/-- Recursion on counts:
    a tree of size `n + 2` is either a unary root over a tree of size `n + 1`,
    or a binary root over two subtrees whose sizes sum to `n`. -/
lemma count_succ_succ (n : ℕ) :
    asClass.count (n + 2) =
      asClass.count (n + 1) +
        ∑ p ∈ Finset.antidiagonal n, asClass.count p.1 * asClass.count p.2 := by
  let binaryFs : Finset (Σ _ : ℕ × ℕ, MotzTree × MotzTree) :=
    (Finset.antidiagonal n).sigma (fun p => asClass.level p.1 ×ˢ asClass.level p.2)
  let rhsFs : Finset (MotzTree ⊕ (Σ _ : ℕ × ℕ, MotzTree × MotzTree)) :=
    (asClass.level (n + 1)).disjSum binaryFs
  let fwd : (x : MotzTree ⊕ (Σ _ : ℕ × ℕ, MotzTree × MotzTree)) → x ∈ rhsFs →
      MotzTree :=
    fun x _ =>
      match x with
      | Sum.inl t => MotzTree.unary t
      | Sum.inr y => MotzTree.binary y.2.1 y.2.2
  have extractBinary :
      ∀ y : Σ _ : ℕ × ℕ, MotzTree × MotzTree, y ∈ binaryFs →
        y.1 ∈ Finset.antidiagonal n ∧
        y.2.1 ∈ asClass.level y.1.1 ∧
        y.2.2 ∈ asClass.level y.1.2 := by
    intro y hy
    refine ⟨(Finset.mem_sigma.mp hy).1,
            (Finset.mem_product.mp (Finset.mem_sigma.mp hy).2).1,
            (Finset.mem_product.mp (Finset.mem_sigma.mp hy).2).2⟩
  have hcard : rhsFs.card = (asClass.level (n + 2)).card := by
    apply Finset.card_bij fwd
    · intro x hx
      cases x with
      | inl t =>
        have ht : t ∈ asClass.level (n + 1) := by
          rcases Finset.mem_disjSum.mp hx with ⟨a, ha, heq⟩ | ⟨b, hb, heq⟩
          · cases heq
            exact ha
          · cases heq
        apply (mem_level_iff (n + 2) (MotzTree.unary t)).mpr
        have hsize : t.size = n + 1 := (mem_level_iff (n + 1) t).mp ht
        change 1 + t.size = n + 2
        omega
      | inr y =>
        have hy : y ∈ binaryFs := by
          rcases Finset.mem_disjSum.mp hx with ⟨a, ha, heq⟩ | ⟨b, hb, heq⟩
          · cases heq
          · cases heq
            exact hb
        obtain ⟨hp, hl, hr⟩ := extractBinary y hy
        have hp_sum : y.1.1 + y.1.2 = n := Finset.mem_antidiagonal.mp hp
        have hlsize : y.2.1.size = y.1.1 := (mem_level_iff _ _).mp hl
        have hrsize : y.2.2.size = y.1.2 := (mem_level_iff _ _).mp hr
        apply (mem_level_iff (n + 2) (MotzTree.binary y.2.1 y.2.2)).mpr
        change 2 + y.2.1.size + y.2.2.size = n + 2
        omega
    · intro x₁ hx₁ x₂ hx₂ heq
      cases x₁ with
      | inl t₁ =>
        cases x₂ with
        | inl t₂ =>
          change MotzTree.unary t₁ = MotzTree.unary t₂ at heq
          injection heq with ht
          simp [ht]
        | inr y₂ =>
          change MotzTree.unary t₁ = MotzTree.binary y₂.2.1 y₂.2.2 at heq
          cases heq
      | inr y₁ =>
        cases x₂ with
        | inl t₂ =>
          change MotzTree.binary y₁.2.1 y₁.2.2 = MotzTree.unary t₂ at heq
          cases heq
        | inr y₂ =>
          have hy₁ : y₁ ∈ binaryFs := by
            rcases Finset.mem_disjSum.mp hx₁ with ⟨a, ha, heq⟩ | ⟨b, hb, heq⟩
            · cases heq
            · cases heq
              exact hb
          have hy₂ : y₂ ∈ binaryFs := by
            rcases Finset.mem_disjSum.mp hx₂ with ⟨a, ha, heq⟩ | ⟨b, hb, heq⟩
            · cases heq
            · cases heq
              exact hb
          obtain ⟨-, hl₁, hr₁⟩ := extractBinary y₁ hy₁
          obtain ⟨-, hl₂, hr₂⟩ := extractBinary y₂ hy₂
          have hlsize₁ : y₁.2.1.size = y₁.1.1 := (mem_level_iff _ _).mp hl₁
          have hlsize₂ : y₂.2.1.size = y₂.1.1 := (mem_level_iff _ _).mp hl₂
          have hrsize₁ : y₁.2.2.size = y₁.1.2 := (mem_level_iff _ _).mp hr₁
          have hrsize₂ : y₂.2.2.size = y₂.1.2 := (mem_level_iff _ _).mp hr₂
          change MotzTree.binary y₁.2.1 y₁.2.2 =
            MotzTree.binary y₂.2.1 y₂.2.2 at heq
          injection heq with hl hr
          have hk : y₁.1.1 = y₂.1.1 := by rw [← hlsize₁, hl, hlsize₂]
          have hm : y₁.1.2 = y₂.1.2 := by rw [← hrsize₁, hr, hrsize₂]
          obtain ⟨⟨k₁, m₁⟩, l₁, r₁⟩ := y₁
          obtain ⟨⟨k₂, m₂⟩, l₂, r₂⟩ := y₂
          simp_all
    · intro t ht
      have hsz : t.size = n + 2 := (mem_level_iff _ _).mp ht
      cases t with
      | leaf =>
        exfalso
        simp only [MotzTree.size_leaf_eq] at hsz
        omega
      | unary u =>
        simp only [MotzTree.size_unary_eq] at hsz
        refine ⟨Sum.inl u, ?_, rfl⟩
        apply Finset.mem_disjSum.mpr
        apply Or.inl
        refine ⟨u, ?_, rfl⟩
        apply (mem_level_iff (n + 1) u).mpr
        change u.size = n + 1
        omega
      | binary l r =>
        simp only [MotzTree.size_binary_eq] at hsz
        refine ⟨Sum.inr ⟨(l.size, r.size), (l, r)⟩, ?_, rfl⟩
        apply Finset.mem_disjSum.mpr
        apply Or.inr
        refine ⟨⟨(l.size, r.size), (l, r)⟩, ?_, rfl⟩
        apply Finset.mem_sigma.mpr
        refine ⟨?_, ?_⟩
        · apply Finset.mem_antidiagonal.mpr
          change l.size + r.size = n
          omega
        · apply Finset.mem_product.mpr
          exact ⟨(mem_level_iff _ _).mpr rfl, (mem_level_iff _ _).mpr rfl⟩
  rw [show asClass.count (n + 2) = (asClass.level (n + 2)).card from rfl, ← hcard,
      show asClass.count (n + 1) = (asClass.level (n + 1)).card from rfl]
  change ((asClass.level (n + 1)).disjSum binaryFs).card =
    (asClass.level (n + 1)).card +
      ∑ p ∈ Finset.antidiagonal n, asClass.count p.1 * asClass.count p.2
  rw [Finset.card_disjSum, Finset.card_sigma]
  apply congrArg (fun x => asClass.count (n + 1) + x)
  apply Finset.sum_congr rfl
  intro p _
  exact Finset.card_product _ _

/-- The OGF `M(z)` satisfies `M = 1 + z M + z² M²`. -/
theorem ogf_functional_equation :
    asClass.ogf =
      1 + PowerSeries.X * asClass.ogf + PowerSeries.X * (PowerSeries.X * asClass.ogf ^ 2) := by
  ext n
  rw [map_add, map_add, coeff_one, coeff_ogf]
  rcases n with _ | m
  · rw [count_zero]
    simp [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_X]
  · rcases m with _ | k
    · rw [count_one, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
      simp [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_X,
        coeff_ogf, count_zero]
    · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_succ_X_mul, sq, coeff_mul, count_succ_succ k, coeff_ogf]
      simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
      apply congrArg (fun x => asClass.count (k + 1) + x)
      apply Finset.sum_congr rfl
      intro p _
      rw [coeff_ogf, coeff_ogf]

example : MotzTree.asClass.count 0 = 1 := count_zero

example : MotzTree.asClass.count 1 = 1 := count_one

example : MotzTree.asClass.count 2 = 2 := by
  rw [show 2 = 0 + 2 by norm_num, count_succ_succ 0, count_one]
  norm_num [Finset.antidiagonal, count_zero]

example : MotzTree.asClass.count 3 = 4 := by
  have h2 : asClass.count 2 = 2 := by
    rw [show 2 = 0 + 2 by norm_num, count_succ_succ 0, count_one]
    norm_num [Finset.antidiagonal, count_zero]
  rw [show 3 = 1 + 2 by norm_num, count_succ_succ 1]
  norm_num [Finset.antidiagonal, count_zero, count_one, h2]

example : MotzTree.asClass.count 4 = 9 := by
  have h2 : asClass.count 2 = 2 := by
    rw [show 2 = 0 + 2 by norm_num, count_succ_succ 0, count_one]
    norm_num [Finset.antidiagonal, count_zero]
  have h3 : asClass.count 3 = 4 := by
    rw [show 3 = 1 + 2 by norm_num, count_succ_succ 1]
    norm_num [Finset.antidiagonal, count_zero, count_one, h2]
  rw [show 4 = 2 + 2 by norm_num, count_succ_succ 2]
  norm_num [Finset.antidiagonal, count_zero, count_one, h2, h3]

example : MotzTree.asClass.count 5 = 21 := by
  have h2 : asClass.count 2 = 2 := by
    rw [show 2 = 0 + 2 by norm_num, count_succ_succ 0, count_one]
    norm_num [Finset.antidiagonal, count_zero]
  have h3 : asClass.count 3 = 4 := by
    rw [show 3 = 1 + 2 by norm_num, count_succ_succ 1]
    norm_num [Finset.antidiagonal, count_zero, count_one, h2]
  have h4 : asClass.count 4 = 9 := by
    rw [show 4 = 2 + 2 by norm_num, count_succ_succ 2]
    norm_num [Finset.antidiagonal, count_zero, count_one, h2, h3]
  rw [show 5 = 3 + 2 by norm_num, count_succ_succ 3]
  norm_num [Finset.antidiagonal, count_zero, count_one, h2, h3, h4]

example : MotzTree.asClass.count 6 = 51 := by
  have h2 : asClass.count 2 = 2 := by
    rw [show 2 = 0 + 2 by norm_num, count_succ_succ 0, count_one]
    norm_num [Finset.antidiagonal, count_zero]
  have h3 : asClass.count 3 = 4 := by
    rw [show 3 = 1 + 2 by norm_num, count_succ_succ 1]
    norm_num [Finset.antidiagonal, count_zero, count_one, h2]
  have h4 : asClass.count 4 = 9 := by
    rw [show 4 = 2 + 2 by norm_num, count_succ_succ 2]
    norm_num [Finset.antidiagonal, count_zero, count_one, h2, h3]
  have h5 : asClass.count 5 = 21 := by
    rw [show 5 = 3 + 2 by norm_num, count_succ_succ 3]
    norm_num [Finset.antidiagonal, count_zero, count_one, h2, h3, h4]
  rw [show 6 = 4 + 2 by norm_num, count_succ_succ 4]
  norm_num [Finset.antidiagonal, count_zero, count_one, h2, h3, h4, h5]

private lemma count_two : MotzTree.asClass.count 2 = 2 := by
  rw [show 2 = 0 + 2 by norm_num, count_succ_succ 0, count_one]
  norm_num [Finset.antidiagonal, count_zero]

private lemma count_three : MotzTree.asClass.count 3 = 4 := by
  rw [show 3 = 1 + 2 by norm_num, count_succ_succ 1]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two]

private lemma count_four : MotzTree.asClass.count 4 = 9 := by
  rw [show 4 = 2 + 2 by norm_num, count_succ_succ 2]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three]

private lemma count_five : MotzTree.asClass.count 5 = 21 := by
  rw [show 5 = 3 + 2 by norm_num, count_succ_succ 3]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four]

private lemma count_six : MotzTree.asClass.count 6 = 51 := by
  rw [show 6 = 4 + 2 by norm_num, count_succ_succ 4]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five]

private lemma count_seven : MotzTree.asClass.count 7 = 127 := by
  rw [show 7 = 5 + 2 by norm_num, count_succ_succ 5]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five, count_six]

private lemma count_eight : MotzTree.asClass.count 8 = 323 := by
  rw [show 8 = 6 + 2 by norm_num, count_succ_succ 6]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five, count_six, count_seven]

private lemma count_nine : MotzTree.asClass.count 9 = 835 := by
  rw [show 9 = 7 + 2 by norm_num, count_succ_succ 7]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five, count_six, count_seven, count_eight]

private lemma count_ten : MotzTree.asClass.count 10 = 2188 := by
  rw [show 10 = 8 + 2 by norm_num, count_succ_succ 8]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five, count_six, count_seven, count_eight, count_nine]

private lemma count_eleven : MotzTree.asClass.count 11 = 5798 := by
  rw [show 11 = 9 + 2 by norm_num, count_succ_succ 9]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five, count_six, count_seven, count_eight, count_nine, count_ten]

private lemma count_twelve : MotzTree.asClass.count 12 = 15511 := by
  rw [show 12 = 10 + 2 by norm_num, count_succ_succ 10]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five, count_six, count_seven, count_eight, count_nine, count_ten, count_eleven]

private lemma count_thirteen : MotzTree.asClass.count 13 = 41835 := by
  rw [show 13 = 11 + 2 by norm_num, count_succ_succ 11]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five, count_six, count_seven, count_eight, count_nine, count_ten, count_eleven,
    count_twelve]

private lemma count_fourteen : MotzTree.asClass.count 14 = 113634 := by
  rw [show 14 = 12 + 2 by norm_num, count_succ_succ 12]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five, count_six, count_seven, count_eight, count_nine, count_ten, count_eleven,
    count_twelve, count_thirteen]

private lemma count_fifteen : MotzTree.asClass.count 15 = 310572 := by
  rw [show 15 = 13 + 2 by norm_num, count_succ_succ 13]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five, count_six, count_seven, count_eight, count_nine, count_ten, count_eleven,
    count_twelve, count_thirteen, count_fourteen]

private lemma count_sixteen : MotzTree.asClass.count 16 = 853467 := by
  rw [show 16 = 14 + 2 by norm_num, count_succ_succ 14]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five, count_six, count_seven, count_eight, count_nine, count_ten, count_eleven,
    count_twelve, count_thirteen, count_fourteen, count_fifteen]

private lemma count_seventeen : MotzTree.asClass.count 17 = 2356779 := by
  rw [show 17 = 15 + 2 by norm_num, count_succ_succ 15]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five, count_six, count_seven, count_eight, count_nine, count_ten, count_eleven,
    count_twelve, count_thirteen, count_fourteen, count_fifteen, count_sixteen]

private lemma count_eighteen : MotzTree.asClass.count 18 = 6536382 := by
  rw [show 18 = 16 + 2 by norm_num, count_succ_succ 16]
  norm_num [Finset.antidiagonal, count_zero, count_one, count_two, count_three, count_four,
    count_five, count_six, count_seven, count_eight, count_nine, count_ten, count_eleven,
    count_twelve, count_thirteen, count_fourteen, count_fifteen, count_sixteen,
    count_seventeen]

private lemma count_nineteen : MotzTree.asClass.count 19 = 18199284 := by
  rw [show 19 = 17 + 2 by norm_num, count_succ_succ 17]
  norm_num [Finset.antidiagonal]
  rw [count_zero, count_one, count_two, count_three, count_four, count_five, count_six,
    count_seven, count_eight, count_nine, count_ten, count_eleven, count_twelve,
    count_thirteen, count_fourteen, count_fifteen, count_sixteen, count_seventeen,
    count_eighteen]
  decide

private lemma count_twenty : MotzTree.asClass.count 20 = 50852019 := by
  rw [show 20 = 18 + 2 by norm_num, count_succ_succ 18]
  norm_num [Finset.antidiagonal]
  rw [count_zero, count_one, count_two, count_three, count_four, count_five, count_six,
    count_seven, count_eight, count_nine, count_ten, count_eleven, count_twelve,
    count_thirteen, count_fourteen, count_fifteen, count_sixteen, count_seventeen,
    count_eighteen, count_nineteen]
  decide

private lemma count_twentyone : MotzTree.asClass.count 21 = 142547559 := by
  rw [show 21 = 19 + 2 by norm_num, count_succ_succ 19]
  norm_num [Finset.antidiagonal]
  rw [count_zero, count_one, count_two, count_three, count_four, count_five, count_six,
    count_seven, count_eight, count_nine, count_ten, count_eleven, count_twelve,
    count_thirteen, count_fourteen, count_fifteen, count_sixteen, count_seventeen,
    count_eighteen, count_nineteen, count_twenty]
  decide

private lemma count_twentytwo : MotzTree.asClass.count 22 = 400763223 := by
  rw [show 22 = 20 + 2 by norm_num, count_succ_succ 20]
  norm_num [Finset.antidiagonal]
  rw [count_zero, count_one, count_two, count_three, count_four, count_five, count_six,
    count_seven, count_eight, count_nine, count_ten, count_eleven, count_twelve,
    count_thirteen, count_fourteen, count_fifteen, count_sixteen, count_seventeen,
    count_eighteen, count_nineteen, count_twenty, count_twentyone]
  decide

private lemma count_twentythree : MotzTree.asClass.count 23 = 1129760415 := by
  rw [show 23 = 21 + 2 by norm_num, count_succ_succ 21]
  norm_num [Finset.antidiagonal]
  rw [count_zero, count_one, count_two, count_three, count_four, count_five, count_six,
    count_seven, count_eight, count_nine, count_ten, count_eleven, count_twelve,
    count_thirteen, count_fourteen, count_fifteen, count_sixteen, count_seventeen,
    count_eighteen, count_nineteen, count_twenty, count_twentyone, count_twentytwo]
  decide

private lemma count_twentyfour : MotzTree.asClass.count 24 = 3192727797 := by
  rw [show 24 = 22 + 2 by norm_num, count_succ_succ 22]
  norm_num [Finset.antidiagonal]
  rw [count_zero, count_one, count_two, count_three, count_four, count_five, count_six,
    count_seven, count_eight, count_nine, count_ten, count_eleven, count_twelve,
    count_thirteen, count_fourteen, count_fifteen, count_sixteen, count_seventeen,
    count_eighteen, count_nineteen, count_twenty, count_twentyone, count_twentytwo,
    count_twentythree]
  decide

example : decide (MotzTree.asClass.count 7 = 127) = true := by
  rw [count_seven]
  decide

example : decide (MotzTree.asClass.count 8 = 323) = true := by
  rw [count_eight]
  decide

example : decide (MotzTree.asClass.count 9 = 835) = true := by
  rw [count_nine]
  decide

example : decide (MotzTree.asClass.count 10 = 2188) = true := by
  rw [count_ten]
  decide

example : decide (MotzTree.asClass.count 11 = 5798) = true := by
  rw [count_eleven]
  decide

example : decide (MotzTree.asClass.count 12 = 15511) = true := by
  rw [count_twelve]
  decide

example : decide (MotzTree.asClass.count 13 = 41835) = true := by
  rw [count_thirteen]
  decide

example : decide (MotzTree.asClass.count 14 = 113634) = true := by
  rw [count_fourteen]
  decide

example : decide (MotzTree.asClass.count 15 = 310572) = true := by
  rw [count_fifteen]
  decide

example : decide (MotzTree.asClass.count 16 = 853467) = true := by
  rw [count_sixteen]
  decide

example : decide (MotzTree.asClass.count 17 = 2356779) = true := by
  rw [count_seventeen]
  decide

example : decide (MotzTree.asClass.count 18 = 6536382) = true := by
  rw [count_eighteen]
  decide

example : decide (MotzTree.asClass.count 19 = 18199284) = true := by
  rw [count_nineteen]
  decide

example : decide (MotzTree.asClass.count 20 = 50852019) = true := by
  rw [count_twenty]
  decide

example : decide (MotzTree.asClass.count 21 = 142547559) = true := by
  rw [count_twentyone]
  decide

example : decide (MotzTree.asClass.count 22 = 400763223) = true := by
  rw [count_twentytwo]
  decide

example : decide (MotzTree.asClass.count 23 = 1129760415) = true := by
  rw [count_twentythree]
  decide

example : decide (MotzTree.asClass.count 24 = 3192727797) = true := by
  rw [count_twentyfour]
  decide

example : decide (MotzTree.asClass.count 7 + MotzTree.asClass.count 6 = 178) = true := by
  rw [count_seven, count_six]
  decide

example : decide (MotzTree.asClass.count 8 = MotzTree.asClass.count 7 + 196) = true := by
  rw [count_eight, count_seven]
  decide

example (n : ℕ) :
    MotzTree.asClass.ogf.coeff n = MotzTree.asClass.count n := by
  rw [coeff_ogf]

/-- Numerical check of the Motzkin recurrence at `n = 3`. -/
example :
    asClass.count (3 + 2) = asClass.count (3 + 1) +
      ∑ k ∈ Finset.range (3 + 1), asClass.count k * asClass.count (3 - k) := by
  rw [show 3 + 2 = 5 by norm_num, show 3 + 1 = 4 by norm_num, count_five,
    count_four]
  norm_num [Finset.range, count_zero, count_one, count_two, count_three]

/-- Alias for the Motzkin-tree combinatorial class. -/
noncomputable abbrev motzClass : CombinatorialClass := asClass

/-- Motzkin recurrence in range-indexed form:
    `M(n+2) = M(n+1) + ∑_{k=0}^{n} M(k) M(n-k)`. -/
theorem motzClass_count_recurrence (n : ℕ) :
    motzClass.count (n + 2) = motzClass.count (n + 1) +
      ∑ k ∈ Finset.range (n + 1), motzClass.count k * motzClass.count (n - k) := by
  change asClass.count (n + 2) = asClass.count (n + 1) +
      ∑ k ∈ Finset.range (n + 1), asClass.count k * asClass.count (n - k)
  rw [count_succ_succ,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l => asClass.count k * asClass.count l) n]

/-- The Motzkin-tree OGF over `ℤ[[z]]` satisfies `M = 1 + z M + z² M²`. -/
theorem motzClass_ogfZ_eq :
    ogfZ motzClass = 1 + PowerSeries.X * ogfZ motzClass
                       + PowerSeries.X ^ 2 * (ogfZ motzClass) ^ 2 := by
  change ogfZ asClass = 1 + PowerSeries.X * ogfZ asClass
      + PowerSeries.X ^ 2 * (ogfZ asClass) ^ 2
  unfold ogfZ
  have h := congrArg (PowerSeries.map (algebraMap ℕ ℤ)) ogf_functional_equation
  simpa [PowerSeries.map_X, pow_two, mul_assoc] using h

end MotzTree
