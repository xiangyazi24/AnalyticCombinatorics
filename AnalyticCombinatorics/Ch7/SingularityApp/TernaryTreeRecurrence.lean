import Mathlib
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeBasic

/-!
# The triple-convolution recurrence for ternary trees

We establish the structural equivalence

`TernaryTreeOfSize (n+1) ≃ Σ p : TripleIndex n, (subtrees of sizes p.1, p.2.1, p.2.2)`

and derive a `Fintype` instance for `TernaryTreeOfSize n` together with the
triple-convolution recurrence for `ternaryCount`.
-/

namespace AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS

open scoped BigOperators

/-- Ordered triples of naturals summing to `n`. -/
def TripleIndex (n : ℕ) : Type :=
  {p : ℕ × ℕ × ℕ // p.1 + p.2.1 + p.2.2 = n}

instance (n : ℕ) : DecidableEq (TripleIndex n) := by
  unfold TripleIndex; infer_instance

instance (n : ℕ) : Fintype (TripleIndex n) := by
  unfold TripleIndex
  exact Fintype.subtype
    (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
      (fun p => p.1 + p.2.1 + p.2.2 = n))
    (by
      intro p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, h3⟩; omega
      · intro h; refine ⟨⟨?_, ?_, ?_⟩, h⟩ <;> omega)

/-- The structural equivalence: a ternary tree with `n+1` internal nodes is an
internal node together with three subtrees whose sizes sum to `n`. -/
def succEquiv (n : ℕ) :
    TernaryTreeOfSize (n + 1) ≃
      Σ p : TripleIndex n,
        TernaryTreeOfSize p.val.1 ×
        TernaryTreeOfSize p.val.2.1 ×
        TernaryTreeOfSize p.val.2.2 where
  toFun := fun t =>
    match t with
    | ⟨.leaf, h⟩ => absurd h (by simp)
    | ⟨.node l m r, h⟩ =>
        ⟨⟨(internalSize l, internalSize m, internalSize r),
            show internalSize l + internalSize m + internalSize r = n by
              have := h; simp only [internalSize_node] at this; omega⟩,
          ⟨⟨l, rfl⟩, ⟨m, rfl⟩, ⟨r, rfl⟩⟩⟩
  invFun := fun s =>
    ⟨.node s.2.1.val s.2.2.1.val s.2.2.2.val, by
      obtain ⟨⟨⟨i, j, k⟩, hp⟩, ⟨l, hl⟩, ⟨m, hm⟩, ⟨r, hr⟩⟩ := s
      change internalSize (.node l m r) = n + 1
      simp only [internalSize_node]
      simp only at hl hm hr hp
      omega⟩
  left_inv := by
    rintro ⟨t, ht⟩
    cases t with
    | leaf => simp at ht
    | node l m r => rfl
  right_inv := by
    rintro ⟨⟨⟨i, j, k⟩, hp⟩, ⟨l, hl⟩, ⟨m, hm⟩, ⟨r, hr⟩⟩
    simp only at hl hm hr
    subst hl; subst hm; subst hr
    rfl

/-- `Fintype` instance for ternary trees of a given size, built by strong
recursion on the size via `succEquiv`. -/
instance instFintypeTernaryTreeOfSize : (n : ℕ) → Fintype (TernaryTreeOfSize n)
  | 0 =>
      Fintype.ofEquiv Unit
        { toFun := fun _ => ⟨.leaf, rfl⟩
          invFun := fun _ => ()
          left_inv := fun _ => rfl
          right_inv := by
            rintro ⟨t, ht⟩
            cases t with
            | leaf => rfl
            | node l m r => simp at ht }
  | (n + 1) => by
      have : ∀ p : TripleIndex n,
          Fintype (TernaryTreeOfSize p.val.1 ×
            TernaryTreeOfSize p.val.2.1 ×
            TernaryTreeOfSize p.val.2.2) := by
        intro p
        obtain ⟨⟨i, j, k⟩, hp⟩ := p
        simp only at hp
        have hi : i ≤ n := by omega
        have hj : j ≤ n := by omega
        have hk : k ≤ n := by omega
        haveI := instFintypeTernaryTreeOfSize i
        haveI := instFintypeTernaryTreeOfSize j
        haveI := instFintypeTernaryTreeOfSize k
        infer_instance
      exact Fintype.ofEquiv _ (succEquiv n).symm

/-- The number of full ternary trees with `n` internal nodes. -/
def ternaryCount (n : ℕ) : ℕ :=
  Fintype.card (TernaryTreeOfSize n)

theorem ternaryCount_zero : ternaryCount 0 = 1 := by
  unfold ternaryCount
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨.leaf, rfl⟩, by rintro ⟨t, ht⟩; cases t with
    | leaf => rfl
    | node l m r => simp at ht⟩

theorem ternaryCount_succ (n : ℕ) :
    ternaryCount (n + 1) =
      ∑ p : TripleIndex n,
        ternaryCount p.val.1 *
        ternaryCount p.val.2.1 *
        ternaryCount p.val.2.2 := by
  unfold ternaryCount
  rw [Fintype.card_congr (succEquiv n), Fintype.card_sigma]
  congr 1
  ext p
  rw [Fintype.card_prod, Fintype.card_prod, mul_assoc]

end AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS
