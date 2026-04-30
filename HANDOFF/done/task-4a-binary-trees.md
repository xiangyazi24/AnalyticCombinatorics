# Task 4 — `BinTree.asClass.finite_level` + `ogf_functional_equation`

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean:36` and `:44`

**Pick this up only after tasks 1, 2, 3 are merged.** This one is the biggest of the four — read in full before starting.

## Subtask 4a — `BinTree.asClass.finite_level`

```lean
def asClass : CombinatorialClass where
  Obj   := BinTree
  size  := BinTree.size
  finite_level n := by
    sorry
```

`BinTree.size` is `0` for `leaf`, `1 + size l + size r` for `node l r`. Trees with `size = n` are finite (Catalan-many).

Recipe sketch — strong induction on n:

```lean
finite_level n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- {t : BinTree | size t = n}.Finite
    -- For n = 0: only `leaf`. Singleton, hence finite.
    -- For n > 0: any t with size t = n is `node l r` with size l + size r = n - 1.
    --           So decompose by splitting n-1 = a + b, l ranges over {size = a},
    --           r ranges over {size = b}. Each finite by IH (a < n, b < n). Finite union.
```

Concretely: cover `{t | size t = n}` by `{leaf} ∪ ⋃_{a + b = n - 1} (node '' (level a × level b))` and apply `Set.Finite.union`, `Set.Finite.iUnion` over `Finset.range`, `Set.Finite.image`, `Set.Finite.prod`.

Helper lemma might be useful:
```lean
lemma BinTree.size_node (l r : BinTree) : (node l r).size = 1 + l.size + r.size := rfl
lemma BinTree.size_leaf_iff (t : BinTree) : t.size = 0 ↔ t = leaf := by
  cases t <;> simp [size]; omega
```

## Subtask 4b — `ogf_functional_equation`

```lean
theorem ogf_functional_equation :
    asClass.ogf = 1 + PowerSeries.X * asClass.ogf ^ 2 := by
  sorry
```

This is essentially `disjSum_ogf` ⋄ `cartProd_ogf` applied to the equivalence `BinTree ≃ Unit ⊕ (BinTree × BinTree)` (where `Unit` ↔ `leaf`, `(l, r)` ↔ `node l r`), with the size function matching `Sum.elim 0 (1 + ·.1.size + ·.2.size)`.

Recipe:

1. After `ext n`, `coeff_ogf`, the goal is a coefficient identity:
   `asClass.count n = (1 + PowerSeries.X * asClass.ogf^2).coeff n`.
2. RHS unfolds via `coeff_one`, `coeff_mul`, `coeff_X_mul`, `coeff_pow`/`coeff_mul_self` to:
   - n = 0: `1` (only the `1` term contributes).
   - n ≥ 1: `∑_{k=0}^{n-1} (asClass.count k) * (asClass.count (n-1-k))`.
3. LHS: counting trees of size n by case-splitting `t = leaf` (only when n = 0) vs `t = node l r` (then `size l + size r = n - 1`).
4. Build a Finset bijection between `asClass.level n` and the relevant disjoint union; conclude.

Alternative, **strongly preferred**: prove a `BinTree ≃ Unit ⊕ (BinTree × BinTree)` (sized) equivalence, then apply (re-usable) lemmas:
- `congr_ogf` — if two CombinatorialClasses are level-set-equivalent for every n, they have the same OGF.
- Then `asClass.ogf = (Epsilon.disjSum (asClass.cartProd asClass)).ogf = 1 + asClass.ogf^2 · X`... but you need `cartProd` size to match `1 + l + r`, which it doesn't (it's `l + r`). So you need `cartProd` shifted by 1 (i.e. tagged with an Atom).

The cleanest factoring: prove a coefficient identity directly in subtask 4b (don't try to reuse disjSum_ogf/cartProd_ogf without first proving a `congr_ogf` helper, which is itself a non-trivial lemma).

If 4b proves harder than 4a, **file a blocker** with a reply listing what you proved, what's left, and what you tried. Don't loop.

## Acceptance

- Both sorrys gone, file compiles, build green.

## Hard constraints

- No axiom escape.
- Do not modify `inductive BinTree` or `def size`.
- Two failed attempts → blocker.
