# Reply — Task 1: `disjSum_ogf`

**Status: done**

## Proof landed

`AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean:110` — `sorry` removed.

`lake build` output: `Build completed successfully (2695 jobs)` — 0 errors, sorry warnings on pre-existing sites only.

## Diff summary

1. Added `import Mathlib.Data.Finset.Sum` (needed for `Finset.toLeft`, `Finset.toRight`, `Finset.card_toLeft_add_card_toRight`).

2. Replaced `sorry` with:

```lean
theorem disjSum_ogf : (A.disjSum B).ogf = A.ogf + B.ogf := by
  ext n
  simp only [map_add, coeff_ogf]
  show (A.disjSum B).count n = A.count n + B.count n
  simp only [count]
  have hL : ((A.disjSum B).level n).toLeft = A.level n := by
    ext x
    simp only [Finset.mem_toLeft, level, Set.Finite.mem_toFinset, Set.mem_setOf_eq, disjSum,
               Sum.elim_inl]
  have hR : ((A.disjSum B).level n).toRight = B.level n := by
    ext x
    simp only [Finset.mem_toRight, level, Set.Finite.mem_toFinset, Set.mem_setOf_eq, disjSum,
               Sum.elim_inr]
  have heq := Finset.card_toLeft_add_card_toRight (u := (A.disjSum B).level n)
  rw [hL, hR] at heq
  exact heq.symm
```

## Strategy note

Avoided `Finset.image` (requires `[DecidableEq (A.Obj ⊕ B.Obj)]` which is not in scope). Used `Finset.toLeft`/`toRight` decomposition from `Mathlib.Data.Finset.Sum` instead — no `DecidableEq` needed. The key lemmas are `Finset.mem_toLeft`, `Finset.mem_toRight`, and `Finset.card_toLeft_add_card_toRight`.
