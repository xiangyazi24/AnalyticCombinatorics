# Task 1 — `disjSum_ogf`

**File:** `AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean:110`

```lean
theorem disjSum_ogf : (A.disjSum B).ogf = A.ogf + B.ogf := by sorry
```

## Already in scope (don't redefine)

- `coeff_ogf : coeff n A.ogf = A.count n` (line 38) — proven.
- `level_mem_iff : x ∈ C.level n ↔ C.size x = n` (line 56) — private lemma in this file.
- `disjSum.Obj = A.Obj ⊕ B.Obj`, `disjSum.size = Sum.elim A.size B.size` (line 99–107).

## Recipe sketch

1. `ext n` to reduce to coefficient equality.
2. After `coeff_ogf` on LHS and `map_add, coeff_ogf, coeff_ogf` on RHS, the goal becomes
   `(A.disjSum B).count n = A.count n + B.count n`.
3. Show the level Finset of `disjSum` is the disjoint union of `(A.level n).map ⟨Sum.inl, _⟩` and `(B.level n).map ⟨Sum.inr, _⟩`. Use `Finset.card_disjUnion` or `Finset.card_union_of_disjoint`.
4. Both maps are injective (`Sum.inl_injective`, `Sum.inr_injective`); their images are disjoint because `Sum.inl x = Sum.inr y` is `False`.

Alternative cleaner route: build a `Finset.Equiv` between `(A.disjSum B).level n` and `(A.level n) ⊕ (B.level n)` and apply `Finset.card_congr`. Or:

```
(A.disjSum B).count n
  = ((A.disjSum B).level n).card
  = ... rewrite via a Finset bijection ...
  = (A.level n).card + (B.level n).card
  = A.count n + B.count n
```

## Acceptance

- File compiles, this `sorry` is gone.
- `cd ~/repos/AnalyticCombinatorics && lake build` returns 0 errors. Sorry warnings on other sites are fine.
- Reply with diff summary in `HANDOFF/outbox/task-1-disjSum-ogf-reply.md`.

## Hard constraints

- Do NOT modify the `structure CombinatorialClass` block or `coeff_ogf` (line 38).
- Do NOT replace `sorry` with `axiom` / `True` / `trivial`.
- If two attempts fail, file a blocker — don't loop.
