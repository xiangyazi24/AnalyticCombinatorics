# Task — Catalan family unification

**File:** `AnalyticCombinatorics/Examples/CatalanFamily.lean` (NEW)

We now have four Catalan-counted classes:

- `BinTree.asClass` — `Examples/BinaryTrees.lean` (`count = catalan` via `catalan_eq_nat_catalan`)
- `planeTreeClass` — `Examples/PlaneTrees.lean` (`count = catalan`)
- `triangulationClass` — `Examples/Triangulations.lean` (`count = catalan`)
- `dyckPathClass` — `Examples/DyckPaths.lean` (`count = catalan`)

Create a small new file `Examples/CatalanFamily.lean` that just **records the pairwise count equalities** at the class level. For each unordered pair, prove a one-line lemma like:

```lean
theorem binTree_count_eq_planeTree (n : ℕ) :
    BinTree.asClass.count n = planeTreeClass.count n := by
  rw [BinTree.asClass_count_eq_catalan, planeTreeClass_count_eq_catalan]
```

(use whatever the actual lemma names are; read the four files first to get the names right).

That's `(4 choose 2) = 6` pairwise lemmas. Also add a one-line summary `theorem` or `example` at the top:

```
example : BinTree.asClass.count 5 = dyckPathClass.count 5 := by ...
```

Just to demonstrate.

Add the new file to `AnalyticCombinatorics.lean`'s imports if applicable.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-catalan-unify-reply.md.
- Don't restate the count↔catalan lemmas — just *use* them.
