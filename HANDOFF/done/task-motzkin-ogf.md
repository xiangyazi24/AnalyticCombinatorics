# Task — Motzkin OGF identity (state-or-blocker)

**File:** `AnalyticCombinatorics/Examples/MotzkinTrees.lean` (append)

The file has `motzClass.count` and a recurrence. Try to **state and prove** the OGF identity:

`M(z) = 1 + z·M(z) + z²·M(z)²`

Or equivalently:

```lean
theorem motzClass_ogfZ_eq :
    motzClass.ogfZ = 1 + PowerSeries.X * motzClass.ogfZ
                       + PowerSeries.X^2 * motzClass.ogfZ^2 := by
  sorry
```

(Adjust to whatever the file's size convention dictates — read the file first to check whether size = #edges, in which case the OGF identity may have a different shape. The relation should mirror the existing `BinTree.asClass.ogf_functional_equation` pattern.)

## Suggested approach

The recurrence `motzClass.count_succ` (corresponding to leaf | unary | binary) gives the coefficient identity that, packaged as an OGF, becomes the functional equation. Use `BinTree.asClass.ogf_functional_equation` as a template — it likely uses the existing `cartProd_ogf` / `disjSum_ogf` machinery.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-motzkin-ogf-reply.md.
- If the convention or shape is awkward, document the actual relation that holds. Don't paper over.
- Do NOT introduce axioms.
