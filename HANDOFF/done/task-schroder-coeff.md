# Task — Schroder OGF coeff identity + sanity

**File:** `AnalyticCombinatorics/Examples/SchroderTrees.lean` (append)

```lean
example : SchroderTree.asClass.count 0 = 1 := by decide
example : SchroderTree.asClass.count 1 = 2 := by decide
example : SchroderTree.asClass.count 2 = 6 := by decide
example : SchroderTree.asClass.count 3 = 22 := by decide
```

If sanity examples already exist (per the codex reply), check status and add OGF coefficient identity:

```lean
example (n : ℕ) :
    SchroderTree.asClass.ogf.coeff n = SchroderTree.asClass.count n := by
  rw [coeff_ogf]
```

Use `native_decide` if `decide` is too slow.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-schroder-coeff-reply.md
