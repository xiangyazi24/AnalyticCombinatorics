# Task — Motzkin sanity counts

**File:** `AnalyticCombinatorics/Examples/MotzkinTrees.lean` (append)

Motzkin numbers OEIS A001006: 1, 1, 2, 4, 9, 21, 51, 127, 323.

```lean
example : MotzTree.asClass.count 0 = 1 := MotzTree.count_zero
-- Add more sanity examples 1..6 if you can compute MotzTree.asClass.count via the recurrence.
```

If MotzTree.count_succ (or similar) is defined and computable, you can add:
```lean
example : MotzTree.asClass.count 1 = 1 := by
  rw [MotzTree.count_succ]; decide
```

If decide doesn't reduce because the recurrence references catalan-like terms, file blocker.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-motzkin-sanity-reply.md
