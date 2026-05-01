# Task — derangementClass OGF small sanity

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append)

```lean
example : derangementClass.ogf.coeff 0 = 1 := by
  rw [coeff_ogf, derangementClass_count_eq_numDerangements]; rfl
example : derangementClass.ogf.coeff 1 = 0 := by
  rw [coeff_ogf, derangementClass_count_eq_numDerangements]; rfl
example : derangementClass.ogf.coeff 4 = 9 := by
  rw [coeff_ogf, derangementClass_count_eq_numDerangements]; decide
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-derangement-ogf-extras-reply.md
