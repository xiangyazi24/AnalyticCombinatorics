# Task — permClass OGF small sanity

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append)

```lean
example : permClass.ogf.coeff 0 = 1 := by
  rw [coeff_ogf, permClass_count_eq_factorial]; rfl
example : permClass.ogf.coeff 3 = 6 := by
  rw [coeff_ogf, permClass_count_eq_factorial]; decide
```

Use `native_decide` if needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-perm-ogf-extras-reply.md
