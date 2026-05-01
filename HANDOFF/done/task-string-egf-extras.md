# Task — Strings additional EGF identities

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

**Goal:** Add a few additional small EGF/OGF identities for stringClass.

```lean
/-- The stringClass.egf coefficient at 0 is 1. -/
example : stringClass.egf.coeff 0 = 1 := by
  rw [CombinatorialClass.coeff_egf, stringClass_count_eq_pow]
  simp

/-- The stringClass.ogf at coeff 0 is 1. -/
example : stringClass.ogf.coeff 0 = 1 := by
  rw [coeff_ogf, stringClass_count_eq_pow]
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-string-egf-extras-reply.md
