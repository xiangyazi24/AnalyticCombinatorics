# Task — string EGF coeff closed form

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append at end)

**Goal:** Add the rational EGF coefficient form for stringClass.

```lean
example (n : ℕ) :
    stringClass.egf.coeff n = (2 ^ n : ℚ) / n.factorial := by
  rw [CombinatorialClass.coeff_egf, stringClass_count_eq_pow]
  push_cast
  rfl
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-string-egf-coeff-reply.md
