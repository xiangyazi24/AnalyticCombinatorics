# Task — Bell numbers small expanded list

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

**Goal:** Add an `example` listing several small Bell values via the established bridge.

```lean
/-! Bell sequence sanity dump: 1,1,2,5,15,52,203,877,4140,21147,115975,678570. -/
example : labelSetCount posIntClass 11 = (678570 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]; decide
```

Use `native_decide` if too slow.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bell-bivariate-reply.md
