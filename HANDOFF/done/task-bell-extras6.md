# Task — Bell / SetPartitions sanity beyond n=20

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

The file currently has `labelSetCount posIntClass n` sanity through `n = 20` (Bell(20) = 51724158235372). Extend through `n = 23`.

Bell numbers: B(21) = 474869816156751, B(22) = 4506715738447323, B(23) = 44583569526191395.

Use the same proof shape:
```
example : labelSetCount posIntClass 21 = (474869816156751 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide
```

If `native_decide` times out at some n, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-bell-extras6-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/SetPartitions.lean`.** Local instances if needed.
