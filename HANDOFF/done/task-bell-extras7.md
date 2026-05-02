# Task — Bell / SetPartitions sanity beyond n=22

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

The file has `labelSetCount posIntClass n` sanity through n=22 (Bell(22) = 4506715738447323). Extend through n=25.

Use the same proof shape:
```
set_option linter.style.nativeDecide false in
example : labelSetCount posIntClass 23 = (BELL_23 : ℚ) := by
  rw [labelSetCount_posIntClass_eq_bell]
  native_decide
```

Compute Bell numbers yourself using the recurrence B(n+1) = sum_{k=0}^{n} C(n,k)*B(k). Do NOT use the values 44583569526191395 for B(23) — that was wrong.

If `native_decide` times out at some n, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-bell-extras7-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/SetPartitions.lean`.** Local instances if needed.
