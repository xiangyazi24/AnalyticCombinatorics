# Task — Surjections sanity beyond n=20

**File:** `AnalyticCombinatorics/Examples/Surjections.lean` (append)

Extend `surjectionClass.count n` (Fubini/ordered Bell numbers) through n=23. Compute the correct Fubini numbers yourself using the recurrence or Stirling numbers. Do NOT use pre-computed values from the task description — verify with `lake env lean` before writing the reply.

Use the same proof shape as existing entries (`rw [surjectionClass_count_eq_fubini]; native_decide`).

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-surj-extras6-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Surjections.lean`.**
