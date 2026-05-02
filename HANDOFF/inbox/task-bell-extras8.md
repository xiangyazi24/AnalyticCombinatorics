# Task — Bell / SetPartitions sanity beyond n=25

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

Extend `labelSetCount posIntClass n` sanity through n=28. Compute correct Bell numbers yourself from the recurrence. Verify with `lake env lean` before writing the reply.

Use the same proof shape (`rw [labelSetCount_posIntClass_eq_bell]; native_decide`).

## Hard constraints

- Build green. No new sorrys.
- Reply at HANDOFF/outbox/task-bell-extras8-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/SetPartitions.lean`.**
