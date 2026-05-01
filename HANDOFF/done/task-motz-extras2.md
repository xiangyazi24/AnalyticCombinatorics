# Task — Motzkin count sanity beyond size 12

**File:** `AnalyticCombinatorics/Examples/MotzkinTrees.lean` (append)

The file has Motzkin count sanity through size 12 (`15511`). Extend through size 15:
- `count 13 = 41835`
- `count 14 = 113634`
- `count 15 = 310572`

Use the existing `decide` / `rw recurrence` pattern. Switch to `native_decide` if needed.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-motz-extras2-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/MotzkinTrees.lean`.** Local instances if needed.
