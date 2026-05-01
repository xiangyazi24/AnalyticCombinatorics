# Task — Motzkin count sanity beyond size 15

**File:** `AnalyticCombinatorics/Examples/MotzkinTrees.lean` (append)

The file has Motzkin count sanity through size 15 (`310572`). Extend through size 18:
- `count 16 = 853467`
- `count 17 = 2356779`
- `count 18 = 6536382`

Use the existing pattern. Switch to `native_decide` if `decide` slows.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-motz-extras3-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/MotzkinTrees.lean`.** Local instances if needed.
