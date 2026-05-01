# Task — Even-composition count sanity beyond n=16

**File:** `AnalyticCombinatorics/Examples/CompositionsEven.lean` (append)

The file has `evenCompClass.count n` sanity through `n = 16` (`128`). Extend through `n = 22`:
- `count 17 = 0`
- `count 18 = 256` (= 2^8)
- `count 19 = 0`
- `count 20 = 512` (= 2^9)
- `count 21 = 0`
- `count 22 = 1024` (= 2^10)

Use the existing `decide`/`native_decide` pattern.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-evencomp-extras2-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/CompositionsEven.lean`.** Local instances if needed.
