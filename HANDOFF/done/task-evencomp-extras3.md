# Task — Even-composition count sanity beyond n=22

**File:** `AnalyticCombinatorics/Examples/CompositionsEven.lean` (append)

The file has `evenCompClass.count n` sanity through `n = 22` (`1024`). Extend through `n = 28`:
- `count 23 = 0`
- `count 24 = 2048` (= 2^11)
- `count 25 = 0`
- `count 26 = 4096` (= 2^12)
- `count 27 = 0`
- `count 28 = 8192` (= 2^13)

Use the existing pattern.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-evencomp-extras3-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/CompositionsEven.lean`.** Local instances if needed.
