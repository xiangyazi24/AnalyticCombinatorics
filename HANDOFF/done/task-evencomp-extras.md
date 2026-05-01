# Task — Even-composition count sanity beyond n=10

**File:** `AnalyticCombinatorics/Examples/CompositionsEven.lean` (append)

The file has `evenCompClass.count n` sanity through `n = 10` (`16`). Extend through `n = 16` matching the pattern (`count(2k) = 2^(k-1)` for `k≥1`, `count(odd)=0`):

- `count 11 = 0`
- `count 12 = 32` (= 2^5)
- `count 13 = 0`
- `count 14 = 64` (= 2^6)
- `count 15 = 0`
- `count 16 = 128` (= 2^7)

Use the existing `decide`/`native_decide` pattern.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-evencomp-extras-reply.md.
