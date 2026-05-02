# Task — Compositions sanity beyond n=15

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

The file has `compositionClass.count n` sanity through n=15 and `compositionGe2Class.count` checks. Extend both through n=18 (or as high as feasible).

Standard compositions: count(n) = 2^(n-1) for n ≥ 1, count(0) = 1.
Compositions with parts ≥ 2: count follows Fibonacci.

Use the same proof patterns already in the file.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-comp-extras3-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Compositions.lean`.** Local instances if needed.
