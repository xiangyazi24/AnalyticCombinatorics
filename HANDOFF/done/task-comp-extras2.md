# Task — Compositions sanity extension

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

The file has `compositionClass.count n` sanity checks. The standard compositions of n use parts ≥ 1, so count = 2^(n-1) for n ≥ 1. Extend sanity checks for `compositionClass.count` through `n = 15` (or as high as feasible).

Also extend `compositionGe2Class.count` if present, through a few more values. The compositionGe2 count follows Fibonacci: comp_ge2(n) = F(n-1).

Use the same proof patterns already in the file (`rw [...]; native_decide` or `decide`).

If `native_decide` times out at some n, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-comp-extras2-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Compositions.lean`.** Local instances if needed.
