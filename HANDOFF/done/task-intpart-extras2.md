# Task — Integer-partition count sanity beyond p_10

**File:** `AnalyticCombinatorics/Examples/IntegerPartitions.lean` (append)

The file has `intPartitionClass.count n` sanity through `n = 10` (`42`). Extend through `n = 15`:
- `p_11 = 56`
- `p_12 = 77`
- `p_13 = 101`
- `p_14 = 135`
- `p_15 = 176`

Use the existing `intPartitionClass_count_eq_card + native_decide` pattern. If `native_decide` blows up at some `n`, document the threshold.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-intpart-extras2-reply.md.
