# Task — Integer partitions sanity beyond p_25

**File:** `AnalyticCombinatorics/Examples/IntegerPartitions.lean` (append)

The file has `intPartitionClass.count n` sanity through `n = 25` (`1958`). Extend through `n = 30`:
- `p_26 = 2436`
- `p_27 = 3010`
- `p_28 = 3718`
- `p_29 = 4565`
- `p_30 = 5604`

Use `intPartitionClass_count_eq_card + native_decide`.

If `native_decide` blows up, document threshold.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-intpart-extras5-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/IntegerPartitions.lean`.** Local instances if needed.
