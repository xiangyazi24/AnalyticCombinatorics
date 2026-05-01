# Task — Integer partitions sanity beyond p_20

**File:** `AnalyticCombinatorics/Examples/IntegerPartitions.lean` (append)

The file has `intPartitionClass.count n` sanity through `n = 20` (`627`). Extend through `n = 25`:
- `p_21 = 792`
- `p_22 = 1002`
- `p_23 = 1255`
- `p_24 = 1575`
- `p_25 = 1958`

Use the existing `intPartitionClass_count_eq_card + native_decide` pattern.

If `native_decide` blows up at some `n`, document the threshold.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-intpart-extras4-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/IntegerPartitions.lean`.** Local instances if needed.
