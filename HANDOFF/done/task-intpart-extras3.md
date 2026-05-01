# Task — Integer partitions sanity beyond p_15

**File:** `AnalyticCombinatorics/Examples/IntegerPartitions.lean` (append)

The file has `intPartitionClass.count n` sanity through `n = 15` (`176`). Extend through `n = 20`:
- `p_16 = 231`
- `p_17 = 297`
- `p_18 = 385`
- `p_19 = 490`
- `p_20 = 627`

Use the existing `intPartitionClass_count_eq_card + native_decide` pattern.

If `native_decide` blows up at some `n`, document the threshold and ship whichever values worked.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-intpart-extras3-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/IntegerPartitions.lean`.** Local instances if needed.
