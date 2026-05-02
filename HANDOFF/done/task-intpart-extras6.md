# Task — Integer Partitions sanity beyond n=30

**File:** `AnalyticCombinatorics/Examples/IntegerPartitions.lean` (append)

The file has `intPartitionClass.count n` sanity through n=30. Extend through n=33 (or as high as feasible).

Partition numbers: p(31)=6842, p(32)=8349, p(33)=10143.

Use the same proof shape as existing entries. If `native_decide` times out, document and stop.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-intpart-extras6-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/IntegerPartitions.lean`.** Local instances if needed.
