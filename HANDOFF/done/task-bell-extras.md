# Task — Bell sanity beyond B_15

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

The file has Bell sanity through `B_15`. Push to `B_18`. Values:

- `B_16 = 10480142147`
- `B_17 = 82864869804`
- `B_18 = 682076806159`

Use the same `labelSetCount_posIntClass_eq_bell + native_decide` pattern as the existing `B_12..B_15`.

If `native_decide` chokes at `B_18`, document the threshold (which is interesting kernel-perf data) and ship whichever values worked.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-bell-extras-reply.md.
