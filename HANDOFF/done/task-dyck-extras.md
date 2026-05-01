# Task — DyckPath count sanity beyond n=10

**File:** `AnalyticCombinatorics/Examples/DyckPaths.lean` (append)

The file has `dyckPathClass.count n` sanity through `n = 10` (`16796`). Extend through `n = 14` matching catalan:
- `n = 11`: `58786`
- `n = 12`: `208012`
- `n = 13`: `742900`
- `n = 14`: `2674440`

Use the existing `dyckPathClass_count + native_decide` pattern.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-dyck-extras-reply.md.
