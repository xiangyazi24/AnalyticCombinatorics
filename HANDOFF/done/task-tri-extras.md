# Task — Triangulation count sanity beyond n=12

**File:** `AnalyticCombinatorics/Examples/Triangulations.lean` (append)

The file has `triangulationClass.count n` sanity through `n = 12` (`208012`). Extend through `n = 15` matching catalan:
- `n = 13`: `742900`
- `n = 14`: `2674440`
- `n = 15`: `9694845`

Use the existing pattern (likely `triangulationClass_count` bridge + `decide` / `native_decide`).

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-tri-extras-reply.md.
