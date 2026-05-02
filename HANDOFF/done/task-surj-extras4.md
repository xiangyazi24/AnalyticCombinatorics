# Task — Surjections sanity beyond n=15

**File:** `AnalyticCombinatorics/Examples/Surjections.lean` (append)

The file has `surjectionClass.count n` sanity through `n = 15`. Extend through `n = 17`:
- `n = 16`: `5315654681981355`
- `n = 17`: `130370767029135901`

Use `surjectionClass_count_eq_fubini + native_decide`.

If `native_decide` blows up, document the threshold.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-surj-extras4-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Surjections.lean`.** Local instances if needed.
