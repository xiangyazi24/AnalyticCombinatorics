# Task — Surjections (Fubini) sanity beyond n=10

**File:** `AnalyticCombinatorics/Examples/Surjections.lean` (append)

The file has `surjectionClass.count n` sanity through `n = 10` (`102247563`). Extend through `n = 13`:
- `n = 11`: `1622632573`
- `n = 12`: `28091567595`
- `n = 13`: `526858348381`

Use the existing `surjectionClass_count_eq_fubini + native_decide` pattern (switch to `native_decide` from `decide` if needed).

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-surj-extras2-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Surjections.lean`.** Local instances if needed.
