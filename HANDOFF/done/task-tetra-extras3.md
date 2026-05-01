# Task — Tetranacci count sanity beyond n=18

**File:** `AnalyticCombinatorics/Examples/Tetranacci.lean` (append)

The file has `tetraClass.count n` sanity through `n = 18` (`76424`). Extend through `n = 22`:
- `count 19 = 147312`
- `count 20 = 283953`
- `count 21 = 547337`
- `count 22 = 1055026`

Use the existing pattern. Switch to `native_decide` if needed.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-tetra-extras3-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Tetranacci.lean`.** Local instances if needed.
