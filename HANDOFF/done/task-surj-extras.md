# Task — Surjections (Fubini) count sanity beyond n=6

**File:** `AnalyticCombinatorics/Examples/Surjections.lean` (append)

The file has `surjectionClass.count n` sanity through `n = 6` (`4683`). Extend through `n = 10` matching the ordered-Bell / Fubini values:
- `n = 7`: `47293`
- `n = 8`: `545835`
- `n = 9`: `7087261`
- `n = 10`: `102247563`

Use the same `surjectionClass_count_eq_fubini + decide / native_decide` pattern.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-surj-extras-reply.md.
- If `decide` is too slow at `n=10`, switch to `native_decide`.
