# Task — Quaternary string sum identity

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

`quatStringClass.count_eq_pow` gives `count n = 4^n`. Add small extension sanity:

- `quatStringClass.count 7 = 16384`
- `quatStringClass.count 8 = 65536`
- `quatStringClass.count 9 = 262144`
- `quatStringClass.count 10 = 1048576`

Add 4 sanity examples mirroring the existing `n = 0..6` pattern.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-quat-pascal-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Strings.lean`.** Local instances if needed.
