# Task — Compositions into even parts

**File:** `AnalyticCombinatorics/Examples/CompositionsEven.lean` (NEW)

A composition of `n` whose parts are all **even positive integers** has count:
- `n = 0` → `1` (empty composition)
- `n` odd → `0`
- `n = 2k` for `k ≥ 1` → `2^(k-1)` (compositions of `k` into positive parts, since each even part `2j` corresponds to a positive part `j`).

Sequence: `1, 0, 1, 0, 2, 0, 4, 0, 8, 0, 16` for `n = 0..10`.

## What to build

1. `evenPartClass : CombinatorialClass` with objects `{n : ℕ // n.Even ∧ 0 < n}` (or `{n : ℕ // n % 2 = 0 ∧ 0 < n}`) and size = the natural number itself.
2. `evenCompClass = seqClass evenPartClass h0` with `h0 : evenPartClass.count 0 = 0`.
3. Sanity examples for `n = 0..10` matching `1, 0, 1, 0, 2, 0, 4, 0, 8, 0, 16`. Use `decide` / `native_decide`.
4. Add to `AnalyticCombinatorics.lean` import list.

## Hard constraints

- Build green.
- No new sorrys.
- Read `Examples/CompositionsOdd.lean` first to copy the subtype-based pattern.
- Reply at HANDOFF/outbox/task-even-comp-reply.md.
- If the subtype + Fintype dance gets awkward, fall back to ship just sanity through `n = 6` and document.
