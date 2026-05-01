# Task — cyclicPermutationCount sanity beyond what's there

**File:** `AnalyticCombinatorics/Examples/CyclicPermutations.lean` (append)

The file establishes that on `[n]` with `n ≥ 1`, the number of cyclic permutations is `(n-1)!`, with sanity n=1..8 verified. Push the table further: add explicit `decide`/`native_decide` sanity for `n = 9, 10, 11, 12` matching `(n-1)!` (`40320, 362880, 3628800, 39916800`).

Use the same identification lemma the existing examples use (read the file first to find its name).

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-cyc-extras-reply.md.
- If `decide` is too slow at `n=11` or `n=12`, switch to `native_decide`.
