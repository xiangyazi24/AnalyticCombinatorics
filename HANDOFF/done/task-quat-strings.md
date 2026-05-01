# Task — Quaternary strings (4-letter alphabet)

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

The file has `boolClass` (2 atoms) and `ternaryClass` (3 atoms). Add the analogous **4-letter** version:

1. `quatClass : CombinatorialClass` with objects `Fin 4`, all atoms of size 1.
2. Bridge instances (`Fintype`, `DecidableEq`).
3. `quatStringClass = seqClass quatClass _` with the appropriate `count 0 = 0` hypothesis.
4. `quatStringClass_count_eq_pow (n) : quatStringClass.count n = 4 ^ n` proved by mirroring the existing `stringClass_count_eq_pow` / `ternaryStringClass_count_eq_pow`.
5. Sanity examples for `n = 0..6`: `1, 4, 16, 64, 256, 1024, 4096`.

## Hard constraints

- Build green.
- No new sorrys.
- Read `ternaryClass` setup first to copy bridge-instance pattern.
- Reply at HANDOFF/outbox/task-quat-strings-reply.md.
- Don't refactor the existing string defs.
