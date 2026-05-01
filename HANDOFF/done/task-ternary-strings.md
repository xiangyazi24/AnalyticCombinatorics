# Task — Strings over a 3-letter alphabet

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

The file currently builds `boolClass` (2-letter alphabet) and the corresponding `stringClass` of length-n binary strings (counted by `2^n`). Add the analogous **ternary** version:

1. A class `ternaryClass` whose objects are `Fin 3` (3 atoms of size 1, like `boolClass` was 2 atoms).
2. The associated `ternaryStringClass = seqClass ternaryClass` (with `count 0 = 0` hypothesis discharged the same way `boolClass` was).
3. `ternaryStringClass.count n = 3 ^ n` proved by reusing the same pattern as `stringClass_count_eq_pow`.
4. Sanity examples for `n = 0..6`: `1, 3, 9, 27, 81, 243, 729`.

Read `boolClass` setup first to copy the bridge instances (`Fintype`, `DecidableEq`, etc.).

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-ternary-strings-reply.md.
- Don't refactor `boolClass`; add ternary as new defs alongside.
