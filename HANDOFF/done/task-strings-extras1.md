# Task — Strings sanity extension

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

The file has various string counting sanity checks. The binary/ternary/quaternary string classes have `count n` checks. Extend sanity checks for the main string classes through higher n values (e.g. n=13..15 or as high as feasible).

Binary strings: count n = 2^n. Ternary: 3^n. Quaternary: 4^n.

Use the same proof patterns already in the file. If checks use `decide` or `native_decide`, continue that pattern.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-strings-extras1-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/Strings.lean`.** Local instances if needed.
