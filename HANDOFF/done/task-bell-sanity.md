# Task — Bell number sanity beyond what's already done

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

The file already verifies Bell `B_0..B_11`. Push the table further: add explicit `decide`/`native_decide` sanity examples for `B_12 = 4213597`, `B_13 = 27644437`, `B_14 = 190899322`, `B_15 = 1382958545`, going through whatever lemma already bridges to `Nat.bell` (look for `bell` identifications already proved in the file — likely `labelSetCount_posIntClass_eq_bell` or similar).

Switch to `native_decide` if `decide` is slow at `B_14` / `B_15`.

If both routes blow up at `n = 14` or beyond, **document the threshold** in the reply (which `n` works in <30s, which doesn't) — this is useful baseline data for future kernel/decide work.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-bell-sanity-reply.md.
