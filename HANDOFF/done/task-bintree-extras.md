# Task — BinTree count sanity beyond what's done

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append)

The file has `BinTree.asClass.count n` sanity for `n = 0..8`. Push further: add `n = 9..14` matching Catalan numbers via the existing `BinTree.asClass.count = Nat.catalan` (or `_root_.catalan`) bridge.

Catalan values: `C_0..C_14 = 1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900, 2674440`.

Use the same tactic the existing examples use. Switch to `native_decide` if `decide` is slow.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-bintree-extras-reply.md.
