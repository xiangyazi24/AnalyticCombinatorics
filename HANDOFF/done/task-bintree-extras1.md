# Task — BinaryTree count sanity beyond n=18

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append)

The file has `BinTree.asClass.count n` sanity through `n = 18` (matching Catalan numbers C_n). Extend through `n = 21`.

Catalan: C_19 = 1767263190, C_20 = 6564120420, C_21 = 24466267020.

Match the existing tactic for n=18: rewrite via `BinTree.catalan` and close with `decide` / `native_decide`. If decide unfolding is slow, follow DyckPaths.lean which rewrites via `_root_.catalan_eq_centralBinom_div` before `native_decide`.

If elaboration blows up at some n=k, document the threshold and stop there.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-bintree-extras1-reply.md.
- **ONLY modify `AnalyticCombinatorics/Examples/BinaryTrees.lean`.** Local instances if needed.
