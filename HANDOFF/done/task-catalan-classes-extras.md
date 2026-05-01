# Task — Extend sanity for Catalan-counted classes

Three small appendings, all pushing existing sanity tables further. By analogy with BinaryTrees just landed (`BinTree.asClass.count 9..14`), extend:

## File 1: `AnalyticCombinatorics/Examples/PlaneTrees.lean`

Add `planeTreeClass.count n` sanity for `n = 9..12` matching catalan numbers `4862, 16796, 58786, 208012`.

## File 2: `AnalyticCombinatorics/Examples/Triangulations.lean`

Add `triangulationClass.count n` sanity for `n = 9..12` matching the same values.

## File 3: `AnalyticCombinatorics/Examples/DyckPaths.lean`

Add `dyckPathClass.count n` sanity for `n = 6..10` matching `132, 429, 1430, 4862, 16796`.

For each file, use the same tactic the existing examples use (likely `decide` after rewriting via the `count = catalan` bridge). Switch to `native_decide` if `decide` is slow.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-catalan-classes-extras-reply.md.
- Do all three files in this single dispatch.
