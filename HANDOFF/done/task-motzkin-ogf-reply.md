Done.

- Appended `MotzTree.motzClass_ogfZ_eq` in `AnalyticCombinatorics/Examples/MotzkinTrees.lean`.
- The file uses size = number of edges, so the proved identity is
  `ogfZ motzClass = 1 + X * ogfZ motzClass + X^2 * (ogfZ motzClass)^2`.
- `ogfZ` in this repo is a root-level function from `PartA.Ch1.Sequences`, not a `CombinatorialClass` namespace member, so the Lean statement uses `ogfZ motzClass` rather than `motzClass.ogfZ`.
- No new `sorry` or `axiom`.

Verification:

```text
lake env lean AnalyticCombinatorics/Examples/MotzkinTrees.lean
lake build
```

Both passed.
