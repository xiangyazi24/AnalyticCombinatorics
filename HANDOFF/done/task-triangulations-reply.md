Done.

- Added `AnalyticCombinatorics/Examples/Triangulations.lean`.
- Added `import AnalyticCombinatorics.Examples.Triangulations` to `AnalyticCombinatorics.lean`.
- Proved `triangulationClass_count` by reducing to `BinTree.catalan_eq_nat_catalan`.
- No new `sorry`/`admit` in the touched files.
- `lake build` passes.

Note: this Mathlib version exposes Catalan numbers as root-level `catalan`, not `Nat.catalan`, so the theorem statement uses `_root_.catalan n`.
