Done.

- Added `catalan_recurrence` to `AnalyticCombinatorics/Examples/CatalanFamily.lean`.
- This checkout exposes Mathlib Catalan numbers as root-level `_root_.catalan`, not `Nat.catalan`, so the delivered theorem uses `_root_.catalan`.
- Proof uses existing Mathlib `_root_.catalan_succ`, with `Finset.sum_range` to match the explicit `Finset.range (n + 1)` statement.
- No new `sorry`s or axioms.
- Verified with `lake env lean AnalyticCombinatorics/Examples/CatalanFamily.lean` and `lake build`.
