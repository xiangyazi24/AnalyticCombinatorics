done

Diff summary:
- Added object-level `CombinatorialClass.labelProd`.
- Encoded level `(k,m)` fibers as `A.level k × B.level m × powersetCard k (Fin (k+m))`.
- Proved `labelProd_count_eq_labelProdCount`.
- Added `labelProd_egf` as the direct EGF corollary.

Verification:
- `lake build` passes: 2764 jobs, 0 errors.

Codex: idle — task done
