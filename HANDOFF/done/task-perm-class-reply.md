done

Implemented `permClass` in `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean`:

- Added `Mathlib.Data.Fintype.Perm`.
- Defined objects as `Σ n : ℕ, Equiv.Perm (Fin n)` with size `Sigma.fst`.
- Proved finite levels by embedding the level into permutations of `Fin n`.
- Proved `permClass.count n = n.factorial` via `Finset.card_bij'` between `permClass.level n` and `Finset.univ : Finset (Equiv.Perm (Fin n))`, avoiding a global `DecidableEq` instance for the sigma type.
- Added wrapper theorem `permClass_count_eq_factorial`.
- Stabilized `labelProdCount_Epsilon` after the new import changed simplification enough to expose a stuck `*_mul_zero` rewrite.

Verification:

```bash
PATH="/Users/huangx/.elan/bin:$PATH" lake env lean AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean
PATH="/Users/huangx/.elan/bin:$PATH" lake build
```

`lake build` completed successfully: 2763 jobs, 0 errors.

Codex: idle — task done
