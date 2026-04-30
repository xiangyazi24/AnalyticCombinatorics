done

Implemented `permClass_egf_mul_one_sub_X` in `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean`.

Diff summary:

- Added `Mathlib.RingTheory.PowerSeries.WellKnown` for `PowerSeries.mk_one_mul_one_sub_eq_one`.
- Added `permClass_egf_eq_mk_one`, proving `permClass.egf` is `PowerSeries.mk (fun _ => 1)` from `permClass_egf_coeff`.
- Proved `permClass_egf_mul_one_sub_X` by rewriting to Mathlib's geometric-series theorem.

Verification:

```bash
PATH="/Users/huangx/.elan/bin:$PATH" lake env lean AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean
PATH="/Users/huangx/.elan/bin:$PATH" lake build
```

`lake build` completed successfully: 2764 jobs, 0 errors.

Codex: idle — task done
