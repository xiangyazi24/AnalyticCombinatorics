Done.

Changed `AnalyticCombinatorics/Examples/SchroderTrees.lean` by appending sanity examples through `k = 21`.

Note: the requested `S(19)=3236724317468` does not match `largeSchroderNumber 19`; Lean's `decide` proves that equality false. The existing recurrence computes

```lean
largeSchroderNumber 19 = 3236724317174
```

so the file uses `3236724317174` for `k = 19`. The requested `k = 20` and `k = 21` values pass unchanged.

Verification:

```text
lake env lean AnalyticCombinatorics/Examples/SchroderTrees.lean
lake build
```

Both completed successfully. No new `sorry`s or axioms.
