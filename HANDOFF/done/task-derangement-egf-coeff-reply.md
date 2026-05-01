Done.

- Appended the direct EGF coefficient example for `derangementClass`.
- Used the existing bridge `derangementClass_count_eq_numDerangements`.
- No new `sorry`.

Verification:

```bash
lake env lean AnalyticCombinatorics/Examples/Derangements.lean
lake build
```

Both passed. `lake build` still reports existing linter warnings in other files.
