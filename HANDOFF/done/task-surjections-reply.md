Done.

- Added `AnalyticCombinatorics/Examples/Surjections.lean`.
- Defined `surjectionClass` as `labelSeq posIntClass posIntClass.count_zero`.
- Added `surjectionClass_count_eq_fubini`, restating the existing ordered-Bell/Fubini sum theorem.
- Added `surjectionClass_egf_mul_two_sub_exp`, restating the existing EGF identity.
- Added sanity examples for `n = 0..6` using `decide`.
- Imported the new file from `AnalyticCombinatorics.lean`.

Verification:

```text
lake build AnalyticCombinatorics
Build completed successfully (2789 jobs).
```
