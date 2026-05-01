Done.

- Read `AnalyticCombinatorics/Examples/SchroderTrees.lean`; the convention is `largeSchroderNumber n` with `a_0 = 1`, so the next two after `n = 5` are `n = 6` and `n = 7`.
- Added sanity examples:
  - `largeSchroderNumber 6 = 1806`
  - `largeSchroderNumber 7 = 8558`
- Kept `decide`; no need for `native_decide`.

Verification:

- `/usr/bin/time -p lake env lean AnalyticCombinatorics/Examples/SchroderTrees.lean`
  - `real 2.67`
- `/usr/bin/time -p lake build AnalyticCombinatorics.Examples.SchroderTrees`
  - `real 2.82`
- `/usr/bin/time -p lake build`
  - `real 3.49`

No new `sorry`s.
