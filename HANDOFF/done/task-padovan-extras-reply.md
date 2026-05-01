Done.

- Added Padovan count lemmas and sanity examples for n = 11..16:
  9, 12, 16, 21, 28, 37.
- Kept the existing `calc`/`rw`/`decide` style; no `native_decide` needed.
- Verified with `lake env lean AnalyticCombinatorics/Examples/Padovan.lean`.
- Verified full build with `lake build`.
