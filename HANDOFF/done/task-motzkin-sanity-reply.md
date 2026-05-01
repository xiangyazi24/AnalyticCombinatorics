Done.

Changed `AnalyticCombinatorics/Examples/MotzkinTrees.lean`:

- Added private count lemmas through size 8 using the existing edge-size convention.
- Added explicit `decide` sanity checks for:
  - `count 7 = 127`
  - `count 8 = 323`
  - `count 7 + count 6 = 178`
  - `count 8 = count 7 + 196`

Note: the file defines `MotzTree.size` as number of edges, with `leaf` at size 0. Under that convention the sequence continues `... 51, 127, 323`; the `132` value in the prompt does not match the existing recurrence/convention.

Verified:

```text
lake env lean AnalyticCombinatorics/Examples/MotzkinTrees.lean
lake build
```

Both passed.
