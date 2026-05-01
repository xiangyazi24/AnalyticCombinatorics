Done.

- Appended both closed-form theorems to `AnalyticCombinatorics/Examples/CompositionsEven.lean`.
- Proved the even case via an explicit halving/doubling bijection with `compositionClass`, then used `compositionClass_count_succ`.
- Proved the odd case by showing any sequence of even parts has even total size.
- No new `sorry`s or axioms.
- Verified with `lake env lean AnalyticCombinatorics/Examples/CompositionsEven.lean` and `lake build`.
