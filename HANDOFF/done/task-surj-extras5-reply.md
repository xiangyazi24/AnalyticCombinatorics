Done.

- Extended `AnalyticCombinatorics/Examples/Surjections.lean` sanity checks through `n = 20`.
- Used the existing `rw [surjectionClass_count_eq_fubini]` + `native_decide` pattern.
- No new `sorry`s.
- Verified with `lake env lean AnalyticCombinatorics/Examples/Surjections.lean`.
- Verified with `lake build`.

Note: the prompt's listed values for `a(18)`, `a(19)`, and `a(20)` are not the ordered Bell/Fubini values for the existing theorem `∑ k, k! * S(n,k)`. Lean rejected them as false. The passing values are:

- `a(18) = 3385534663256845323`
- `a(19) = 92801587319328411133`
- `a(20) = 2677687796244384203115`
