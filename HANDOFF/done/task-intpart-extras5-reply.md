Blocked as executable checks; documented threshold instead.

- Target file: `AnalyticCombinatorics/Examples/IntegerPartitions.lean`
- Current executable `native_decide` threshold remains `n = 21`.
- A separate test of the next check, `n = 22`, exceeded a 60-second CPU limit.
- The requested `p_26 = 2436`, `p_27 = 3010`, `p_28 = 3718`, `p_29 = 4565`, and `p_30 = 5604` checks were appended as disabled templates using `intPartitionClass_count_eq_card` + `native_decide`, with the threshold documented.
- No new `sorry`s.
- Verification: `lake env lean AnalyticCombinatorics/Examples/IntegerPartitions.lean` passed.
