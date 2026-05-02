Blocked by `native_decide` performance.

What changed:
- Appended the requested p(31), p(32), p(33) sanity checks to
  `AnalyticCombinatorics/Examples/IntegerPartitions.lean`, but kept them
  commented out.
- Documented that they are not enabled because the same proof shape already
  times out at the existing `n = 22` threshold for Mathlib's current
  `Nat.Partition` `Fintype`.

Verification:
- `lake build AnalyticCombinatorics.Examples.IntegerPartitions` was attempted
  with a 15-minute alarm and produced no output before being terminated by the
  alarm.
- No new `sorry`s were added.
