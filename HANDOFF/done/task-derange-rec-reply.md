# Task — Derangement recurrence reply

- Appended `numDerangements_recurrence` to `AnalyticCombinatorics/Examples/Derangements.lean`.
- Mathlib already exposes the recurrence as top-level `numDerangements_add_two`; the new theorem wraps it in the local `Nat.numDerangements` bridge and swaps the summands.
- No new `sorry`s or axioms.

Verification:

```bash
lake env lean AnalyticCombinatorics/Examples/Derangements.lean
lake build
```
