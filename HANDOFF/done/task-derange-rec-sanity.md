# Task — Derangement recurrence numerical sanity

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append)

We have `numDerangements_recurrence n : Nat.numDerangements (n+2) = (n+1) * (Nat.numDerangements (n+1) + Nat.numDerangements n)`. Add small numerical sanity examples checking the recurrence at specific values:

- `n = 0`: `D_2 = 1 * (D_1 + D_0) = 1 * (0 + 1) = 1`
- `n = 1`: `D_3 = 2 * (D_2 + D_1) = 2 * (1 + 0) = 2`
- `n = 2`: `D_4 = 3 * (D_3 + D_2) = 3 * (2 + 1) = 9`
- `n = 3`: `D_5 = 4 * (D_4 + D_3) = 4 * (9 + 2) = 44`
- `n = 4`: `D_6 = 5 * (D_5 + D_4) = 5 * (44 + 9) = 265`

Add 5 examples reflecting the above.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-derange-rec-sanity-reply.md.
