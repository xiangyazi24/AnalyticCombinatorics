# Task — Bell recurrence numerical sanity

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

We have `bell_recurrence n : Nat.bell (n + 1) = ∑ k ∈ range (n+1), choose n k * bell k`. Add small numerical sanity examples checking the recurrence at specific values:

- `n = 0`: `bell 1 = choose 0 0 * bell 0 = 1`
- `n = 1`: `bell 2 = choose 1 0 * bell 0 + choose 1 1 * bell 1 = 1 + 1 = 2`
- `n = 2`: `bell 3 = choose 2 0 * bell 0 + choose 2 1 * bell 1 + choose 2 2 * bell 2 = 1 + 2 + 2 = 5`
- `n = 3`: `bell 4 = 1 + 3 + 6 + 5 = 15`
- `n = 4`: `bell 5 = 1 + 4 + 12 + 20 + 15 = 52`

These should all `decide` cleanly via `bell_recurrence`.

Add 5 examples reflecting the above.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-bell-rec-sanity-reply.md.
