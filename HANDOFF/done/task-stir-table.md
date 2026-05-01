# Task — Stirling 2nd kind small triangle sanity

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append)

The file has scattered Stirling 2nd kind sanity. Add the **complete row** at `n = 6` so we have a clean small table:

```lean
example : Nat.stirlingSecond 6 0 = 0 := by decide
example : Nat.stirlingSecond 6 1 = 1 := by decide
example : Nat.stirlingSecond 6 2 = 31 := by decide
example : Nat.stirlingSecond 6 3 = 90 := by decide
example : Nat.stirlingSecond 6 4 = 65 := by decide
example : Nat.stirlingSecond 6 5 = 15 := by decide
example : Nat.stirlingSecond 6 6 = 1 := by decide
```

Sum should equal `B_6 = 203`. Add a sanity `example` that the sum equals the Bell number:

```lean
example : ∑ k ∈ Finset.range 7, Nat.stirlingSecond 6 k = 203 := by decide
```

(Or use `native_decide` if needed.)

Also add the analogous unsigned Stirling 1st row at `n = 6`:
- `c(6, 0) = 0`
- `c(6, 1) = 120`  (= 5!)
- `c(6, 2) = 274`
- `c(6, 3) = 225`
- `c(6, 4) = 85`
- `c(6, 5) = 15`
- `c(6, 6) = 1`

Sum should equal `6! = 720`.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-stir-table-reply.md.
