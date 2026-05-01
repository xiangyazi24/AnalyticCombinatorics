# Task — Connect labelled SET to Bell numbers

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` is wrong place; create new `AnalyticCombinatorics/Examples/SetPartitions.lean` and add to `AnalyticCombinatorics.lean` import list.

**Goal:** Prove that the labelled-SET count of `posIntClass` (positive integers, the class with `count k = 1` for k ≥ 1, `count 0 = 0`) equals the n-th Bell number.

This is F&S's iconic example of the labelled SET construction giving combinatorial Bell numbers, and connects our framework to Mathlib's `Nat.bell`.

## Required code

```lean
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
import AnalyticCombinatorics.Examples.Compositions  -- for posIntClass
import Mathlib.Combinatorics.Enumerative.Bell

open CombinatorialClass

/-- The labelled SET count of `posIntClass` at size n equals the n-th Bell number. -/
theorem labelSetCount_posIntClass_eq_bell (n : ℕ) :
    labelSetCount posIntClass n = (Nat.bell n : ℚ) := by
  sorry
```

## Strategy: induction on n via the Bell recurrence

Mathlib provides:
- `Nat.bell_zero : Nat.bell 0 = 1`
- `Nat.bell_succ' : Nat.bell (n+1) = ∑ ij ∈ antidiagonal n, n.choose ij.1 * Nat.bell ij.2`

Need to show `labelSetCount posIntClass` satisfies the same recurrence.

### Combinatorial intuition

For a labelled SET of size n+1 over posIntClass:
- Element 0 (or any chosen element) lies in some block of size m+1 (for 1 ≤ m+1 ≤ n+1).
- Choose the m other elements of that block: `n.choose m` ways.
- The remaining n-m elements form a labelled SET of size n-m: `labelSetCount posIntClass (n-m)` ways.

So `labelSetCount posIntClass (n+1) = ∑_{m=0}^{n} n.choose m · labelSetCount posIntClass (n-m)`.

This is exactly Bell's recurrence with the variable substituted.

## Required intermediate

You'll likely need:
```lean
theorem labelSetCount_posIntClass_succ (n : ℕ) :
    labelSetCount posIntClass (n + 1) =
      ∑ ij ∈ Finset.antidiagonal n, n.choose ij.1 * labelSetCount posIntClass ij.2
```

This intermediate could come from manipulating the inner sum in the definition of `labelSetCount` plus the `posIntClass` count formula (`posIntClass.count k = 1` for k ≥ 1).

The technical core: relate `(labelPow posIntClass k).count (n+1)` to a recurrence.

## Hard constraints

- `lake build` green; current 2764 jobs.
- No new sorrys when delivered.
- Two real attempts; if blocked file `HANDOFF/outbox/task-bell-numbers-reply.md` documenting where the recurrence breaks.
- New file `Examples/SetPartitions.lean` with appropriate imports; must be added to root `AnalyticCombinatorics.lean`.

## Reply format

`HANDOFF/outbox/task-bell-numbers-reply.md` with diff summary + `Codex: idle — task done`.
