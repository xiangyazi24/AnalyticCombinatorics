# Task — Fibonacci compositions example

**File:** `AnalyticCombinatorics/Examples/Fibonacci.lean` (new). Add to root.

**Goal:** Define the class of compositions of n into parts of size 1 or 2 (think domino tilings of a 1×n strip), prove its count is the Fibonacci number `Nat.fib (n+1)`.

**Depends on:** `atomOfSize` (just added in CombinatorialClass.lean).

```lean
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import Mathlib.Combinatorics.Enumerative.Composition  -- check if needed
import Mathlib.Combinatorics.Enumerative.DoubleCounting  -- maybe
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Data.Nat.Fib.Basic

open CombinatorialClass

/-- The atom class for parts of size 1 or 2. Count is 1 at sizes 1 and 2, else 0. -/
noncomputable def stepClass : CombinatorialClass :=
  (atomOfSize 1).disjSum (atomOfSize 2)

/-- stepClass has no size-0 part. -/
theorem stepClass_count_zero : stepClass.count 0 = 0 := by
  show (CombinatorialClass.disjSum (atomOfSize 1) (atomOfSize 2)).count 0 = 0
  rw [CombinatorialClass.disjSum_count, atomOfSize_count, atomOfSize_count]
  decide

/-- Compositions into parts of size 1 or 2. -/
noncomputable def fibClass : CombinatorialClass :=
  seqClass stepClass stepClass_count_zero

/-- The number of compositions of n into 1s and 2s equals fib(n+1). -/
theorem fibClass_count_eq_fib (n : ℕ) : fibClass.count n = Nat.fib (n + 1) := by
  sorry
```

## Strategy

The recurrence: `fibClass.count (n+2) = fibClass.count (n+1) + fibClass.count n`.

Combinatorial reading: a composition of n+2 either starts with a 1 (then the rest is a composition of n+1) or starts with a 2 (then the rest is a composition of n).

Proof outline:
1. Compute `stepClass.count k` formula: 1 if k = 1, 1 if k = 2, 0 else.
2. Use `seqClass.count_succ` recurrence: count (n+1) = ∑ p ∈ antidiag (n+1), stepClass.count p.1 · fibClass.count p.2. Only p.1 = 1 (gives count(n)) and p.1 = 2 (gives count(n-1)) contribute.
3. Match Mathlib's `Nat.fib_add_two : fib (n+2) = fib n + fib (n+1)` by induction.

## Hard constraints

- `lake build` green. Add to root AnalyticCombinatorics.lean imports.
- No new sorrys when delivered.
- Write reply at HANDOFF/outbox/task-fibonacci-reply.md.
