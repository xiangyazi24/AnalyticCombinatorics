# Task — cyclic permutation class

**File:** `AnalyticCombinatorics/Examples/CyclicPermutations.lean` (new). Add to root.

**Goal:** Define the class of "n-cycles" — single-cycle permutations of `Fin n` for n ≥ 1. The count of n-cycles is `(n-1)!`. EGF identity: this equals `labelCycCount Atom n` (already proven). Connect them.

```lean
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
import Mathlib.GroupTheory.Perm.Cycle.Basic

open CombinatorialClass

/-- A cyclic permutation of size n is a fixed-point-free permutation that consists of
    a single cycle of length n. (Empty permutation of Fin 0 vacuously qualifies.) -/
-- For n ≥ 1, count = (n-1)!.
-- For n = 0, count is vacuous; convention: 0 cycles ↔ the empty permutation.

/-- Cardinality bridge: `labelCycCount Atom (n+1) = ((n+1)-1)!` (already proven). -/
example (n : ℕ) : labelCycCount Atom (n + 1) = (n.factorial : ℚ) :=
  labelCycCount_Atom_succ n

/-- Sanity: 1-cycles, 2-cycles, 3-cycles, 4-cycles, 5-cycles. -/
example : labelCycCount Atom 1 = 1 := labelCycCount_Atom_succ 0  -- (0)! = 1
example : labelCycCount Atom 2 = 1 := labelCycCount_Atom_succ 1  -- (1)! = 1
example : labelCycCount Atom 3 = 2 := labelCycCount_Atom_succ 2  -- (2)! = 2
example : labelCycCount Atom 4 = 6 := labelCycCount_Atom_succ 3  -- (3)! = 6
example : labelCycCount Atom 5 = 24 := labelCycCount_Atom_succ 4  -- (4)! = 24
```

If the existing `labelCycCount_Atom_succ` is enough to close those, no new theorem is needed — just sanity examples. Otherwise add small helper lemmas as needed.

## Hard constraints

- Build green
- No new sorrys
- Add new file to AnalyticCombinatorics.lean root imports if you create one (or just append to existing if simpler)
- Reply at HANDOFF/outbox/task-cyclic-perm-reply.md
