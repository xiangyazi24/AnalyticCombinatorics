# Task: Lattice Paths / Dyck Paths (v2, simplified)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/LatticePaths.lean`.

## Approach

Use the simplest possible representation. A Dyck path of semilength n is a list of n U-steps and n D-steps (total 2n steps) that never goes below 0.

```lean
inductive Step where | U | D
  deriving DecidableEq, Repr

def isDyckPath (xs : List Step) : Bool :=
  xs.foldl (fun (valid, h) s =>
    let h' := if s = .U then h + 1 else h - 1
    (valid && (h' ≥ 0), h')) (true, 0) |>.1 && 
    xs.foldl (...) |>.2 == 0
```

Actually, even simpler: just define `dyckCount (n : ℕ) : ℕ` directly as `Nat.centralBinom n / (n + 1)` (Catalan number) and verify it matches the binary tree count.

## Required:

1. `dyckCount n := Nat.centralBinom n / (n + 1)` (= Catalan)
2. `dyckCount_eq_binaryTree_count`: for n=0..6, show dyckCount n = binaryTreeClass.count n (native_decide)
3. Sanity: dyckCount 0 = 1, 1 = 1, 2 = 2, 3 = 5, 4 = 14
4. Optional: Define actual Dyck paths as `List Bool` with constraint, build a CombinatorialClass, verify counts match for small n.

If the CombinatorialClass approach fails (finite_level is hard for constrained lists), just do the counting-formula approach.

## Key constraint

**Must compile with `lake build AnalyticCombinatorics.PartA.Ch1.LatticePaths`.** Delete anything that doesn't compile.

No sorry, no axiom.

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Central
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Trees
```

## Output

Write file, verify build, report.
