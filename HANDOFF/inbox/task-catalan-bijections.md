# Task: Catalan Family Bijections

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/CatalanBijections.lean` proving the Catalan numbers arise from multiple combinatorial classes.

## What to formalize

From F&S Chapter I: all the following have OGF satisfying C = 1 + z*C^2 (Catalan):
- Binary trees (already in Trees.lean)
- Plane trees rooted (already in PlaneTrees.lean — note different recursion T = z/(1-T))
- Dyck paths (already in LatticePaths.lean)

This file proves they all give the SAME counting sequence by native_decide verification for n=0..8.

### Required:

1. Import Trees, LatticePaths (and optionally PlaneTrees)
2. `catalan_binary_dyck : ∀ n, binaryTreeClass.count n = dyckCount n` — for n=0..8 via `decide` or `native_decide`
   
   Actually this is tricky because binaryTreeClass counts by internal nodes (so count 0 = 1 = empty tree) while dyckCount counts semilength.
   
   Better: just verify the sequence values match:
   - `binaryTree_catalan : ∀ n ≤ 8, binaryTreeClass.count n = Nat.centralBinom n / (n + 1)` via native_decide on each case

3. **Triangulation numbers = Catalan:** Define `triangCount (n : ℕ) : ℕ := Nat.centralBinom (n+1) / (n+2)` (triangulations of (n+3)-gon = C_{n+1}). Verify for n=0..6.

4. **Ballot problem:** ballotCount n = C_n. Verify.

5. State the unified theorem:
   ```lean
   theorem catalan_family_equal (n : ℕ) (hn : n ≤ 8) :
       binaryTreeClass.count n = dyckCount n := by native_decide
   ```

## Imports

```lean
import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartA.Ch1.LatticePaths
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.CatalanBijections`
- No sorry, no axiom
- Delete anything that doesn't compile
- Keep it simple: native_decide for verification, no complex bijection proofs

## Output

Write file, verify build, report.
