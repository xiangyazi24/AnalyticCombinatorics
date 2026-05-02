# Task: Moment Generating Functions (Ch3 extension)

## Goal

Extend `AnalyticCombinatorics/PartA/Ch3/Parameters.lean` with moment/probability generating function content, OR create a new file `AnalyticCombinatorics/PartA/Ch3/Moments.lean`.

## What to formalize

From F&S Chapter III: Parameters on combinatorial structures give rise to bivariate GFs. Key results:
- Mean = [z^n] ∂_u F(z,1) / [z^n] F(z,1)  
- Variance via second derivative

### Required (create `Moments.lean`):

1. Define `varianceParam` analogous to `meanParam` in Parameters.lean:
   ```lean
   noncomputable def varianceParam (A : CombinatorialClass) (cost : A.Obj → ℕ)
       (n : ℕ) : ℚ := ...
   ```
   (second moment minus mean squared, over count)

2. **Concrete example: binary tree height.** Not easy to formalize height as parameter, so instead:

   **Number of leaves in binary trees:**
   ```lean
   def binaryTreeLeaves : BinaryTree → ℕ
     | .leaf => 1
     | .node l r => binaryTreeLeaves l + binaryTreeLeaves r
   ```
   
   Verify for small n: total leaves across all binary trees of size n.
   - n=1: 1 tree (node leaf leaf), 2 leaves. Total = 2.
   - n=2: 2 trees, total leaves = 2+2+2+2 = hmm, let me recalculate.
   
   Actually simpler: just define the cost function and verify `cumulatedCost` for n=0..4 via native_decide.

3. **Path length in binary trees:**
   ```lean
   def binaryTreePathLength : BinaryTree → ℕ
     | .leaf => 0
     | .node l r => binaryTreePathLength l + binaryTreePathLength r + binaryTreeLeaves l + binaryTreeLeaves r
   ```
   This is the total internal path length. Verify cumulated cost for n=0..4.

4. Verify that average path length / n → 2√(πn) is consistent with growth (just check ratios for n=1..6 are increasing, via native_decide on numerics).

If the rational arithmetic is too hard, just do the integer cumulated costs.

## Imports

```lean
import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartA.Ch3.Parameters
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch3.Moments`
- No sorry, no axiom
- Delete anything that doesn't compile
- Prefer native_decide for any numerical verification
- If Parameters.lean doesn't export what you need, just define locally

## Output

Write file, verify build, report.
