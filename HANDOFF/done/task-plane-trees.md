# Task: Plane Trees (General/Ordered Trees) — Part A Ch I

## Goal

Create file `AnalyticCombinatorics/PartA/Ch1/PlaneTrees.lean` formalizing plane (ordered) trees and their OGF equation.

## What to formalize

A plane tree is a rooted tree where children are ordered. The symbolic equation is:
- `T = Z × SEQ(T)` (a root node followed by a sequence of subtrees)

This gives the OGF functional equation:
- `T(z) = z / (1 - T(z))`, equivalently `T(z)(1 - T(z)) = z · (1 - T(z)) + z · T(z) = z`
- Actually: `T(z) = z · (1 + T(z) + T(z)² + ...)` = `z / (1 - T(z))`

Counting: plane trees of size n = Catalan number C_{n-1} (shifted by 1 from binary trees).

### Required:

1. **`PlaneTree` inductive type:**
   ```lean
   inductive PlaneTree where
     | node : List PlaneTree → PlaneTree
   ```
   with `size (node children) = 1 + sum of children sizes`.

2. **`planeTreeClass : CombinatorialClass`** with finite_level proof.

3. **Count recursion:**
   ```lean
   theorem planeTree_count_recursion (n : ℕ) :
       planeTreeClass.count (n + 1) =
         ∑ p ∈ Finset.antidiagonal n, (seqClass planeTreeClass _).count p.1 ... -- or equivalent
   ```

   Simpler: prove the convolution identity relating plane tree counts to itself.

4. **OGF equation** (the key result):
   ```lean
   theorem planeTree_ogf_eq :
       (1 - planeTreeClass.ogf) * planeTreeClass.ogf = X * (1 - planeTreeClass.ogf)
   ```
   or equivalently over ℤ[[z]]:
   ```lean
   theorem planeTree_ogf_func_eq :
       planeTreeClass.ogf = X + X * planeTreeClass.ogf + X * planeTreeClass.ogf ^ 2 + ...
   ```

   Actually the cleanest form: since T = z·SEQ(T) and SEQ has OGF 1/(1-·):
   ```lean
   theorem planeTree_ogf_satisfies :
       planeTreeClass.ogf = PowerSeries.X * seqOGF planeTreeClass.ogf
   ```
   where seqOGF f = 1/(1-f) in the ℤ[[z]] sense.

   **Simplest provable form:**
   ```lean
   theorem planeTree_ogf_eq :
       planeTreeClass.ogf = PowerSeries.X * (1 + planeTreeClass.ogf + planeTreeClass.ogf ^ 2 + ...)
   ```
   or at the count level: `count(n+1) = ∑_{k=0}^{n} (seqClass ...).count k * ...`

5. **Sanity checks** (plane trees of size n = C_{n-1} for n≥1):
   - count 1 = 1 (single node, no children)
   - count 2 = 1 (root with one child)
   - count 3 = 2
   - count 4 = 5
   - count 5 = 14

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch1.PlaneTrees` must pass
- The `finite_level` proof is the hardest part. Key insight: trees of size ≤ n have at most n nodes, each node has children drawn from trees of size < n. Use well-founded recursion.

## Output

Write the complete file and report theorems proved.
