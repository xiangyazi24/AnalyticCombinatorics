# Task: Tree OGF Equations — Part A Ch I §3

## Goal

Create file `AnalyticCombinatorics/PartA/Ch1/Trees.lean` formalizing the recursive OGF equations for tree families from F&S Chapter I §3.

## What to formalize

The key tree families satisfy functional equations:

### Binary Trees (Catalan)
- `T = ε + Z × T × T`
- OGF: `T(z) = 1 + z · T(z)²`
- Counting: T_n = C_n (Catalan numbers)

### General (Plane) Trees
- `T = Z × SEQ(T)`
- OGF: `T(z) = z / (1 - T(z))` equivalently `T(z) = z · (1 + T(z) + T(z)² + ...)`
- Counting: T_n = C_{n-1} (shifted Catalan)

### Motzkin Trees (Unary-Binary)
- `T = Z + Z × T + Z × T × T`
- OGF: `T(z) = z(1 + T(z) + T(z)²)`
- Counting: Motzkin numbers

### Required:

1. **Define `BinaryTree`** inductive type and its `CombinatorialClass` instance:
   ```lean
   inductive BinaryTree where
     | leaf : BinaryTree
     | node : BinaryTree → BinaryTree → BinaryTree
   ```
   with `size leaf = 0` and `size (node l r) = 1 + size l + size r`.

2. **Prove the functional equation at the count level:**
   ```lean
   theorem binaryTree_count_recursion (n : ℕ) :
       binaryTreeClass.count (n + 1) =
         ∑ p ∈ Finset.antidiagonal n, binaryTreeClass.count p.1 * binaryTreeClass.count p.2
   ```

3. **Prove OGF satisfies `T(z) = 1 + z · T(z)²`:**
   ```lean
   theorem binaryTree_ogf_eq :
       binaryTreeClass.ogf = 1 + X * binaryTreeClass.ogf ^ 2
   ```
   (over ℕ[[z]])

4. **Sanity checks** (using the recursive definition):
   - count 0 = 1 (leaf)
   - count 1 = 1 (node leaf leaf)
   - count 2 = 2
   - count 3 = 5
   - count 4 = 14

5. **Connection to Catalan:** State that `binaryTreeClass.count n = Nat.centralBinom n / (n + 1)` for the first few values (or prove via the known formula if tractable).

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Central
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch1.Trees` must pass
- Focus on BinaryTree. If time permits, add PlaneTree similarly.
- The `finite_level` proof needs careful induction — the key insight is that trees of size n have bounded depth and bounded structure.

## Output

Write the complete file and report theorems proved.
