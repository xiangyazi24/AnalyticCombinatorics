# Task: Motzkin Trees and Unary-Binary Trees — Part A Ch I

## Goal

Create file `AnalyticCombinatorics/PartA/Ch1/MotzkinTrees.lean` formalizing Motzkin trees.

## What to formalize

Motzkin trees (unary-binary trees): each node has 0, 1, or 2 children.
- `T = Z + Z×T + Z×T×T` → `T(z) = z(1 + T + T²)`

### Required:

1. **`MotzkinTree` inductive type:**
   ```lean
   inductive MotzkinTree where
     | leaf : MotzkinTree
     | unary : MotzkinTree → MotzkinTree
     | binary : MotzkinTree → MotzkinTree → MotzkinTree
   ```
   Size: leaf = 1, unary t = 1 + size t, binary l r = 1 + size l + size r.

2. **`motzkinTreeClass : CombinatorialClass`**

3. **OGF equation:**
   ```lean
   theorem motzkinTree_ogf_eq :
       motzkinTreeClass.ogf = X * (1 + motzkinTreeClass.ogf + motzkinTreeClass.ogf ^ 2)
   ```

4. **Sanity (Motzkin numbers):**
   - count 1 = 1 (leaf)
   - count 2 = 1 (unary leaf)
   - count 3 = 2 (binary leaf leaf, unary(unary leaf))
   - count 4 = 4
   - count 5 = 9

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch1.MotzkinTrees` must pass

## Output

Write the file and report.
