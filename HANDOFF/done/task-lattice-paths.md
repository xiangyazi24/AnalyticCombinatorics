# Task: Lattice Paths — Part A Ch I §3

## Goal

Create file `AnalyticCombinatorics/PartA/Ch1/LatticePaths.lean` formalizing lattice path enumeration.

## What to formalize

Dyck paths (steps U=(1,1) and D=(1,-1), never going below x-axis) are counted by Catalan numbers. They have the same symbolic equation as binary trees: `D = ε + U·D·D·D` ... no, the correct one is:

**Dyck paths:** A Dyck path of semilength n is a path from (0,0) to (2n,0) with steps (+1,+1) and (+1,-1), never dipping below the x-axis.
- Count(n) = Catalan(n) = C(2n,n)/(n+1)

Symbolic decomposition: `D = ε + U·D·D·D` ... actually the first-return decomposition gives:
- `D = ε | U·D·D·…` — no. The correct one is:
- **D = ε + U·D·D** (first-return: up, walk until return, remaining walk) → same as binary tree!

### Required:

1. **`DyckPath` type** — list of steps (U/D) with Dyck constraint:
   ```lean
   inductive Step where | U | D
   def isDyckPath (xs : List Step) : Prop := ...
   ```
   Or simpler: represent as `List Bool` (true=U, false=D) with prefix-sum ≥ 0 and total sum = 0.

2. **`dyckPathClass : CombinatorialClass`** where size = semilength (half the path length).

3. **Count theorem** connecting to Catalan:
   ```lean
   theorem dyckPath_count_eq_catalan (n : ℕ) :
       dyckPathClass.count n = Nat.centralBinom n / (n + 1)
   ```
   Or at least verify for small n.

4. **Bijection to binary trees** (at the counting level):
   ```lean
   theorem dyckPath_count_eq_binaryTree (n : ℕ) :
       dyckPathClass.count n = binaryTreeClass.count n
   ```

5. **Sanity checks:**
   - count 0 = 1 (empty path)
   - count 1 = 1 (UD)
   - count 2 = 2 (UUDD, UDUD)
   - count 3 = 5
   - count 4 = 14

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Trees
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch1.LatticePaths` must pass
- If proving the full bijection is too hard, just verify count equality for n=0..4 with native_decide and state the general theorem.

## Output

Write the file and report.
