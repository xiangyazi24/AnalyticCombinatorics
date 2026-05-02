# Task: Generating Function Operations

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/GFOperations.lean` formalizing key operations on ordinary generating functions.

## What to formalize

From F&S Chapter I Appendix: Operations on OGFs and their combinatorial meaning.

### Required:

1. **Sequence operation (already in Sequences.lean)** — skip, just import.

2. **Pointing/marking:** If A(z) is OGF of class A, then z*A'(z) is OGF of pointed (marked) structures.
   Define `pointedCount (A : CombinatorialClass) (n : ℕ) : ℕ := n * A.count n`
   
   Verify for binary trees: pointed binary trees of size n = n * C_n.
   Check n * C_n for n=0..6: 0, 1, 4, 15, 56, 210, 792

3. **Diagonal extraction:** From bivariate GF, extract diagonal. For counting:
   Define `diagonalCount (f : ℕ → ℕ → ℕ) (n : ℕ) : ℕ := f n n`
   
4. **Hadamard product:** Coefficient-wise product of two OGFs.
   ```lean
   noncomputable def hadamardProduct (f g : PowerSeries ℕ) : PowerSeries ℕ :=
     PowerSeries.mk (fun n => coeff n f * coeff n g)
   ```

5. **Verify:** Hadamard product of geometric series 1/(1-z) with itself gives `∑ z^n` = 1/(1-z) again (since 1*1=1 for all coefficients). Actually 1/(1-z) coefficients are all 1, so Hadamard(1/(1-z), 1/(1-z)) = 1/(1-z). Verify for n=0..10.

6. **Composition/substitution:** f(g(z)) when g(0)=0. Define the coefficient formula:
   Faà di Bruno not needed — just verify that for f = 1/(1-z) and g = z/(1-z), f(g(z)) = 1/(1-2z) with coefficients 2^n. Check for n=0..10.

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Trees
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.GFOperations`
- No sorry, no axiom
- Delete anything that doesn't compile

## Output

Write file, verify build, report.
