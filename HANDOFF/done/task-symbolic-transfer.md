# Task: Symbolic Method Transfer Theorems (Ch I/II unified)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/SymbolicTransfer.lean`.

## What to formalize

The symbolic method's core transfer theorems: constructions ↔ OGF operations.

1. **SEQ transfer (already in Sequences.lean — extend):**
   Create new file with collected transfer statements verified at the counting level.

2. **Disjoint union transfer verified:**
   - For any two CombinatorialClasses A, B: (A + B).count n = A.count n + B.count n
   - Already a theorem (disjSum_count), but create a "showcase" file with worked examples

3. **Product transfer verified:**
   - cartProd_count: (A × B).count n = Σ_{k=0}^{n} A.count k * B.count (n-k)
   - Verify for Atom × Atom: count n = [n=2] — via native_decide for n=0..5

4. **Powers:**
   - A^k (k-fold product): count n = k-fold convolution
   - For Atom^3: count n = [n=3]
   - For (Atom + Atom^2)^k: verify for k=2, n=0..6

5. **SEQ(Atom) = geometric:**
   - seqClass.count n = 1 for all n (already proved, cross-ref)

6. **Substitution / composition:**
   - If B has no size-0 objects, then A(B) where we replace each atom of A with a B-structure
   - Define `compose (A B : CombinatorialClass) : CombinatorialClass` (if feasible)
   - Or just verify: SEQ(Atom) has count 1, SEQ(Atom+Atom^2) has Fibonacci count

## Imports

```lean
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.SymbolicTransfer`
- No sorry, no axiom
- Delete anything that doesn't compile
- Focus on simple verifications via existing theorems + native_decide

## Output

Write file, verify build, report.
