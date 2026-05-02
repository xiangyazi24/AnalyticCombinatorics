# Task: Functional Equations for OGFs

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/FunctionalEquations.lean` collecting the key functional equations satisfied by combinatorial OGFs.

## What to formalize

From F&S Chapter I/II: Combinatorial classes satisfy functional equations that characterize their OGFs.

### Required:

1. **Collection of functional equations verified coefficientwise:**
   For each, define the sequence and verify the functional equation holds at the power series level for coefficients 0..10 (or wherever native_decide is fast).

   a. Binary trees: C = 1 + z*C² (already in Trees.lean, just re-export/reference)
   
   b. Motzkin: M = 1 + z*M + z²*M² (wait, Motzkin-by-edges uses M = z + z*M + z*M², already have)
   
   c. **Ordered trees (general plane trees):** T = z/(1-T) ↔ T = z + T² + T³ + ...
      Already have: T(1-T) = z in PlaneTrees.lean.
   
   d. **2-regular graphs / set partitions:** B(n) = sum C(n-1,k-1) * B(n-k)
      Already have in BellNumbers.lean.
   
   e. **NEW: Ternary trees:** T = 1 + z*T³
      Define `ternaryTreeCount : ℕ → ℕ` satisfying this recursion.
      Count: 1, 1, 3, 12, 55, 273, 1428, ...
      Verify for n=0..6.

   f. **NEW: Non-crossing partitions:** NC(n) = Catalan(n).
      Just verify `catalanNumber n = nonCrossingPartCount n` for n=0..8.
      (NC count equals Catalan — this is a theorem.)

2. **Lagrange inversion preview:** State that if T = z*φ(T), then
   [z^n]T = (1/n) * [w^{n-1}] φ(w)^n.
   Don't prove — just verify for φ(w) = 1 + w (Catalan) that (1/n)*C(2n-2,n-1) = C_n for n=1..8.
   In ℕ: verify `n * catalanNumber n = Nat.choose (2*n - 2) (n - 1)` wouldn't work cleanly.
   Better: `(n+1) * catalanNumber n = Nat.choose (2*n) n` — this is the standard identity.
   Verify for n=0..10 via native_decide.

## Imports

```lean
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartA.Ch1.LatticePaths
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.FunctionalEquations`
- No sorry, no axiom
- Delete anything that doesn't compile

## Output

Write file, verify build, report.
