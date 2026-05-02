# Task: General Tree Families (Ch I §5)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/GeneralTrees.lean`.

## What to formalize

From F&S Chapter I: various tree families defined by degree constraints.

1. **Unary-binary trees** (= Motzkin trees, already done — skip)

2. **t-ary trees**: Trees where every internal node has exactly t children.
   - `taryTreeCount (t : ℕ) (n : ℕ) : ℕ` — number of t-ary trees with n internal nodes
   - For t=2: should match Catalan numbers
   - For t=3: 1, 1, 3, 12, 55, 273 (Fuss-Catalan)
   - Formula: `taryTreeCount t n = (1/(t*n+1)) * C(t*n+1, n)` but this has division...
   - Use: `(t*n+1) * taryTreeCount t n = Nat.choose (t*n+1) n` as the verifiable form

3. Sanity checks via native_decide:
   - t=2: 1, 1, 2, 5, 14 (Catalan)
   - t=3: 1, 1, 3, 12, 55

4. **Cayley trees (unordered labelled)**: already in LabelledTrees — just add cross-reference theorem `cayley_matches_labelled`.

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.GeneralTrees`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for sanity; avoid division by using multiplied-out form

## Output

Write file, verify build, report.
