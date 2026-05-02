# Task: Cycle Index and Permutation Types (Ch II)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/CycleIndex.lean`.

## What to formalize

From F&S Chapter II: permutation statistics via cycle structure.

1. `cycleTypeCount (n : ℕ) (k : ℕ) : ℕ` — number of permutations of n elements with exactly k cycles (unsigned Stirling numbers of the first kind).
   - Recursion: `c(n+1, k) = n * c(n, k) + c(n, k-1)` with c(0,0)=1, c(n,0)=0 for n>0

2. Sanity checks (native_decide):
   - c(3,1) = 2, c(3,2) = 3, c(3,3) = 1
   - c(4,1) = 6, c(4,2) = 11, c(4,3) = 6, c(4,4) = 1
   - Row sums: Σ_k c(n,k) = n! for n=1..6

3. `stirling1_row_sum (n : ℕ) : ∑ k ∈ Finset.range (n+1), cycleTypeCount n k = n.factorial`
   Verify for n=0..8 via native_decide.

4. Connection to derangements:
   `derangeCount_eq_fixed_point_zero`: verify for n=0..6 that derangeCount n = number of permutations with 0 fixed points (which is related to cycleTypeCount but needs inclusion-exclusion — just verify numerically).

## Imports

```lean
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch2.Derangements
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.CycleIndex`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all verifications
- Keep the recursion simple, avoid mutual recursion

## Output

Write file, verify build, report.
