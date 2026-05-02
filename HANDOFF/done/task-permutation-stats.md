# Task: Permutation Statistics

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/PermutationStats.lean` formalizing basic permutation statistics.

## What to formalize

From F&S Chapter II: Key statistics on permutations.

### Required:

1. **Number of permutations with exactly k fixed points:**
   ```lean
   def fixedPointCount (n k : ℕ) : ℕ :=
     Nat.choose n k * derangeCount (n - k)
   ```
   where `derangeCount` is from Derangements.lean.
   
   Verify: Σ_{k=0}^{n} fixedPointCount n k = n! for n=0..8.

2. **Signless Stirling numbers of the first kind** (number of permutations of n with exactly k cycles):
   Already defined as `unsignedStirling1` in CycleIndex.lean if it exists.
   If not:
   ```lean
   def stirling1Unsigned : ℕ → ℕ → ℕ
     | 0, 0 => 1
     | 0, _ + 1 => 0
     | _ + 1, 0 => 0
     | n + 1, k + 1 => n * stirling1Unsigned n (k + 1) + stirling1Unsigned n k
   ```
   
   Sanity: stirling1Unsigned 3 1 = 2, stirling1Unsigned 3 2 = 3, stirling1Unsigned 3 3 = 1
   Row sum: Σ_k stirling1Unsigned n k = n! for n=0..6.

3. **Euler numbers (alternating permutations):**
   ```lean
   def eulerianNumber : ℕ → ℕ → ℕ
     | _, 0 => 1
     | 0, _ + 1 => 0
     | n + 1, k + 1 => (k + 2) * eulerianNumber n (k + 1) + (n - k + 1) * eulerianNumber n k
   ```
   Wait, the recursion is A(n,k) = (k+1)*A(n-1,k) + (n-k)*A(n-1,k-1).
   
   Sanity: row sums = n!. First few rows: [1], [1,1], [1,4,1], [1,11,11,1].

4. Verify all row sums equal n! for n=0..6 via native_decide.

## Imports

```lean
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch2.Derangements
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.PermutationStats`
- No sorry, no axiom
- Delete anything that doesn't compile

## Output

Write file, verify build, report.
