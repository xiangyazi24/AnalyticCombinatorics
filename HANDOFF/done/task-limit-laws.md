# Task: Limit Laws Framework (Ch III / Ch IX)

## Goal

Create `AnalyticCombinatorics/PartA/Ch3/LimitLaws.lean`.

## What to formalize

From F&S Chapter III/IX: Parameters on combinatorial structures converge in distribution.

1. **Gaussian limit law predicate:**
   ```lean
   def IsAsymptoticallyGaussian (meanSeq varSeq : ℕ → ℚ) : Prop :=
     ∀ ε > 0, ∃ N, ∀ n > N, varSeq n > 0
   ```
   (Simplified — just assert variance grows)

2. **Binary search tree depth** — number of comparisons for random input:
   - Mean depth ~ 2 ln n (just define as Prop)
   - Verify: for binary trees of size n, mean path length / n is increasing for n=1..8

3. **Concrete: number of leaves in binary trees**
   - Total leaves across all size-n binary trees:
   - `totalLeaves (n : ℕ) : ℕ := ∑ t ∈ binaryTreeClass.level n, binaryTreeLeaves t`
   - Verify for n=1..5 via native_decide
   - Mean = totalLeaves n / binaryTreeClass.count n (just verify numerator)

4. **Poisson limit for fixed points in permutations:**
   - Fraction of n-permutations with exactly k fixed points → e^{-1}/k!
   - Verify: for n=5..10, number of permutations with 0 fixed points = derangeCount n (cross-reference)

5. Define general `LimitLaw` structure:
   ```lean
   structure LimitLaw where
     meanGrowth : ℕ → ℚ
     varianceGrowth : ℕ → ℚ
     limitType : Type  -- Normal, Poisson, etc.
   ```

## Imports

```lean
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartA.Ch3.Moments
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch3.LimitLaws`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for verifications
- Prop/structure definitions are fine without proofs

## Output

Write file, verify build, report.
