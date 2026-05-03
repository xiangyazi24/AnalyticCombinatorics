# Task: Multivariate Generating Functions (Ch III/IX)

## Goal

Create `AnalyticCombinatorics/PartA/Ch3/MultivariateGF.lean`.

## What to formalize

From F&S Chapter III/IX: Bivariate GFs encode parameters on combinatorial structures.

1. **Bivariate generating function type:**
   Already have `bgf` in Parameters.lean. Add more worked examples.

2. **Number of descents in permutations (Eulerian numbers):**
   - `eulerianNumber (n k : ℕ) : ℕ` — A(n,k) = number of permutations of [n] with exactly k descents
   - Recursion: A(n,k) = (k+1)*A(n-1,k) + (n-k)*A(n-1,k-1)
   - A(0,0) = 1, A(n,k) = 0 for k ≥ n
   - Row sums: Σ_k A(n,k) = n!
   - Sanity: A(3,0)=1, A(3,1)=4, A(3,2)=1; A(4,0)=1, A(4,1)=11, A(4,2)=11, A(4,3)=1

3. Verify row sums = n! for n=0..7 via native_decide.

4. **Symmetry:** A(n,k) = A(n, n-1-k) verified for n=1..6, all k.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch3.MultivariateGF`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all verifications

## Output

Write file, verify build, report.
