# Task: Unlabelled Structures (Pólya-style counting)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/UnlabelledStructures.lean` with Burnside/Pólya-style counting for unlabelled structures.

## What to formalize

From F&S Chapter I appendix / Chapter II: Counting under symmetry.

### Required:

1. **Necklace counting:** Number of binary necklaces of length n (cyclic equivalence classes of binary strings):
   ```lean
   def necklaceCount (n : ℕ) : ℕ :=
     if n = 0 then 1
     else (∑ d ∈ Nat.divisors n, Nat.totient d * 2 ^ (n / d)) / n
   ```
   Sequence: 1, 2, 3, 4, 6, 8, 14, 20, 36, ...
   
   Actually for n≥1: necklaceCount n = (1/n) Σ_{d|n} φ(d) * 2^{n/d}

   Since we need ℕ division to be exact, verify via:
   ```lean
   def necklaceCountTimesN (n : ℕ) : ℕ :=
     ∑ d ∈ Nat.divisors n, Nat.totient d * 2 ^ (n / d)
   ```
   and check divisibility + quotient values.

2. Sanity checks: necklaceCount for n=1..8 via native_decide.

3. **Rooted plane tree symmetry (non-isomorphic trees):**
   Actually this is just the Catalan number (plane trees already counted correctly).
   
   Instead: **Non-isomorphic unrooted trees** (simpler version):
   Just define the sequence via OEIS A000055: 1, 1, 1, 1, 2, 3, 6, 11, 23, ...
   and verify a few values.

4. **Multiset coefficient (Euler transform):** Given a sequence a(n), the Euler transform counts multisets. Define:
   ```lean
   def eulerTransform (a : ℕ → ℕ) : ℕ → ℕ
   ```
   This is hard to define cleanly. Skip if it doesn't compile easily.

Focus on necklaces (Burnside's lemma application) as the main content.

## Imports

```lean
import Mathlib.Tactic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Divisors
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.UnlabelledStructures`
- No sorry, no axiom
- Delete anything that doesn't compile
- Focus on necklace counting + sanity checks

## Output

Write file, verify build, report.
