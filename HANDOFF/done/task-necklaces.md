# Task: Necklaces and Burnside's Lemma (Ch I)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/Necklaces.lean`.

## What to formalize

Necklaces (equivalence classes of strings under cyclic rotation). Count = (1/n) * Σ_{d|n} φ(d) * k^{n/d} for k-colored necklaces.

1. `necklaceCount (k n : ℕ) : ℕ` — number of necklaces with k colors and n beads.
   - For n=0 return 1 (empty necklace)
   - For n>0: `(∑ d ∈ Nat.divisors n, Nat.totient d * k ^ (n / d)) / n`
   
   Since this involves division, use the multiplied form for verification:
   `n * necklaceCount k n = ∑ d ∈ Nat.divisors n, Nat.totient d * k ^ (n / d)`

2. Sanity checks for binary necklaces (k=2):
   - n=1: 2, n=2: 3, n=3: 4, n=4: 6, n=5: 8, n=6: 14

3. For k=3: n=1: 3, n=2: 6, n=3: 11, n=4: 24

4. `binaryNecklaceCount n := necklaceCount 2 n`

5. Verify the multiplied identity `n * count = Σ divisors` for n=1..8 via native_decide.

## Imports

```lean
import Mathlib.Tactic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Divisors
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.Necklaces`
- No sorry, no axiom
- Delete anything that doesn't compile
- Use Nat division (exact for this formula), verify via native_decide

## Output

Write file, verify build, report.
