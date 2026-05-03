# Task: Random Mappings and Functional Digraphs (Ch II appendix / Ch IX)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/RandomMappings.lean`.

## What to formalize

A mapping f: [n] → [n] can be viewed as a functional digraph. Its connected
components each have exactly one cycle. Key statistics from F&S Ch II/IX.

1. **Number of mappings [n] → [n]:**
   `mappingCount (n : ℕ) : ℕ := n ^ n`
   
   Verify: mappingCount 0 = 1 (convention), 1 = 1, 2 = 4, 3 = 27, 4 = 256

2. **Number of connected functional digraphs on [n]:**
   A connected functional digraph on n vertices = exactly one cycle with
   trees hanging from each cycle node.
   
   `connectedMappingCount : ℕ → ℕ`
   - connectedMappingCount 0 = 0 (or 1 by convention)
   - Formula: connectedMappingCount n = Σ_{k=1}^{n} (n-1)! / (k-1)! * n^{n-k} * k... 
   
   Actually this is complex. Simpler approach:
   
   **Number of mappings with exactly one connected component** = number of connected
   functional digraphs = sequence A001865:
   c(1)=1, c(2)=3, c(3)=15, c(4)=106, c(5)=945, ...
   
   Recursion is complex. Instead, use:
   **Number of idempotent mappings** (f(f(x)) = f(x) for all x):
   `idempotentCount (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), Nat.choose n k * k ^ (n - k)`
   
   This counts mappings where the image is a fixed point set.
   Verify: n=0: 1, n=1: 1, n=2: 3, n=3: 10, n=4: 41, n=5: 196

3. **Labeled rooted forests on [n] with k roots:**
   `rootedForestCount (n k : ℕ) : ℕ := k * n ^ (n - k - 1) * Nat.factorial n / Nat.factorial (n - k)`
   
   Hmm that's not clean. Use the simpler:
   **Labeled rooted forests on [n] (any number of roots):**
   Total = Σ_{k=1}^{n} C(n,k) * k * n^{n-k-1}... also complex.
   
   Simpler: **number of labeled rooted trees on [n]** = n^{n-1} (Cayley's formula).
   `cayleyCount (n : ℕ) : ℕ := if n = 0 then 1 else n ^ (n - 1)`
   
   Verify: n=1: 1, n=2: 2, n=3: 9, n=4: 64, n=5: 625 
   Wait: 5^4 = 625. Let me check: Cayley n=5 should be 5^3 = 125.
   
   cayleyCount: n^{n-2} is labeled UNROOTED trees. n^{n-1} is labeled ROOTED trees.
   Labeled rooted trees on n vertices: n^{n-1}.
   Labeled unrooted trees on n vertices: n^{n-2}.
   
   Use both:
   - `labeledRootedTreeCount (n : ℕ) : ℕ := if n = 0 then 1 else n ^ (n - 1)`
   - `labeledTreeCount (n : ℕ) : ℕ := if n ≤ 1 then 1 else n ^ (n - 2)`

4. **Verify Cayley's formula values:**
   - Labeled trees: n=3: 3, n=4: 16, n=5: 125, n=6: 1296
   - Labeled rooted trees: n=3: 9, n=4: 64, n=5: 625
   - Relationship: labeledRootedTreeCount n = n * labeledTreeCount n (for n ≥ 2)

5. **Idempotent mapping verification:**
   Verify idempotentCount values for n=0..6 via native_decide.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.RandomMappings`
- No sorry, no axiom  
- Delete anything that doesn't compile
- native_decide for all checks
- Focus on clean definitions + numerical verification
- Use `if n = 0 then ... else ...` for Cayley-type formulas to handle edge case

## Output

Write file, verify build, report.
