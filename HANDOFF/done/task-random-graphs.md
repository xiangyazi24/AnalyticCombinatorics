# Task: Random Graphs and Phase Transitions (Ch IX)

## Goal

Create `AnalyticCombinatorics/PartB/Ch9/RandomGraphs.lean`.

## What to formalize

Counting formulas from Chapter IX related to random graphs.

1. **Labelled graphs on n vertices:**
   Total graphs: 2^C(n,2).
   ```lean
   def totalGraphs (n : ℕ) : ℕ := 2 ^ (Nat.choose n 2)
   ```
   Verify: totalGraphs 0 = 1, totalGraphs 1 = 1, totalGraphs 2 = 2,
   totalGraphs 3 = 8, totalGraphs 4 = 64, totalGraphs 5 = 1024

2. **Connected labelled graphs (small values):**
   c(1)=1, c(2)=1, c(3)=4, c(4)=38, c(5)=728
   Define via inclusion-exclusion or table:
   ```lean
   def connectedGraphCount : ℕ → ℕ
     | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 4 | 4 => 38 | 5 => 728 | _ => 0
   ```
   
   Verify: connectedGraphCount 3 + connectedGraphCount-complement = totalGraphs 3.
   Actually just verify the exponential formula relation:
   totalGraphs n = Σ_{k=1}^n C(n-1,k-1) * connectedGraphCount k * totalGraphs (n-k)
   ... this is complex. Just verify the table values.

3. **Labelled trees (Cayley):**
   Already in RandomMappings. Cross-reference:
   Trees on n ≤ number of connected graphs on n.
   ```lean
   def cayleyTreeCount (n : ℕ) : ℕ := if n ≤ 1 then 1 else n ^ (n - 2)
   ```
   Verify: cayleyTreeCount 3 = 3, cayleyTreeCount 4 = 16, cayleyTreeCount 5 = 125

4. **Forest counting:**
   Labelled forests on n vertices with k components:
   ```lean
   def forestCount (n k : ℕ) : ℕ :=
     if k = 0 then (if n = 0 then 1 else 0)
     else Nat.choose n k * k * n ^ (n - k - 1)  -- not quite right for small n
   ```
   Actually use: total forests on n = (n+1)^(n-1). Verify for small n.
   ```lean
   def totalForestCount (n : ℕ) : ℕ := (n + 1) ^ (n - 1)
   -- Hmm this doesn't work for n=0. Use:
   def totalForestCount (n : ℕ) : ℕ := if n = 0 then 1 else (n + 1) ^ (n - 1)
   ```
   Wait, total labelled forests on n vertices = (n+1)^(n-1)? No.
   Total labelled rooted forests = (n+1)^(n-1). Actually that's wrong too.
   
   Simpler: just verify that totalGraphs grows much faster than cayleyTreeCount:
   ```lean
   example : cayleyTreeCount 5 < totalGraphs 5 := by native_decide
   ```

5. **Erdős-Rényi threshold:**
   At p = 1/n, expected number of edges = C(n,2)/n ≈ n/2.
   Expected edges in G(n, 1/n): C(n,2) * 1/n.
   For n=10: C(10,2)/10 = 45/10 = 4.5. Just verify C(10,2) = 45.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch9.RandomGraphs`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace RandomGraphs`** and close with `end RandomGraphs`

## Output

Write file, verify build, report.
