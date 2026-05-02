# Task: Labelled Trees — Part A Ch II

## Goal

Create file `AnalyticCombinatorics/PartA/Ch2/LabelledTrees.lean` formalizing labelled tree counting from F&S Chapter II.

## What to formalize

Chapter II's showcase: **Cayley's formula** T_n = n^{n-1} (number of labelled trees on n vertices).

The EGF approach: if T(z) is the EGF of labelled rooted trees, then:
- `T(z) = z · exp(T(z))` (a rooted tree = root + SET of subtrees)
- By Lagrange inversion: [z^n] T(z) = n^{n-1} / n!
- So the count of labelled rooted trees on n vertices = n^{n-1}

### Required:

1. **`cayleyCount (n : ℕ) : ℕ`** — number of labelled trees (rooted) on n vertices:
   - cayleyCount 0 = 0 (no tree on 0 vertices)  
   - cayleyCount 1 = 1
   - cayleyCount n = n^(n-1) for n ≥ 1

2. **Sanity checks via native_decide:**
   - cayleyCount 1 = 1
   - cayleyCount 2 = 2
   - cayleyCount 3 = 9
   - cayleyCount 4 = 64
   - cayleyCount 5 = 625

3. **EGF coefficient identity:**
   ```lean
   theorem cayley_egf_coeff (n : ℕ) (hn : 0 < n) :
       (cayleyCount n : ℚ) / n.factorial = (n : ℚ)^(n-1) / n.factorial
   ```

4. **Labelled unrooted trees (Cayley's formula proper):**
   - Number of labelled unrooted trees on n vertices = n^{n-2} for n ≥ 2
   - `cayleyUnrooted n = n^(n-2)` for n ≥ 2
   - Relation: cayleyCount n = n * cayleyUnrooted n (each unrooted tree gives n rooted ones)

5. **Connection to Prüfer sequences** (optional bonus):
   State that the count equals the number of length-(n-2) sequences over {1,...,n}, which is n^{n-2}.

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch2.LabelledTrees` must pass
- Focus on the counting formulas and sanity checks. Skip the actual Lagrange inversion proof (just define the counts directly and verify).
- The EGF functional equation `T = z·exp(T)` can be stated as a theorem about coefficients.

## Output

Write the complete file and report what you proved.
