# Task: Species Theory Basics (Ch II appendix)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/Species.lean`.

## What to formalize

Species theory provides a clean framework for labelled enumeration.

1. **Species as a structure:**
   ```lean
   structure Species where
     apply : Finset ℕ → Type
     transport : ∀ {S T : Finset ℕ}, S.card = T.card → apply S ≃ apply T
   ```
   Actually this is too abstract. Simpler approach:

2. **Species counting function:**
   ```lean
   def speciesCount (species : ℕ → ℕ) (n : ℕ) : ℕ := species n
   ```
   
   Better: define standard species by their EGF coefficients.

3. **Concrete species examples (just counting):**
   - Atom species: count n = [n = 1]
   - Set species: count n = 1 (one structure for each label set)
   - Cycle species: count n = (n-1)! for n ≥ 1
   - Linear order species: count n = n!
   - Partition species: count n = Bell(n)
   
4. **Species operations:**
   - Sum: (F + G)(n) = F(n) + G(n)
   - Product: (F · G)(n) = Σ_{k=0}^{n} C(n,k) * F(k) * G(n-k)
   - Composition: (F ∘ G)(n) = ... (complex, maybe skip)
   
5. Verify:
   - LinearOrder = SEQ at EGF level: count n = n! (trivial)
   - Cycle product rule: count of PERM as SET(CYC) verified for n=0..6

## Imports

```lean
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch2.CycleIndex
import AnalyticCombinatorics.PartA.Ch2.BellNumbers
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.Species`
- No sorry, no axiom
- Delete anything that doesn't compile
- Focus on counting-level verification, not the full categorical framework

## Output

Write file, verify build, report.
