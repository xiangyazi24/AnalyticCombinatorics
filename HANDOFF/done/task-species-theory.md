# Task: Species Theory Basics

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/Species.lean` with basic species-theoretic constructions.

## What to formalize

A combinatorial species is a functor from finite sets to finite sets. Key operations:
- Species sum: (F+G)[S] = F[S] ⊔ G[S]
- Species product: (F·G)[S] = Σ_{S=S₁⊔S₂} F[S₁] × G[S₂]
- Substitution/composition: (F∘G)[S] = Σ_{π∈Part(S)} F[π] × ∏_{B∈π} G[B]

### Required:

1. Define `Species` as a structure with:
   ```lean
   structure Species where
     apply : ℕ → ℕ  -- number of structures on n labels
   ```

2. Define operations:
   - `Species.sum`, `Species.prod` (Cauchy product of EGF coefficients)
   - Basic species: `Species.empty` (0 everywhere), `Species.one` (1 at 0), `Species.atom` (1 at 1)

3. Verify EGF convolution: for product species, count satisfies binomial convolution:
   `(F·G).apply n = Σ_{k=0}^n C(n,k) * F.apply k * G.apply (n-k)`

4. Sanity checks:
   - `atom.apply 1 = 1`, `atom.apply 0 = 0`, `atom.apply 2 = 0`
   - `(one.sum atom).apply 0 = 1`, `(one.sum atom).apply 1 = 1`
   
5. SET species: `set.apply n = 1` for all n. Verify EGF = e^z numerically.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.Species`
- No sorry, no axiom
- Delete anything that doesn't compile
- Keep definitions simple, verify with native_decide

## Output

Write file, verify build, report.
