# Task: Restricted Permutations (Ch II)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/RestrictedPerms.lean`.

## What to formalize

From F&S Chapter II: Permutations with cycle-length restrictions.

1. **Permutations with all cycles of length ≤ m:**
   Define `boundedCyclePermCount (m n : ℕ) : ℕ` — permutations of [n] where all cycle lengths are ≤ m.
   - m=1: only identity (= 1 for all n)... No, m=1 means only fixed points, so count = 1 if n=0 else 1 (identity).
     Actually for m≥n this is just n!.
   - m=2: involutions (already done, cross-check)
   
   Simpler approach: just verify for small cases.

2. **Permutations with no fixed points and no 2-cycles:**
   `noFixedNo2Count : ℕ → ℕ`
   Recursion from inclusion-exclusion on cycle structure.
   - n=0: 1, n=1: 0, n=2: 0, n=3: 2, n=4: 6, n=5: 24

3. **Alternating permutations (zigzag / tangent/secant numbers):**
   `zigzagCount : ℕ → ℕ` — number of alternating permutations of [n].
   - Recursion: E(n) via tangent/secant decomposition
   - E(0)=1, E(1)=1, E(2)=1, E(3)=2, E(4)=5, E(5)=16, E(6)=61
   - Recurrence: E(n) = (1/2) * Σ_{k=0}^{n-1} C(n-1,k) * E(k) * E(n-1-k)
   - Use multiplied form: 2*E(n) = Σ...

4. Sanity checks via native_decide.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.RestrictedPerms`
- No sorry, no axiom
- Delete anything that doesn't compile
- Focus on zigzag numbers (tangent numbers) — most interesting
- If alternating permutation recursion is hard, just do the Euler zigzag triangle

## Output

Write file, verify build, report.
