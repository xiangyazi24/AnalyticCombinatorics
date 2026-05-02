# Task: Labelled SET and CYCLE operators — Part A Ch II

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/SetCycleOps.lean` formalizing the SET and CYCLE EGF operators.

## What to formalize

From F&S Chapter II:
- SET(B): EGF = exp(B.egf)
- CYCLE(B): EGF = log(1/(1 - B.egf))

The existing LabelledClass.lean already has `labelSeq` (EGF = 1/(1-B.egf)) and partial `labelSet`/`labelCyc`. This file adds concrete verifications.

### Required:

1. **SET of Atom = all subsets:** Verify that the labelled SET count for Atom gives the right numbers.
   The file already has `labelSetCount_Atom n = 1`. Add:
   - `labelSetCount` for a 2-letter alphabet gives `2^n / n!` coefficients — actually the EGF coefficient of SET(2-Atom) is `e^{2z}` coefficient = `2^n/n!`.

2. **Connected permutations = CYCLE(Atom):** The number of cyclic permutations of n elements is `(n-1)!`. Verify this matches `labelCycCount Atom` from LabelledClass.lean.

3. **Exponential formula: PERM = SET(CYCLE(Atom)):** At the EGF level, `1/(1-z) = exp(log(1/(1-z)))`.
   Verify at the counting level for n=1..5:
   - n! = Σ_{partitions of n} ∏ (k_i - 1)! * multinomial
   
   Or simpler: just verify the coefficient identity for small n via native_decide.

4. **Involutions = SET_2(Atom):** Objects where SET allows only pairs (fixed points + transpositions). Count: `a(n) = a(n-1) + (n-1)*a(n-2)` with a(0)=1, a(1)=1.
   - involutionCount: 1, 1, 2, 4, 10, 26
   - EGF = exp(z + z²/2)

5. Verify EGF coefficient of `exp(z + z²/2)` for n=0..5 matches involution counts.

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.SetCycleOps`
- No sorry, no axiom
- Delete anything that doesn't compile
- Focus on involutions (simplest and most concrete)

## Output

Write file, verify build, report.
