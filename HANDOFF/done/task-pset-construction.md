# Task: PSET (Powerset/Subset) Construction — Part A Ch I

## Goal

Create file `AnalyticCombinatorics/PartA/Ch1/Powerset.lean` formalizing the PSET construction from F&S Proposition I.2.

## What to formalize

Given a combinatorial class `B` with `B.count 0 = 0`, PSET(B) consists of all finite subsets of objects from B (each object used at most once). The OGF satisfies:

```
OGF(PSET(B))(z) = ∏_{n≥1} (1 + z^n)^{b_n}
```

### Required definitions and theorems:

1. **`psetClass`** — the combinatorial class of finite subsets (Finset) over B. Use `Finset B.Obj` with size = sum of sizes. Require `B.count 0 = 0` and `[DecidableEq B.Obj]`.

2. **`psetClass_count_zero`** — `(psetClass B h).count 0 = 1` (empty set)

3. **`psetClass_count_one`** — `(psetClass B h).count 1 = B.count 1`

4. **Relation to MSET:** For `B = Atom`, PSET(Atom) has exactly one subset of each size n ≤ 1, and zero for n ≥ 2 (since Atom has only one object). Verify:
   - `(psetClass Atom _).count 0 = 1`
   - `(psetClass Atom _).count 1 = 1`
   - `(psetClass Atom _).count 2 = 0`

5. **For a richer base:** Define `twoAtoms` (two distinct atoms of size 1) and verify PSET(twoAtoms):
   - count 0 = 1 (empty)
   - count 1 = 2 (either atom alone)
   - count 2 = 1 (both atoms)

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch1.Powerset` must pass
- Follow Mathlib style

## Output

Write the complete file to `AnalyticCombinatorics/PartA/Ch1/Powerset.lean` and report what you proved.
