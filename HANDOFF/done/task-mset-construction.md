# Task: MSET (Multiset) Construction — Part A Ch I

## Goal

Create file `AnalyticCombinatorics/PartA/Ch1/Multiset.lean` formalizing the MSET construction from F&S Proposition I.2.

## What to formalize

Given a combinatorial class `B` with `B.count 0 = 0`, MSET(B) consists of all finite multisets of objects from B. The OGF satisfies the Euler product identity:

```
OGF(MSET(B))(z) = ∏_{n≥1} (1 - z^n)^{-b_n}
```

where `b_n = B.count n`.

### Required definitions and theorems:

1. **`msetClass`** — the combinatorial class of finite multisets over B. Use `Multiset B.Obj` with size = sum of sizes. Require `B.count 0 = 0`.

2. **`msetClass_count_zero`** — `(msetClass B h).count 0 = 1` (empty multiset is the unique size-0 object)

3. **`msetClass_count_one`** — `(msetClass B h).count 1 = B.count 1` (singleton multisets)

4. **Sanity checks using `native_decide`:**
   - If B = Atom, then MSET(Atom) counts integer partitions. Verify:
     - `(msetClass Atom _).count 0 = 1`
     - `(msetClass Atom _).count 1 = 1`
     - `(msetClass Atom _).count 2 = 2`
     - `(msetClass Atom _).count 3 = 3`
     - `(msetClass Atom _).count 4 = 5`
     - `(msetClass Atom _).count 5 = 7`

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Card
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch1.Multiset` must pass
- Follow Mathlib style
- Keep it focused: definitions + count theorems + sanity checks. Skip the Euler product OGF identity if it requires heavy PowerSeries infinite product machinery.

## Output

Write the complete file to `AnalyticCombinatorics/PartA/Ch1/Multiset.lean` and report what you proved.
