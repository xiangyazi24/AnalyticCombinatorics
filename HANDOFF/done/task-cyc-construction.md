# Task: CYC (Cyclic Sequence) Construction — Part A Ch I

## Goal

Create file `AnalyticCombinatorics/PartA/Ch1/Cycle.lean` formalizing the CYC construction from F&S Proposition I.2.

## What to formalize

CYC(B) consists of cyclic arrangements of objects from B. A cycle of length k over B is an equivalence class of k-tuples under cyclic rotation. If B.count 0 = 0:

```
count(CYC(B), n) = (1/n) * Σ_{d|n} φ(d) * (number of sequences of B-objects of size n using d-fold periodicity)
```

For the simplest case where B = Atom:
- CYC(Atom) counts circular permutations: count(n) = (n-1)! for n ≥ 1, count(0) = 0.

### Required definitions and theorems:

1. **`cycClass`** — Define CYC(B) as equivalence classes of nonempty lists under cyclic rotation. Use a quotient type or a canonical representative (lex-min rotation).

   Simpler approach: define it as `{xs : List B.Obj // xs ≠ [] ∧ isCanonicalRotation xs}` where isCanonicalRotation picks the lexicographically smallest rotation, OR just define via counting formula directly.

   **Recommended approach:** Define the count directly via Burnside/Cauchy (avoid quotient type complexity):

   ```lean
   noncomputable def cycCount (B : CombinatorialClass) (n : ℕ) : ℕ :=
     if n = 0 then 0
     else (seqClass B h).count n / n  -- NOT exact for general B
   ```

   Actually, for B = Atom the exact count is `(n-1)!` for n ≥ 1. For general B, use the Pólya formula. Let's keep it simple:

2. **`cycAtomCount`** — For B = Atom: `cycAtomCount n = if n = 0 then 0 else (n-1)!`

3. **Sanity checks:**
   - cycAtomCount 1 = 1
   - cycAtomCount 2 = 1
   - cycAtomCount 3 = 2
   - cycAtomCount 4 = 6
   - cycAtomCount 5 = 24

4. **OGF relationship:** CYC(Atom) has OGF `- log(1 - z)` (formal power series). Prove:
   ```lean
   theorem cycAtom_ogf_coeff (n : ℕ) (hn : 0 < n) :
       (cycAtomCount n : ℚ) = (n - 1).factorial
   ```

5. **Connect to `labelCycCount` from LabelledClass.lean:** Show the unlabelled cycle count for Atom equals `(n-1)!`, consistent with the labelled version.

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Totient
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch1.Cycle` must pass
- Keep it focused on the Atom case which is cleanly provable. General CYC(B) can use Burnside counting but may be complex — if you can't prove it fully, state the theorem with a direct computation approach.

## Output

Write the file and report what you proved.
