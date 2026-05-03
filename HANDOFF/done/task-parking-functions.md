# Task: Parking Functions and Labeled Trees (Ch II/V application)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/ParkingFunctions.lean`.

## What to formalize

Parking functions are sequences (a_1,...,a_n) with a_i ∈ {1,...,n} such that when cars park greedily, all find spots. Count = (n+1)^{n-1}.

1. **parkingFunctionCount (n : ℕ) : ℕ := (n + 1) ^ (n - 1)**
   (With parkingFunctionCount 0 = 1)

2. **Connection to labelled trees (Cayley's formula):**
   - parkingFunctionCount n = cayleyCount (n + 1) / (n + 1)... 
   - Actually: parkingFunctionCount n = (n+1)^{n-1}
   - cayleyCount n = n^{n-2} (labelled trees on n vertices)
   - Relationship: parkingFunctionCount n = cayleyCount (n+1) if cayleyCount uses n^{n-1} convention
   
   Simpler: just verify both sequences agree for n=1..8.

3. Sanity checks (native_decide):
   - n=1: 1, n=2: 3, n=3: 16, n=4: 125, n=5: 1296
   - These are (n+1)^{n-1}

4. **Abel's generalization:**
   - Σ_{k=0}^{n} C(n,k) * k * (n-k)^{n-k-1} * (k+1)^{k-1} = ... 
   - Skip this if complex. Just do the basic count + sanity.

5. **Ballot problem (related):**
   - ballotCount (n k : ℕ) — number of sequences where candidate A always leads
   - For 2-candidate: ballotCount n k = (n-k)/(n+k) * C(n+k, k) when n > k
   - Verify for small values.

## Imports

```lean
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch2.LabelledTrees
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.ParkingFunctions`
- No sorry, no axiom
- Delete anything that doesn't compile
- Focus on parkingFunctionCount + Cayley connection
- native_decide for all checks

## Output

Write file, verify build, report.
