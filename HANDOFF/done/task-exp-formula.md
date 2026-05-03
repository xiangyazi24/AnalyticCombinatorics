# Task: Exponential Formula (Ch II)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/ExponentialFormula.lean`.

## What to formalize

From F&S Chapter II: The exponential formula PERM = SET(CYC(Atom)).

At the counting level: n! = Σ over partitions of [n] into cycles.

1. **permCount (n : ℕ) : ℕ := n.factorial**

2. **Exponential formula verification:**
   For n=0..8, verify:
   `n.factorial = ∑ k ∈ Finset.range (n+1), cycleTypeCount n k`
   where `cycleTypeCount` is the unsigned Stirling number from CycleIndex.lean.
   (Row sum = n!)

   This is already in CycleIndex.lean! So instead, verify a different form:

3. **EGF composition verification:**
   The EGF of permutations is `1/(1-z)`. The EGF of SET(CYC(Atom)) = exp(log(1/(1-z))) = 1/(1-z).
   Verify at the coefficient level:
   - Coefficient of z^n/n! in 1/(1-z) is 1 (so EGF coeff = n!/n! = 1... hmm)
   
   Better: **EGF of derangements × EGF of identity = EGF of all permutations**
   - Σ_{k=0}^{n} C(n,k) * derangeCount(n-k) = n!
   - This is already in Derangements.lean! 
   
   So instead focus on:

4. **Connected components formula:**
   - Number of permutations of n with exactly k cycles = unsigned Stirling c(n,k) [in CycleIndex]
   - Bell numbers = Σ Stirling2 = number of set partitions [in BellNumbers]
   - Exponential formula: exp(Σ connected_EGF) = total_EGF
   
   Concrete verification: 
   - Define `connectedPermCount (n : ℕ) := (n - 1).factorial` (cycles = connected permutations)
   - Verify: `∑ k ∈ range (n+1), (1/k!) * (connectedPermCount)^*k [n]` = 1 for n-th coeff
   
   This is complex. Instead:

5. **Simple version:** Verify numerically that for n=1..7:
   `n.factorial = ∑ over all partitions λ of n, ∏ (λ_i - 1)! * multinomial coefficient`
   
   Simplest: just verify `n! = ∑_{k=1}^{n} c(n,k)` which is stirling1 row sum, already done.
   
   **NEW CONTENT:** Verify the EGF identity at coefficient level:
   - [z^n] exp(-log(1-z)) = [z^n] 1/(1-z) = 1
   - Define: `expLogCoeff (n : ℕ) : ℚ := ...` such that Σ expLogCoeff(k) * connectedPerm(n-k)/k! = n!/n!
   
   Honestly, the cleanest new content is:

6. **Final approach — Labelled product verification:**
   For labelled structures, EGF of A * B has coefficient = Σ C(n,k) a_k b_{n-k} / n!.
   Define `labelledProductCoeff` and verify for:
   - PERM * PERM: coefficient should give multinomial
   - SET * CYC: verify for small n

Just pick whatever compiles cleanly.

## Imports

```lean
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch2.CycleIndex
import AnalyticCombinatorics.PartA.Ch2.Derangements
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.ExponentialFormula`
- No sorry, no axiom
- Delete anything that doesn't compile
- Focus on whatever compiles: the key insight is SET(CYC) = PERM at counting level
- If the general framework is too hard, just do numerical verifications for n=0..6

## Output

Write file, verify build, report.
